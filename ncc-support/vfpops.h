//vfpops.h


#define VFP_CPNUM       0xA // VFP coprocessor number
#define VFP_DT_BASE     (0x0C000000u | (VFP_CPNUM << 8)) // Data transfer

#define VFP_Rn(v)       F_RN(v)
#define VFP_Rt(v)       F_RD(v)
#define VFP_Rt2(v)      F_RN(v)
#define VFP_Rd(v)       F_RD(v)

// For register encoding
#define VFP_BIT_D       (1u<<22)
#define VFP_BIT_N       (1u<< 7)
#define VFP_BIT_M       (1u<< 5)

#define VFP_D(v)  (((v) & 0x1) << 22)
#define VFP_N(v)  (((v) & 0x1) <<  7)
#define VFP_M(v)  (((v) & 0x1) <<  5)

#define VFP_Vd(v) (((v) & 0xf) << 12)
#define VFP_Vn(v) (((v) & 0xf) << 16)
#define VFP_Vm(v) (((v) & 0xf) <<  0)

// [Page 257 of ARMv7-A and ARMv7-R architecture reference manual)
// Single precision encodes registers:   (0x1e = bits [4:1] of reg number)
//   Destination:  Vd, D (bits[15:12, 22])
//   First param:  Vn, N (bits[19:16, 7])
//   Second param: Vm, M (bits[3:0, 5])
#define VFP_Sd(r) ( VFP_Vd((r) >> 1) | VFP_D((r) & 1) )
#define VFP_Sn(r) ( VFP_Vn((r) >> 1) | VFP_N((r) & 1) )
#define VFP_Sm(r) ( VFP_Vm((r) >> 1) | VFP_M((r) & 1) )

// Double precision encodes registers:
//   Destination:  D, Vd (bits[22, 15:12])
//   First param:  N, Vn (bits[7, 19:16])
//   Second param: M, Vm (bits[5, 3:0])
#define VFP_Dd(r) ( VFP_D((r) >> 4) | VFP_Vd(r) )
#define VFP_Dn(r) ( VFP_N((r) >> 4) | VFP_Vn(r) )
#define VFP_Dm(r) ( VFP_M((r) >> 4) | VFP_Vm(r) )

#define VFP_VADD_S          0x0E300A00u // Sd <- Sn + Sm         p831
#define VFP_VADD_D          0x0E300B00u // Dd <- Dn + Dm         p831

#define VFP_VSUB_S          0x0E300A40u // Sd <= Sn - Sm
#define VFP_VSUB_D          0x0E300B40u // Dd <= Dn - Dm

#define VFP_VMUL_S          0x0E200A00u // Sd <= Sn * Sm
#define VFP_VMUL_D          0x0E200B00u // Dd <= Dn * Dm

#define VFP_VDIV_S          0x0E800A00u // Sd <= Sn / Sm
#define VFP_VDIV_D          0x0E800B00u // Dd <= Dn / Dm

#define VFP_VEOR_D          0xF3000110u // Dd <= Dn ^ Dm Cond=ALWAYS p889

#define VFP_VCVT_F32_F64    0x0EB70BC0u
#define VFP_VCVT_F64_F32    0x0EB70AC0u

// Integer (S32) <-> FP (F32 or F64) conversions
#define VFP_VCVT_Round_FPSCR (1u<<7)

#define VFP_VCVT_S32_F32    0x0EBD0AC0u // Sd <- Sm round towards zero
#define VFP_VCVT_S32_F64    0x0EBD0BC0u // Sd <- Dm round towards zero
#define VFP_VCVT_F32_S32    0x0eb80ac0u // round to FPSCR (regardless of flag)
#define VFP_VCVT_F64_S32    0x0EB80Bc0u // round to FPSCR (regardless of flag)

#define VFP_VCVT_S32_F32_FLOOR 0x0EEB0AEFu  // Sd <- Sm (imm 1 = floor)
#define VFP_VCVT_S32_F64_FLOOR 0x0EEB0AEFu  // Sd <- Dm (imm 1 = floor)

#define VFP_UP              (1u<<23)

// Load/store one register (single or double precision).
// Can combine with VFP_UP/VFP_DOWN, but not writeback
#define VFP_VLDR_S_IMM      0x0D100A00u // Sd <- [Rn, #imm]     p925
#define VFP_VLDR_D_IMM      0x0D100B00u
#define VFP_VSTR_S_IMM      0x0D000A00u // Sd <- [Rn, #imm]     p1083
#define VFP_VSTR_D_IMM      0x0D000B00u // Sd <- [Rn, #imm]     p1083

#define VFP_IMM8(off)    ( ((unsigned)((off) >> 2)) & 0xFFu )

#define VFP_VLDR_S(rn, sreg, off_bytes) ( VFP_VLDR_S_IMM | VFP_Rn(rn) | VFP_Sd(sreg) | VFP_IMM8(off_bytes) )
#define VFP_VSTR_S(rn, sreg, off_bytes) ( VFP_VSTR_S_IMM | VFP_Rn(rn) | VFP_Sd(sreg) | VFP_IMM8(off_bytes) )
#define VFP_VLDR_D(rn, dreg, off_bytes) ( VFP_VLDR_D_IMM | VFP_Rn(rn) | VFP_Dd(dreg) | VFP_IMM8(off_bytes) )
#define VFP_VSTR_D(rn, dreg, off_bytes) ( VFP_VSTR_D_IMM | VFP_Rn(rn) | VFP_Dd(dreg) | VFP_IMM8(off_bytes) )

// Common field builders for VPUSH/VPOP/VLDM/VSTM, NOT VLDR.
#define VFP_PRE             (1u<<24)
#define VFP_WRITEBACK       (1u<<21)

// Load/store multiple. VLDM/VPOP/VSTM/VPUSH
// VPUSH === VSTMFD sp!, <list> ie. Rd=sp, VFP_PRE,  VFP_DOWN, VFP_WRITEBACK
// VPOP  === VLDMFD sp!, <list> ie. Rd=sp, VFP_POST, VFP_UP,   VFP_WRITEBACK
#define VFP_VPUSH_S         0x0D2D0A00u // [sp] <- Sd + <list>  p993
#define VFP_VPUSH_D         0x0D2D0B00u // [sp] <- Dd + <list>  p993
#define VFP_VPOP_S          0x0CBD0A00u // Sd + <list> <- [sp]  p991
#define VFP_VPOP_D          0x0CBD0B00u // Dd + <list> <- [sp]  p991

// Can combine with VFP_UP/VFP_DOWN, VFP_PRE/VFP_POST, VFP_WRITEBACK
#define VFP_VSTM_S          0x0C000A00u // [Rn] <- Sd + <list>  p1081
#define VFP_VSTM_D          0x0C000B00u // [Rn] <- Dd + <list>  p1081
#define VFP_VLDM_S          0x0C100A00u // Sd + <list> <- [Rn]  p923
#define VFP_VLDM_D          0x0C100B00u // Dd + <list> <- [Rn]  p923

#define VFP_VLDMFD_D        (VFP_VLDM_D | VFP_UP /*| VFP_VFP_POST*/)

// I went with quiet-NaN, not signalling-NaN.
#define VFP_VCMP_S          0x0EB40A40u // Sd, Sm               p865
#define VFP_VCMP_D          0x0EB40B40u // Dd, Dm               p865
#define VFP_VCMPZ_S         0x0EB50A40u // Sd, Sm               p865
#define VFP_VCMPZ_D         0x0EB50B40u // Dd, Dm               p865
#define VFP_VMRS_APSR       0x0EF1FA10u // APSR <- flags        p955

#define VFP_VABS_S          0x0EB00AC0u // Sd <- Sm   p825
#define VFP_VABS_D          0x0EB00BC0u // Dd <- Dm   p825
#define VFP_VNEG_S          0x0EB10A40u
#define VFP_VNEG_D          0x0EB10B40u

#define VFP_VMOV_S_S        0x0EB00A40u // Sd <- Sm
#define VFP_VMOV_D_D        0x0EB00B40u // Dd <- Dm

#define VFP_VMOV_S_IMM      0x0EB00A00u // Sd <- #imm           p937
#define VFP_VMOV_D_IMM      0x0EB00B00u // Sd <- #imm           p937

// VMOV to core registers transfer the bit pattern.
// Use VCVT with S-type for converting int to float/double.
// (Sreg for signed, Ureg for unsigned).
#define VFP_VMOV_S_R        0x0E000A10u // Sn <- Rt             p945
#define VFP_VMOV_R_S        0x0E100A10u // Rt <- Sn             p945
#define VFP_VMOV_D_R_R      0x0C400B10u // Dm <- Rt, Rt2        p949
#define VFP_VMOV_R_R_D      0x0C500B10u // Rt, Rt2 <- Dm        p949

// Two registers to/from two core registers. Not sure it's useful with current
// JOPS. Essentially just an extra flag on VFP_VMOV_D_R_R/VFP_VMOV_R_R_D.
#define VFP_VMOV_S_S_R_R    0x0C400A10u // Sm, Sm1 <- Rt, Rt2 p947 (unused)
#define VFP_VMOV_R_R_S_S    0x0C500A10u // Rt, Rt2 <- Dn

// Use the top-most regs as scratch registers.
#define VFP_SCR_S   30  // S31
#define VFP_SCR_D   15  // D15

// For down-casting register numbers from RealRegister/IPtr/UPtr.
#define R_(X) (uint32_t)(X)

struct FP_Gen;
extern struct FP_Gen const vfp_gen;
