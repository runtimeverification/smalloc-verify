-- Correctness proofs for smalloc's `reqali_to_sc`.
--
-- Source of the Rust function:
--   https://github.com/zooko/smalloc/blob/main/smalloc/src/lib.rs
--
-- The Aeneas-extracted version lives in `SmallocArith/Funs.lean`; the model of
-- the external `usize::ilog2` intrinsic lives in `SmallocArith/FunsExternal.lean`.

import Aeneas
import SmallocArith
import Mathlib.Data.Nat.Log

open Aeneas Aeneas.Std Result

namespace SmallocArithVerif.BasicProofs

set_option maxHeartbeats 1000000

/-! ## Pure Nat specification

The mathematical specification of `reqali_to_sc` as a Nat computation,
mirroring the Rust implementation step-by-step. `Nat.log 2` is floor-log2. -/

def reqali_to_sc_spec (siz ali : Nat) : Nat :=
  Nat.log 2 ((siz - 1) ||| (ali - 1) ||| 3) + 1

/-! ## Safety preconditions

The Rust function panics on `siz = 0` or `ali = 0` (because of the
checked subtractions `siz - 1` and `ali - 1`). Aeneas-extracted code
exposes these panics as `Result.fail`, so we bundle the preconditions
into a structure. -/

structure SafeParams (siz ali : Usize) : Prop where
  hsiz : siz.val ≥ 1
  hali : ali.val ≥ 1
  hali_pow2 : ∃ k : Nat, ali.val = 2 ^ k
  hali_bound : ali.val < 2 ^ 32

/-! ## Platform-width helpers

`usize` is 32 or 64 bits wide (`System.Platform.numBits`); these bound small
constants against it. -/

private theorem numBits_ge (n : Nat) (h : n ≤ 32) : n ≤ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with hp | hp <;> omega

private theorem numBits_gt (n : Nat) (h : n ≤ 31) : n < System.Platform.numBits := by
  rcases System.Platform.numBits_eq with hp | hp <;> omega

/-- For any `usize`, `floor(log2 x) < 64`: it fits in a `u32` and a `u8` without
    truncation, since `usize` is at most 64 bits. -/
private theorem log2_usize_lt (x : Std.Usize) : Nat.log 2 x.val < 64 := by
  have hb : x.val < 2 ^ Std.Usize.numBits := by scalar_tac
  have hnb : Std.Usize.numBits ≤ 64 := by
    rw [Std.Usize.numBits]; rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have h64 : x.val < 2 ^ 64 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hnb)
  exact Nat.log_lt_of_lt_pow' (by norm_num) h64

/-- The constant `SMALLEST_SLOT_SIZE_BITS_MASK = (1 << 2) - 1 = 3`. -/
@[local step]
private theorem mask_spec :
    smalloc_arith.SMALLEST_SLOT_SIZE_BITS_MASK ⦃ (r : Std.Usize) => r.val = 3 ⦄ := by
  unfold smalloc_arith.SMALLEST_SLOT_SIZE_BITS_MASK smalloc_arith.SMALLEST_SLOT_SIZE_BITS
  step
  case hy => simp; exact numBits_gt 2 (by norm_num)
  have hsize : (4 : Nat) < Std.Usize.size := by
    rw [Std.Usize.size, Std.Usize.numBits]
    calc (4 : Nat) < 2 ^ 32 := by norm_num
      _ ≤ 2 ^ System.Platform.numBits :=
        Nat.pow_le_pow_right (by norm_num) (numBits_ge 32 (by norm_num))
  have hi : ∀ i : Std.Usize, i.val = 1 <<< 2 % Std.Usize.size → i.val = 4 := by
    intro i hii; rw [hii]; exact Nat.mod_eq_of_lt hsize
  step
  rw [r_post1, hi i i_post1]

/-! ## Functional spec of the extracted function

Stepping through the Aeneas-extracted monadic code: under the preconditions the
function succeeds and returns exactly `floor(log2 m) + 1`, where
`m = (siz-1) ||| (ali-1) ||| 3`. No subtraction underflows, the `u32` add does
not overflow, and the final `u8` cast does not truncate. -/

private theorem reqali_spec (siz ali : Std.Usize) (hsiz : 1 ≤ siz.val) (hali : 1 ≤ ali.val) :
    smalloc_arith.reqali_to_sc siz ali ⦃ (r : Std.U8) =>
      r.val = Nat.log 2 ((siz.val - 1) ||| (ali.val - 1) ||| 3) + 1 ⦄ := by
  unfold smalloc_arith.reqali_to_sc
  step*
  · -- `i5 + 1#u32` does not overflow `u32`
    have hlt := log2_usize_lt i4
    rw [i5_post]; scalar_tac
  · -- the final `u8` cast does not truncate
    have hi4 : (↑i4 : Nat) = (↑siz - 1 ||| ↑ali - 1 ||| 3) := by
      rw [i4_post1, UScalar.val_or, i3_post, i2_post1, UScalar.val_or, i_post1, i1_post1]
    have hlt : Nat.log 2 (↑siz - 1 ||| ↑ali - 1 ||| 3) < 64 := by
      rw [← hi4]; exact log2_usize_lt i4
    rw [UScalar.cast_val_eq, i6_post, i5_post, hi4]
    simp only [UScalarTy.U8_numBits_eq]
    apply Nat.mod_eq_of_lt
    omega

/-! ## Theorem T1: slot size fits

Under SafeParams, the slot size `2 ^ reqali_to_sc(siz, ali)` is at least
`max(siz, ali, SMALLEST_SLOT_SIZE) = max(siz, ali, 4)`.

This is the core correctness property: an allocation request of `siz`
bytes with alignment `ali` is satisfied by a slot of size at least `siz`
and aligned to at least `ali`. -/

theorem reqali_to_sc_size_fits
    (siz ali : Usize) (safe : SafeParams siz ali) :
    ∃ result : Std.U8,
      smalloc_arith.reqali_to_sc siz ali = ok result ∧
      2 ^ result.val ≥ siz.val ∧
      2 ^ result.val ≥ ali.val ∧
      2 ^ result.val ≥ 4 := by
  obtain ⟨result, hok, hval⟩ := WP.spec_imp_exists (reqali_spec siz ali safe.hsiz safe.hali)
  -- `m < 2 ^ (log2 m + 1) = 2 ^ result`, and `m` dominates each of `siz-1`, `ali-1`, `3`.
  have hlt : ((siz.val - 1) ||| (ali.val - 1) ||| 3) < 2 ^ result.val := by
    rw [hval]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hsiz1 : siz.val - 1 ≤ (siz.val - 1) ||| (ali.val - 1) ||| 3 :=
    le_trans Nat.left_le_or Nat.left_le_or
  have hali1 : ali.val - 1 ≤ (siz.val - 1) ||| (ali.val - 1) ||| 3 :=
    le_trans Nat.right_le_or Nat.left_le_or
  have h3 : 3 ≤ (siz.val - 1) ||| (ali.val - 1) ||| 3 := Nat.right_le_or
  have := safe.hsiz; have := safe.hali
  exact ⟨result, hok, by omega, by omega, by omega⟩

/-! ## Theorem T2: alignment fits

Under SafeParams, the slot returned by `reqali_to_sc(siz, ali)` has
size that is a multiple of `ali` (i.e. its alignment is at least `ali`).
This follows from T1 plus the fact that both `2 ^ result` and `ali` are
powers of two with `2 ^ result ≥ ali`. -/

theorem reqali_to_sc_alignment_fits
    (siz ali : Usize) (safe : SafeParams siz ali) :
    ∃ result : Std.U8,
      smalloc_arith.reqali_to_sc siz ali = ok result ∧
      ali.val ∣ 2 ^ result.val := by
  obtain ⟨result, hok, hval⟩ := WP.spec_imp_exists (reqali_spec siz ali safe.hsiz safe.hali)
  obtain ⟨k, hk⟩ := safe.hali_pow2
  refine ⟨result, hok, ?_⟩
  -- `2 ^ result ≥ ali = 2 ^ k`, so `k ≤ result` and `2 ^ k ∣ 2 ^ result`.
  have hlt : ((siz.val - 1) ||| (ali.val - 1) ||| 3) < 2 ^ result.val := by
    rw [hval]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hali1 : ali.val - 1 ≤ (siz.val - 1) ||| (ali.val - 1) ||| 3 :=
    le_trans Nat.right_le_or Nat.left_le_or
  have hh := safe.hali
  have hav : ali.val ≤ 2 ^ result.val := by omega
  rw [hk] at hav
  have hkr : k ≤ result.val := (Nat.pow_le_pow_iff_right (by norm_num)).mp hav
  rw [hk]; exact Nat.pow_dvd_pow 2 hkr

end SmallocArithVerif.BasicProofs
