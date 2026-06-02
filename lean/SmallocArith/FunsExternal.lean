-- External function models for [smalloc_arith].
-- Hand-written companion to the Aeneas-generated `FunsExternal_Template.lean`.
--
-- Aeneas could not translate `usize::ilog2` (a std intrinsic), so it emitted an
-- opaque `axiom` in the template. An opaque axiom is unusable for proofs (it
-- could return anything) and counts as an unproved axiom, so here we replace it
-- with a *computable model*: `ilog2 x = floor(log2 x)`, expressed via `Nat.log 2`.
-- Rust's `ilog2` panics on `x = 0`; `Nat.log 2 0 = 0`, which is harmless because
-- every caller in this crate passes `x ≥ 1`.
import Aeneas
import SmallocArith.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open smalloc_arith

/-- [core::num::{usize}::ilog2]: model as floor(log2).
    Name pattern: [core::num::{usize}::ilog2] -/
@[rust_fun "core::num::{usize}::ilog2"]
def core.num.Usize.ilog2 (x : Std.Usize) : Result Std.U32 :=
  ok ⟨BitVec.ofNat _ (Nat.log 2 x.val)⟩

/-- **Spec theorem for `core::num::{usize}::ilog2`**
    The result equals `Nat.log 2 x.val` (floor of the base-2 logarithm).
    Always succeeds and never truncates: for any `usize`, `log2 x < 64 ≤ 2^32`. -/
@[step]
theorem core.num.Usize.ilog2_spec (x : Std.Usize) :
    core.num.Usize.ilog2 x ⦃ (r : Std.U32) => r.val = Nat.log 2 x.val ⦄ := by
  unfold core.num.Usize.ilog2
  rw [WP.spec_ok]
  show (BitVec.ofNat 32 (Nat.log 2 x.val)).toNat = Nat.log 2 x.val
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : x.val < 2 ^ Std.Usize.numBits := by scalar_tac
  have hnb : Std.Usize.numBits ≤ 64 := by
    rw [Std.Usize.numBits]
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have h64 : x.val < 2 ^ 64 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hnb)
  have hlog : Nat.log 2 x.val < 64 := Nat.log_lt_of_lt_pow' (by norm_num) h64
  exact lt_of_lt_of_le hlog (by norm_num)
