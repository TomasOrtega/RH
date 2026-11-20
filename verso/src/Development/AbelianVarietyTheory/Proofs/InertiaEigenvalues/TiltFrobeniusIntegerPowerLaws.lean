import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.PwLaws
variable {l : ℕ} [Fact l.Prime]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pw_apply_eq (k : ℤ) (x : Fl l) :
    pw k x = ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x := rfl
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem pw_zadd (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  simp only [pw_apply_eq, zpow_add, RingAut.mul_apply]
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pw_one (x : Fl l) : pw 1 x = x ^ l := by
  rw [pw_apply_eq, zpow_one]
  show frobeniusEquiv (Fl l) l x = _
  rw [frobeniusEquiv_apply, frobenius_def]
/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_apply_eq]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    rw [h, pw_zadd, ih, pw_one, ← pow_mul, pow_succ]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem pw_zero_int (x : Fl l) : pw 0 x = x := by
  simp [pw_apply_eq]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sh_pow' (x : Fl l) (m : ℕ) : sh (x ^ m) = sh x ^ m := by
  simp only [sh, map_pow, SubmonoidClass.coe_pow]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem norm_sh_pw_nat (n : ℕ) (x : Fl l) : ‖sh (pw (n : ℤ) x)‖ = ‖sh x‖ ^ (l ^ n) := by
  rw [pw_nat, sh_pow', norm_pow]
/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [norm_sh_pw_nat, zpow_natCast, ← Real.rpow_natCast]
    push_cast
    rfl
  · set y := pw (-(n : ℤ)) x with hy
    have hx : x = pw (n : ℤ) y := by
      rw [hy, ← pw_zadd, add_neg_cancel, pw_zero_int]
    have hne : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have e : ((l : ℝ) ^ (-(n : ℤ))) = (((l ^ n : ℕ) : ℝ))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      push_cast
      rfl
    conv_rhs => rw [hx, norm_sh_pw_nat, e]
    exact (Real.pow_rpow_inv_natCast (norm_nonneg _) hne).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem pw_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  intro l _
  refine ⟨fun k x y => ?_, fun k x y => ?_, fun k => ?_, pw_zadd, pw_nat, fun k n x => ?_, norm_sh_pw⟩
  · simp only [pw_apply_eq, map_add]
  · simp only [pw_apply_eq, map_mul]
  · simp only [pw_apply_eq, map_zero]
  · simp only [pw_apply_eq, map_pow]

end GlobalTheory.PSer.PwLaws
