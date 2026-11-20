import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

section
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem prodN_mul_apply {p : ℕ} {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} {g : GL (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (hg : InN p g) (r s : n ⊕ Fin c) (hrs : lev p s ≤ lev p r) :
    (h * g.val) r s = h r s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [hg s s le_rfl, Matrix.one_apply_eq, mul_one]
  · intro t _ hts
    by_cases hlt : lev p t < lev p r
    · rw [hh hlt, zero_mul]
    · rw [hg t s (hrs.trans (not_lt.mp hlt)), Matrix.one_apply_ne hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem prodN_blockTriangular {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) :
    g.val.BlockTriangular (lev p) := by
  intro i j hij
  rw [hg i j hij.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem prodN_inN_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : InN p g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro r s _; simp
  | mul x y _ _ hx hy =>
    intro r s hrs
    rw [Units.val_mul, prodN_mul_apply (prodN_blockTriangular hx) hy r s hrs]
    exact hx r s hrs
  | inv x _ hx =>
    intro r s hrs
    have : Invertible x.val := ⟨x.inv, x.inv_val, x.val_inv⟩
    have hb : (x⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (prodN_blockTriangular hx)
    have key := prodN_mul_apply hb hx r s hrs
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, eq_comm] at key

end

end GlobalTheory.RootEx
