import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd

noncomputable section

namespace Formalism.ExponentWindows

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_apply_sub_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (n : ℕ) : (γ ^ n) w - w ∈ U := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hU _ ih
    have e0 : (γ ^ (n + 1)) w = γ ((γ ^ n) w) := by rw [pow_succ']; rfl
    have e : (γ ^ (n + 1)) w - w = γ ((γ ^ n) w - w) + (γ w - w) := by
      rw [e0, map_sub]; abel
    rw [e]
    exact U.add_mem h1 hw

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aeval_apply_sub_eval_one_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (P : Polynomial R) :
    Polynomial.aeval γ P w - P.eval 1 • w ∈ U := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval γ (p + q) w - (p + q).eval 1 • w =
        (Polynomial.aeval γ p w - p.eval 1 • w) + (Polynomial.aeval γ q w - q.eval 1 • w) := by
      rw [map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]; abel
    rw [e]
    exact U.add_mem hp hq
  | monomial n a =>
    have e : Polynomial.aeval γ (Polynomial.monomial n a) w - (Polynomial.monomial n a).eval 1 • w =
        a • ((γ ^ n) w - w) := by
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one, smul_sub]
      congr 1
      all_goals first
        | rfl
        | simp [Module.algebraMap_end_apply]
    rw [e]
    exact U.smul_mem a (pow_apply_sub_mem γ U hU w hw n)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem aeval_sub_eval_one_smul_mem : KillerShift := by
  intro R M _ _ _ γ U hU P w hw
  exact aeval_apply_sub_eval_one_mem γ U hU w hw P

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro k V _ _ _ γ U hU Q₀ hQ hkill w hw
  have hm := aeval_apply_sub_eval_one_mem γ U hU w hw Q₀
  set c := Q₀.eval 1 with hc
  set x := Polynomial.aeval γ Q₀ w with hx
  refine ⟨c⁻¹ • x, w - c⁻¹ • x, ?_, ?_, by abel⟩
  · have h := hkill w
    rw [map_mul, map_sub, Polynomial.aeval_X, map_one] at h
    change (γ - 1) x = 0 at h
    rw [LinearMap.sub_apply] at h
    change γ x - x = 0 at h
    rw [map_smul, sub_eq_zero.mp h]
  · have e : w - c⁻¹ • x = (-c⁻¹) • (x - c • w) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hQ, neg_smul, neg_smul, one_smul]; abel
    rw [e]
    exact U.smul_mem _ hm

end Formalism.ExponentWindows
