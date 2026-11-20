import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescent
import Mathlib
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.baseChange_polynomial_kills_descent` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBaseChangePolynomialAnnihilatesDescent.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.baseChange_polynomial_annihilates_descent : ∀ (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB] [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB), (∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a) →
    ∀ (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X]),
    (∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) →
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  first | exact @GlobalTheory.baseChange_polynomial_kills_descent | exact GlobalTheory.baseChange_polynomial_kills_descent | (intros; apply GlobalTheory.baseChange_polynomial_kills_descent <;> assumption)
