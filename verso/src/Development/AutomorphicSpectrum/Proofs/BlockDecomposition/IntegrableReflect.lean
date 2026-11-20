import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

noncomputable section

open MeasureTheory
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.ConvTest

variable (X : Ctx)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem support_cv_subset (φ ψ : X.G → ℂ) :
    Function.support (cv X.μ φ ψ) ⊆ tsupport φ * tsupport ψ := by
  intro y hy
  by_contra hmem
  apply hy
  have hz : ∀ z : X.G, φ z * ψ (z⁻¹ * y) = 0 := by
    intro z
    by_contra hne
    have h1 : φ z ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ψ (z⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hne
    apply hmem
    refine Set.mem_mul.2 ⟨z, subset_tsupport _ h1, z⁻¹ * y, subset_tsupport _ h2, ?_⟩
    group
  simp [cv, hz]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem continuous_cv {φ ψ : X.G → ℂ} (hφ : Tst φ) (hψ : Tst ψ) : Continuous (cv X.μ φ ψ) := by
  have hK : IsCompact (tsupport φ) := hφ.2
  have hEq : cv X.μ φ ψ = fun y => ∫ z in tsupport φ, φ z * ψ (z⁻¹ * y) ∂X.μ := by
    funext y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hEq]
  refine continuous_parametric_integral_of_continuous
    (f := fun (y z : X.G) => φ z * ψ (z⁻¹ * y)) ?_ hK
  have h1 : Continuous fun p : X.G × X.G => φ p.2 := hφ.1.comp continuous_snd
  have h2 : Continuous fun p : X.G × X.G => ψ (p.2⁻¹ * p.1) :=
    hψ.1.comp (continuous_snd.inv.mul continuous_fst)
  exact h1.mul h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem integrable_reflect {ψ : X.G → ℂ} (hψ : Tst ψ) (y : X.G) :
    Integrable (fun z => ‖ψ (z⁻¹ * y)‖) X.μ := by
  have hc : Continuous fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.1.comp (continuous_inv.mul continuous_const)
  have hs : HasCompactSupport fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.2.comp_homeomorph ((Homeomorph.inv X.G).trans (Homeomorph.mulRight y))
  exact (hc.integrable_of_hasCompactSupport hs).norm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_cv_le {φ ψ : X.G → ℂ} (hψ : Tst ψ) (B : ℝ) (hB : ∀ z, ‖φ z‖ ≤ B) (y : X.G) :
    ‖cv X.μ φ ψ y‖ ≤ B * ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hshift : ∫ z, ‖ψ (z⁻¹ * y)‖ ∂X.μ = ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
    have h := integral_mul_left_eq_self (μ := X.μ) (fun z => ‖ψ z⁻¹‖) y⁻¹
    simpa [mul_inv_rev] using h
  have hle : ‖cv X.μ φ ψ y‖ ≤ ∫ z, B * ‖ψ (z⁻¹ * y)‖ ∂X.μ := by
    refine norm_integral_le_of_norm_le ((integrable_reflect X hψ y).const_mul B) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
  rw [integral_const_mul, hshift] at hle
  exact hle

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem cvTest : CvTest := by
  intro X φ ψ hφ hψ
  have hsupp := support_cv_subset X φ ψ
  refine ⟨⟨continuous_cv X hφ hψ, ?_⟩, hsupp, fun B hB y => norm_cv_le X hψ B hB y⟩
  have hK : IsCompact (tsupport φ * tsupport ψ) := IsCompact.mul hφ.2 hψ.2
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  exact hy (hsupp hne)

end GlobalTheory.CompanionTheory.ConvTest

end
