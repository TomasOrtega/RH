import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy`. Establish `hcl` using `GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1`. Establish `hSG : Sset k r z ⊆ GG k r` using `hcl.2.2.2.1.1`. Establish `hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w` using `(GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1`. Establish `hu₂ : σ (Matrix.of y) u₁ ∈ DD σ w` using `hstab _ hy u₁ hu₁`.

Establish `hint` using `(GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab hStd.2.2.2.2.2.2.2.1 _ hu₂ v hv).1`. Establish `hint2` using `hint.apply_continuousLinearMap ξ`. Establish `hA : Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y) = ∫ s, (coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ ∂μS`. Unfold `Afun be`. Conclude with `ContinuousLinearMap.integral_apply hint ξ`.

Establish `hinner : ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ s, ⟪(coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ, ξ⟫_ℂ ∂μS`. Rewrite using `[hA, ← inner_conj_symm, ← integral_inner hint2, ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[inner_conj_symm]`.

Rewrite using `[hinner, ← integral_const_mul]`. Establish `hS0 : μS {x | Matrix.of x ∉ Sset k r z} = 0` using `hSide.2.2.2.1.2.2.1`. Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z`. Rewrite using `[ae_iff]`.

Simplify using `using hS0`. Use `filter_upwards [hae] with s hs`. Establish `hmul : σ (Matrix.of s * Matrix.of y) = (σ (Matrix.of s)).comp (σ (Matrix.of y))` using `hStd.2.1.1.2 _ (hSG hs) _ hy`. Simplify using `only [ContinuousLinearMap.smul_apply, inner_smul_left]`. Establish `hc : coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) = coef σ u₁ v (Matrix.of s * Matrix.of y)`.

Simplify using `only [coef, hmul, ContinuousLinearMap.comp_apply]`. Rewrite using `[hc, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem coef_mul_inner_Afun_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have hu₂ : σ (Matrix.of y) u₁ ∈ DD σ w := hstab _ hy u₁ hu₁
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab
    hStd.2.2.2.2.2.2.2.1 _ hu₂ v hv).1
  have hint2 := hint.apply_continuousLinearMap ξ
  have hA : Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y) =
      ∫ s, (coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ ∂μS := by
    unfold Afun be
    exact ContinuousLinearMap.integral_apply hint ξ
  have hinner : ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ s, ⟪(coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ, ξ⟫_ℂ ∂μS := by
    rw [hA, ← inner_conj_symm, ← integral_inner hint2, ← integral_conj]
    congr 1; funext s; rw [inner_conj_symm]
  rw [hinner, ← integral_const_mul]
  have hS0 : μS {x | Matrix.of x ∉ Sset k r z} = 0 := hSide.2.2.2.1.2.2.1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS0
  filter_upwards [hae] with s hs
  have hmul : σ (Matrix.of s * Matrix.of y) = (σ (Matrix.of s)).comp (σ (Matrix.of y)) :=
    hStd.2.1.1.2 _ (hSG hs) _ hy
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
  have hc : coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) = coef σ u₁ v (Matrix.of s * Matrix.of y) := by
    simp only [coef, hmul, ContinuousLinearMap.comp_apply]
  rw [hc, mul_assoc]
  rfl

end GlobalTheory.SgInf
