import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConePolar
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeChartGram
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearNoetherNormalization
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem anForm_maDens_eq_geo_maDensity {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.ChartRestriction.G.Geo.maDensity φ z :=
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem maDens_log_dualNorm_sheet {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin e) (Fin n) ℂ) (y : Fin e → ℂ) (x : Fin n → ℂ)
    (s : (Fin e → ℂ) → Fin n → ℂ) (hx : x ∈ fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y)
    (hs : IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s) :
    ReciprocityTheory.AnForm.maDens (fun k => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) y =
      (e.factorial : ℝ) / Real.pi ^ e * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y /
        h.dualNorm x ^ (2 * (e + 1)) := by
  obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := hs
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : eval (0 : Fin n → ℂ) (linForm ℓ - 1) = 0 :=
      hxZ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    rw [map_sub, map_one, linForm, map_sum] at h1
    simp at h1
  have hdual : ∀ z, h.dualNorm z = ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ z)‖ := fun z => by
    simp [HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hv : ∀ᶠ y' in 𝓝 (A *ᵥ x), DifferentiableAt ℂ (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y' := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have hs' := (hdiff y' hy').differentiableAt (hU.mem_nhds hy')
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).differentiableAt.comp y' hs'
  have hne : (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') (A *ᵥ x) ≠ 0 := by
    intro h0
    have hpos := HermNorm.dualNorm_pos h hx0
    rw [hdual, ← hsx, show (h.matᵀ)⁻¹ *ᵥ s (A *ᵥ x) = 0 from h0] at hpos
    simp at hpos
  have key := ChartGramMA.proof e n _ _ hv hne
  have hF : (fun k : Fin e => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) =
      fun _ y' => Real.log ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y')‖ := by
    funext k y'
    simp only [Function.comp_apply, hdual]
  rw [hF, anForm_maDens_eq_geo_maDensity, key, hsx, ← hdual]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem ConePolar.proof (h₁ : SliceDim.Statement) (h₂ : LinearNoetherNormalization.Statement)
    (h₃ : ConeChartGram.Statement) : ConePolar.Statement := by
  intro e
  refine ⟨1, fun n h J ℓ g hJ hdim hℓ hg hgc => ?_⟩
  have hex : ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A :=
    h₂ n e _ (h₁ n e J ℓ hJ hdim hℓ)
  rw [one_mul, varInt, dif_pos hex, h₃ n e h J ℓ g hex.choose hJ hdim hℓ hg hgc hex.choose_spec,
    chartInt]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [chartDens, sheetSum]
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  split_ifs with hs
  · rw [maDens_log_dualNorm_sheet h J ℓ _ y x _ hx hs.choose_spec]
  · rfl

end

end GroundTheory.Heights₂.Heights
