import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionLocalBoundContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableInverseQuarticOverLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitMeasureFiniteCompactSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoefficientMeasurableBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaLocallyConstantBoundedStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

/- English proof (translation)
Introduce `K _ _ h2 hC c n t M hM Sv m g hg`. Take `⟨hfinμ, hae, -⟩` from `GlobalTheory.T.unit_measure_finite_compact_support Sv`. Use `haveI := hfinμ`. Use `haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable`. Take `⟨-, N, B, -, hN, -, hbd, hmeas⟩` from `GlobalTheory.T.product_theta_locally_constant_bounded K h2 c M hM Sv m g hg`.

Take `⟨Wa, hWa, A, hAb, -⟩` from `GlobalTheory.T.real_weil_action_local_bound_continuous n t (GL2Classical.realPart g) hg.2`. Take `⟨hctm, hct1⟩` from `GlobalTheory.T.twisted_coefficient_measurable_bounded K c M Sv m`. Establish `hmem : GL2Classical.realPart g ∈ Wa` using `mem_of_mem_nhds hWa`. Use `set L : Set K := {ξ : K | ∃ a : 𝓞 K, (N : K) * ξ = a} with hL`. Use `set b : K → ℝ := L.indicator (fun ξ => |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹) with hb`.

Establish `hbsum : Summable b`. Rewrite using `[hb, ← summable_subtype_iff_indicator]`. Conclude with `(GlobalTheory.T.summable_inverse_quartic_over_lattice K h2 hC N hN).mul_left _`. Use `set F : K → (∀ v : Sv, (Qv v.1)ˣ) → ℂ := fun ξ u => ctM M Sv m u * thT n t (twM M Sv m u) g ξ with hF`. Establish `hFm : ∀ ξ, Measurable (F ξ)` using `fun ξ => by`.

Simplify using `only [hF, thT]`. Conclude with `hctm.mul ((hmeas ξ).const_mul _)`. Establish `hFb : ∀ ξ, ∀ᵐ u ∂muU Sv, ‖F ξ u‖ ≤ b ξ` using `fun ξ => by filter_upwards [hae] with u hu`. Take `⟨h1, h3⟩` from `hbd u hu ξ`. Establish `hp : 0 ≤ ((1 + ‖embC K ξ‖) ^ 4)⁻¹` using `by positivity`.

Establish `ha : ‖piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K ξ)‖ ≤ |A| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹` using `(hAb _ hmem _).trans (mul_le_mul_of_nonneg_right (le_abs_self A) hp)`. Distinguish the cases in `h0 : ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = 0`. Establish `: F ξ u = 0` using `by simp only [hF, thT, h0, mul_zero]`. Rewrite using `[this, norm_zero]`. Conclude with `Set.indicator_nonneg (fun _ _ => by positivity) _`.

Establish `hξ : ξ ∈ L` using `h3 h0`. Establish `hbξ : b ξ = |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹` using `Set.indicator_of_mem hξ _`. Rewrite using `[hbξ]`. Simplify using `only [hF, thT, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hct1 u`. Conclude with `h1.trans (le_abs_self B)`. Use `_ = |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := by ring`. Establish `hFi : ∀ ξ, Integrable (F ξ) (muU Sv)` using `fun ξ => Integrable.of_bound (hFm ξ).aestronglyMeasurable (b ξ) (hFb ξ)`. Establish `hsum : Summable fun ξ => ∫ u, ‖F ξ u‖ ∂muU Sv`.

Use `Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun _ => norm_nonneg _) (fun ξ => ?_) (hbsum.mul_right ((muU Sv).real Set.univ))` and prove the remaining obligations. Use `norm_integral_le_of_norm_le_const (μ := muU Sv) (f := fun u => ‖F ξ u‖) (C := b ξ) (by filter_upwards [hFb ξ] with u hu; simpa using hu)` as an intermediate fact. Conclude with `(le_abs_self _).trans (by simpa using this)`. Establish `key` using `hasSum_integral_of_summable_integral_norm hFi hsum`. Establish `hint : (∫ u, ∑' ξ, F ξ u ∂muU Sv) = ∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [hF, thP, tsum_mul_left]`. Rewrite `key` using `[hint]`. Conclude with `key`.
-/
theorem hasSum_aT : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
    ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ), ∀ g ∈ Gp M,
    HasSum (fun ξ : K => aT n t M Sv g m ξ) (∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv) := by
  intro K _ _ h2 hC c n t M hM Sv m g hg
  obtain ⟨hfinμ, hae, -⟩ := GlobalTheory.T.unit_measure_finite_compact_support Sv
  haveI := hfinμ
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  obtain ⟨-, N, B, -, hN, -, hbd, hmeas⟩ := GlobalTheory.T.product_theta_locally_constant_bounded K h2 c M hM Sv m g hg
  obtain ⟨Wa, hWa, A, hAb, -⟩ := GlobalTheory.T.real_weil_action_local_bound_continuous n t (GL2Classical.realPart g) hg.2
  obtain ⟨hctm, hct1⟩ := GlobalTheory.T.twisted_coefficient_measurable_bounded K c M Sv m
  have hmem : GL2Classical.realPart g ∈ Wa := mem_of_mem_nhds hWa
  set L : Set K := {ξ : K | ∃ a : 𝓞 K, (N : K) * ξ = a} with hL
  set b : K → ℝ := L.indicator (fun ξ => |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹) with hb
  have hbsum : Summable b := by
    rw [hb, ← summable_subtype_iff_indicator]
    exact (GlobalTheory.T.summable_inverse_quartic_over_lattice K h2 hC N hN).mul_left _
  set F : K → (∀ v : Sv, (Qv v.1)ˣ) → ℂ := fun ξ u => ctM M Sv m u * thT n t (twM M Sv m u) g ξ with hF
  have hFm : ∀ ξ, Measurable (F ξ) := fun ξ => by
    simp only [hF, thT]
    exact hctm.mul ((hmeas ξ).const_mul _)
  have hFb : ∀ ξ, ∀ᵐ u ∂muU Sv, ‖F ξ u‖ ≤ b ξ := fun ξ => by
    filter_upwards [hae] with u hu
    obtain ⟨h1, h3⟩ := hbd u hu ξ
    have hp : 0 ≤ ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := by positivity
    have ha : ‖piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K ξ)‖ ≤
        |A| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ :=
      (hAb _ hmem _).trans (mul_le_mul_of_nonneg_right (le_abs_self A) hp)
    by_cases h0 : ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = 0
    · have : F ξ u = 0 := by simp only [hF, thT, h0, mul_zero]
      rw [this, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · have hξ : ξ ∈ L := h3 h0
      have hbξ : b ξ = |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := Set.indicator_of_mem hξ _
      rw [hbξ]
      simp only [hF, thT, norm_mul]
      calc ‖ctM M Sv m u‖ * (‖piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K ξ)‖ *
            ‖∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ‖)
          ≤ 1 * ((|A| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹) * |B|) := by
            gcongr
            · exact hct1 u
            · exact h1.trans (le_abs_self B)
        _ = |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := by ring
  have hFi : ∀ ξ, Integrable (F ξ) (muU Sv) := fun ξ =>
    Integrable.of_bound (hFm ξ).aestronglyMeasurable (b ξ) (hFb ξ)
  have hsum : Summable fun ξ => ∫ u, ‖F ξ u‖ ∂muU Sv := by
    refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun _ => norm_nonneg _) (fun ξ => ?_)
      (hbsum.mul_right ((muU Sv).real Set.univ))
    have := norm_integral_le_of_norm_le_const (μ := muU Sv) (f := fun u => ‖F ξ u‖) (C := b ξ)
      (by filter_upwards [hFb ξ] with u hu; simpa using hu)
    exact (le_abs_self _).trans (by simpa using this)
  have key := hasSum_integral_of_summable_integral_norm hFi hsum
  have hint : (∫ u, ∑' ξ, F ξ u ∂muU Sv) = ∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF, thP, tsum_mul_left]
  rw [hint] at key
  exact key

end GlobalTheory.CompanionTheory.FexTheta
