import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.QuotUniq

/- English proof (translation)
Take `⟨-, -, φ, hφ, h⟩` from `GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν hR hG hμ hU hν`. Take `⟨h1, -, -⟩` from `GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν' hR hG hμ hU hν'`. Establish `h1' : ∀ᵐ x ∂ν', Matrix.of x ∈ GG k r` using `h1`. Establish `hae : ∀ᵐ s ∂μR, Matrix.of s ∈ R` using `hμ.2.2.1`. Establish `hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (lmulM (Matrix.of s) x) ∂μR) ∂ν'` using `hν'`.

Establish `hTm` using `(GlobalTheory.Amp.CutQuot.continuous_act k r).measurable`. Rewrite using `[h F hF hFi, hW' (fun x => φ x * F x) (hφ.1.mul hF)]`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [h1'] with x hx`. Establish `hTx : Measurable fun s : Mt k r => lmulM (Matrix.of s) x` using `hTm.comp (measurable_id.prodMk measurable_const)`.

Establish `h2 : ∫⁻ s, φ (lmulM (Matrix.of s) x) * F (lmulM (Matrix.of s) x) ∂μR = ∫⁻ s, φ (lmulM (Matrix.of s) x) * F x ∂μR`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with s hs`. Rewrite using `[hFi _ hs x hx]`. Rewrite using `[h2, lintegral_mul_const (F x) (f := fun s => φ (lmulM (Matrix.of s) x)) (hφ.1.comp hTx)]`.

Conclude with `mul_le_of_le_one_left zero_le (hφ.2 x hx)`.
-/
theorem lintegral_le {k r : ℕ} {R : Set (Mat k r)} {μG μR ν ν' : Measure (Mt k r)}
    (hR : IsClosedSub k r R) (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (hU : IsUnimod R μR)
    (hν : IsQuotMeas μG μR ν) (hν' : IsQuotMeas μG μR ν') (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) :
    ∫⁻ x, F x ∂ν ≤ ∫⁻ x, F x ∂ν' := by
  obtain ⟨-, -, φ, hφ, h⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν hR hG hμ hU hν
  obtain ⟨h1, -, -⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν' hR hG hμ hU hν'
  have h1' : ∀ᵐ x ∂ν', Matrix.of x ∈ GG k r := h1
  have hae : ∀ᵐ s ∂μR, Matrix.of s ∈ R := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (lmulM (Matrix.of s) x) ∂μR) ∂ν' := hν'
  have hTm := (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  rw [h F hF hFi, hW' (fun x => φ x * F x) (hφ.1.mul hF)]
  refine lintegral_mono_ae ?_
  filter_upwards [h1'] with x hx
  have hTx : Measurable fun s : Mt k r => lmulM (Matrix.of s) x :=
    hTm.comp (measurable_id.prodMk measurable_const)
  have h2 : ∫⁻ s, φ (lmulM (Matrix.of s) x) * F (lmulM (Matrix.of s) x) ∂μR =
      ∫⁻ s, φ (lmulM (Matrix.of s) x) * F x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [hFi _ hs x hx]
  rw [h2, lintegral_mul_const (F x) (f := fun s => φ (lmulM (Matrix.of s) x)) (hφ.1.comp hTx)]
  exact mul_le_of_le_one_left zero_le (hφ.2 x hx)

/- English proof (translation)
Introduce `k r R μG μR ν ν' hR hG hμ hU hν hν' V _ _ _ F hF hFi`. Use `borelize V`. Use `set S : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hS`. Establish `hSm : MeasurableSet S` using `GlobalTheory.Amp.CutQuot.measurable_G k r`. Establish `hFc : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) S` using `hF`.

Use `set F' : Mt k r → V := S.piecewise (fun x : Mt k r => F (Matrix.of x)) (fun _ => 0) with hF'`. Establish `hF'm : Measurable F'` using `hFc.measurable_piecewise continuousOn_const hSm`. Establish `hsep : TopologicalSpace.IsSeparable (Set.range F')`. Establish `h1 : TopologicalSpace.IsSeparable ((fun x : Mt k r => F (Matrix.of x)) '' S)` using `hFc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace S)`. Use `(h1.union (Set.finite_singleton (0 : V)).isSeparable).mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Distinguish the cases in `hx : x ∈ S`. Conclude with `Or.inl ⟨x, hx, by rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]⟩`. Conclude with `Or.inr (by rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; rfl)`. Establish `hinv : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → F' (lmulM ρ x) = F' x`.

Introduce `ρ hρ x hx`. Establish `hx' : lmulM ρ x ∈ S` using `(GlobalTheory.Amp.CutQuot.mul_mem_iff (hR.1 hρ) (Matrix.of x)).2 hx`. Rewrite using `[hF', Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ (show x ∈ S from hx)]`. Conclude with `hFi ρ hρ _ hx`. Establish `hm : MeasurableSpace.comap F' inferInstance ≤ (inferInstance : MeasurableSpace (Mt k r))` using `hF'm.comap_le`.

Establish `hsm : StronglyMeasurable[MeasurableSpace.comap F' inferInstance] F'` using `(@stronglyMeasurable_iff_measurable_separable _ _ _ (MeasurableSpace.comap F' inferInstance) _ _ _ _).2 ⟨comap_measurable F', hsep⟩`. Establish `htrim : ν.trim hm = ν'.trim hm`. Use `@Measure.ext _ (MeasurableSpace.comap F' inferInstance) _ _ fun A hA => ?_` and prove the remaining obligations. Rewrite using `[trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]`. Establish `hAm : MeasurableSet A` using `hm A hA`.

Take `⟨B, -, rfl⟩` from `hA`. Establish `hi : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → (F' ⁻¹' B).indicator (1 : Mt k r → ℝ≥0∞) (lmulM ρ x) = (F' ⁻¹' B).indicator 1 x`. Introduce `ρ hρ x hx`. Simplify using `only [Set.indicator, Set.mem_preimage, hinv ρ hρ x hx, Pi.one_apply]`. Rewrite using `[← lintegral_indicator_one hAm, ← lintegral_indicator_one hAm]`.

Conclude with `le_antisymm (lintegral_le hR hG hμ hU hν hν' _ (measurable_one.indicator hAm) hi) (lintegral_le hR hG hμ hU hν' hν _ (measurable_one.indicator hAm) hi)`. Establish `hae : ∀ ν₀ : Measure (Mt k r), IsQuotMeas μG μR ν₀ → (fun x : Mt k r => F (Matrix.of x)) =ᵐ[ν₀] F'`. Introduce `ν₀ h`. Establish `h1 : ∀ᵐ x ∂ν₀, x ∈ S` using `(GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν₀ hR hG hμ hU h).1`. Use `filter_upwards [h1] with x hx`.

Rewrite using `[hF', Set.piecewise_eq_of_mem _ _ _ hx]`. Rewrite using `[integrable_congr (hae ν hν), integrable_congr (hae ν' hν'), integral_congr_ae (hae ν hν), integral_congr_ae (hae ν' hν'), integral_trim hm hsm, integral_trim hm hsm, htrim]`. Use `⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `integrable_of_integrable_trim hm (htrim ▸ h.trim hm hsm)`. Conclude with `integrable_of_integrable_trim hm (htrim.symm ▸ h.trim hm hsm)`.
-/
theorem quot_uniq : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  intro k r R μG μR ν ν' hR hG hμ hU hν hν' V _ _ _ F hF hFi
  classical
  borelize V
  set S : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hS
  have hSm : MeasurableSet S := GlobalTheory.Amp.CutQuot.measurable_G k r
  have hFc : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) S := hF
  set F' : Mt k r → V := S.piecewise (fun x : Mt k r => F (Matrix.of x)) (fun _ => 0) with hF'
  have hF'm : Measurable F' := hFc.measurable_piecewise continuousOn_const hSm
  have hsep : TopologicalSpace.IsSeparable (Set.range F') := by
    have h1 : TopologicalSpace.IsSeparable ((fun x : Mt k r => F (Matrix.of x)) '' S) :=
      hFc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace S)
    refine (h1.union (Set.finite_singleton (0 : V)).isSeparable).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · exact Or.inl ⟨x, hx, by rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]⟩
    · exact Or.inr (by rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; rfl)
  have hinv : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → F' (lmulM ρ x) = F' x := by
    intro ρ hρ x hx
    have hx' : lmulM ρ x ∈ S := (GlobalTheory.Amp.CutQuot.mul_mem_iff (hR.1 hρ) (Matrix.of x)).2 hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ (show x ∈ S from hx)]
    exact hFi ρ hρ _ hx
  have hm : MeasurableSpace.comap F' inferInstance ≤ (inferInstance : MeasurableSpace (Mt k r)) :=
    hF'm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap F' inferInstance] F' :=
    (@stronglyMeasurable_iff_measurable_separable _ _ _ (MeasurableSpace.comap F' inferInstance)
      _ _ _ _).2 ⟨comap_measurable F', hsep⟩
  have htrim : ν.trim hm = ν'.trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap F' inferInstance) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    have hAm : MeasurableSet A := hm A hA
    obtain ⟨B, -, rfl⟩ := hA
    have hi : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r →
        (F' ⁻¹' B).indicator (1 : Mt k r → ℝ≥0∞) (lmulM ρ x) = (F' ⁻¹' B).indicator 1 x := by
      intro ρ hρ x hx
      simp only [Set.indicator, Set.mem_preimage, hinv ρ hρ x hx, Pi.one_apply]
    rw [← lintegral_indicator_one hAm, ← lintegral_indicator_one hAm]
    exact le_antisymm (lintegral_le hR hG hμ hU hν hν' _ (measurable_one.indicator hAm) hi)
      (lintegral_le hR hG hμ hU hν' hν _ (measurable_one.indicator hAm) hi)
  have hae : ∀ ν₀ : Measure (Mt k r), IsQuotMeas μG μR ν₀ →
      (fun x : Mt k r => F (Matrix.of x)) =ᵐ[ν₀] F' := by
    intro ν₀ h
    have h1 : ∀ᵐ x ∂ν₀, x ∈ S := (GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν₀ hR hG hμ hU h).1
    filter_upwards [h1] with x hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]
  rw [integrable_congr (hae ν hν), integrable_congr (hae ν' hν'), integral_congr_ae (hae ν hν),
    integral_congr_ae (hae ν' hν'), integral_trim hm hsm, integral_trim hm hsm, htrim]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · exact integrable_of_integrable_trim hm (htrim ▸ h.trim hm hsm)
  · exact integrable_of_integrable_trim hm (htrim.symm ▸ h.trim hm hsm)

end GlobalTheory.SnMass.QuotUniq
