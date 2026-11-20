import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

namespace SliceFormMass

/- English proof (translation)
Establish `hS : Metric.sphere (0 : Fin n → ℂ) 1 ⊆ {x | x ≠ 0}`. Introduce `x hx hx0`. Rewrite `hx` using `[hx0, mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one hx`. Take `⟨M, hM⟩` from `(isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn (hfc.mono hS)`.

Use `⟨M, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.mpr hx`. Establish `ht : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (inv_ne_zero hn)`. Rewrite using `[← hf0 _ x ht, ← Real.norm_eq_abs]`. Use `hM _ ?_` and prove the remaining obligations.

Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]`.
-/
theorem exists_bound {n : ℕ} (f : (Fin n → ℂ) → ℝ)
    (hf0 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) (hfc : ContinuousOn f {x | x ≠ 0}) :
    ∃ M : ℝ, ∀ x : Fin n → ℂ, x ≠ 0 → |f x| ≤ M := by
  have hS : Metric.sphere (0 : Fin n → ℂ) 1 ⊆ {x | x ≠ 0} := by
    intro x hx hx0
    rw [hx0, mem_sphere_zero_iff_norm, norm_zero] at hx
    exact zero_ne_one hx
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn (hfc.mono hS)
  refine ⟨M, fun x hx => ?_⟩
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ht : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hn)
  rw [← hf0 _ x ht, ← Real.norm_eq_abs]
  refine hM _ ?_
  rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]

/- English proof (translation)
Use `measurable_of_isOpen fun O hO => ?_` and prove the remaining obligations. Establish `hsplit : f ⁻¹' O = ({x | x ≠ 0} ∩ f ⁻¹' O) ∪ ({0} ∩ f ⁻¹' O)`. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x = 0 <;> simp [hx]`. Rewrite using `[hsplit]`.

Conclude with `(hfc.isOpen_inter_preimage (isOpen_ne) hO).measurableSet.union ((Set.finite_singleton (0 : Fin n → ℂ)).subset Set.inter_subset_left).measurableSet`.
-/
theorem measurable_of_continuousOn_ne_zero {n : ℕ} {f : (Fin n → ℂ) → ℝ}
    (hfc : ContinuousOn f {x | x ≠ 0}) : Measurable f := by
  refine measurable_of_isOpen fun O hO => ?_
  have hsplit : f ⁻¹' O = ({x | x ≠ 0} ∩ f ⁻¹' O) ∪ ({0} ∩ f ⁻¹' O) := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  rw [hsplit]
  exact (hfc.isOpen_inter_preimage (isOpen_ne) hO).measurableSet.union
    ((Set.finite_singleton (0 : Fin n → ℂ)).subset Set.inter_subset_left).measurableSet

end SliceFormMass

/- English proof (translation)
Introduce `n e h W F ℓ A f c ψ hW hF hℓ hA hf0 hfc hψ0 hψc`. Take `⟨hprime, hdim, -⟩` from `hI n (e + 1) W F ℓ hW hF hℓ`. Establish `hmem : linForm ℓ - 1 ∈ W ⊔ Ideal.span {linForm ℓ - 1}` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Establish `hint` using `hM n (e + 1) h _ ℓ A hprime hmem hdim hA`. Take `⟨M, hMf⟩` from `SliceFormMass.exists_bound f hf0 hfc`.

Take `⟨C, hCs⟩` from `hC n (e + 1) h c ψ hψ0 hψc`. Establish `hmeas : Measurable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f (fun k x => c k * Real.log (h.dualNorm x) + ψ k x))` using `SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|) (continuous_abs.comp (continuous_fst.mul continuous_snd)).measurable (SliceFormMass.measurable_of_continuousOn_ne_zero hfc) _`. Use `(hint.const_mul (M * |C|)).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Apply the tactic sequence `have hnn : 0 ≤ chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f (fun k x => c k * Real.log (h.dualNorm x) + ψ k x) y := finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> positivity`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg hnn]`.

Use `sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) (M * |C|) _ _ fun x hx s hs => ?_` and prove the remaining obligations. Take `⟨hxZ, hxy⟩` from `hx`. Take `⟨U, hU, hyU, hsd, hsx, -, -⟩` from `hs`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Use `hxZ _ hmem` as an intermediate fact. Simplify using `[linForm] at this`. Establish `hbd` using `hCs s U (A *ᵥ x) hU hyU hsd (by rw [hsx]; exact hx0)`. Rewrite `hbd` using `[show A *ᵥ x = y from hxy]`. Establish `hM0 : 0 ≤ M` using `(abs_nonneg _).trans (hMf x hx0)`.

Rewrite using `[one_mul, abs_mul]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SliceFormMass.proof (hI : SliceIdeal.Statement) (hM : SliceMassFinite.Statement)
    (hC : SheetFormCompare.Statement) : SliceFormMass.Statement := by
  intro n e h W F ℓ A f c ψ hW hF hℓ hA hf0 hfc hψ0 hψc
  obtain ⟨hprime, hdim, -⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  have hmem : linForm ℓ - 1 ∈ W ⊔ Ideal.span {linForm ℓ - 1} :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hint := hM n (e + 1) h _ ℓ A hprime hmem hdim hA
  obtain ⟨M, hMf⟩ := SliceFormMass.exists_bound f hf0 hfc
  obtain ⟨C, hCs⟩ := hC n (e + 1) h c ψ hψ0 hψc
  have hmeas : Measurable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
      (fun k x => c k * Real.log (h.dualNorm x) + ψ k x)) :=
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      (continuous_abs.comp (continuous_fst.mul continuous_snd)).measurable
      (SliceFormMass.measurable_of_continuousOn_ne_zero hfc) _
  refine (hint.const_mul (M * |C|)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hnn : 0 ≤ chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
      (fun k x => c k * Real.log (h.dualNorm x) + ψ k x) y :=
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) (M * |C|) _ _ fun x hx s hs => ?_
  obtain ⟨hxZ, hxy⟩ := hx
  obtain ⟨U, hU, hyU, hsd, hsx, -, -⟩ := hs
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hxZ _ hmem
    simp [linForm] at this
  have hbd := hCs s U (A *ᵥ x) hU hyU hsd (by rw [hsx]; exact hx0)
  rw [show A *ᵥ x = y from hxy] at hbd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMf x hx0)
  rw [one_mul, abs_mul]
  calc |f x| * |ReciprocityTheory.AnForm.maDens
        (fun k => (fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y|
      ≤ M * (|C| * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y|) :=
        mul_le_mul (hMf x hx0) (hbd.trans ((le_abs_self _).trans (abs_mul _ _).le))
          (abs_nonneg _) hM0
    _ = M * |C| * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| := by
        ring

end GroundTheory.Heights₂.Heights
