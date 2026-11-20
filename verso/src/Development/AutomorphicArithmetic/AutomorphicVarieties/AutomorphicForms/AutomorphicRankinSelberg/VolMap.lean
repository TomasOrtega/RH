import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

/- English proof (translation)
Rewrite using `[← measurableEmbedding_coe.measurable_comp_iff]`. Establish `h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) = fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ)`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : 0 < w.im`. Simplify using `[hw, ofComplex_apply_of_im_pos hw]`.

Simplify using `only [Function.comp, hw, if_false]`. Rewrite using `[ofComplex_apply_of_im_nonpos (not_lt.mp hw), ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]`. Rewrite using `[h]`. Conclude with `Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id measurable_const`.
-/
private lemma measurable_ofComplex : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw), ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id measurable_const

/- English proof (translation)
Unfold `pt`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
private lemma pt_eq (p : ℝ × ℝ) : pt p.1 p.2 = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold pt
  congr 1
  apply Complex.ext <;> simp

/- English proof (translation)
Establish `hm : Measurable (fun p : ℝ × ℝ => pt p.1 p.2)`. Simplify using `only [pt_eq]`. Conclude with `measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use extensionality with `s hs`.

Establish `hp : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) = (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi 0)`. Rewrite using `[Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hset : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' s ∩ univ ×ˢ Ioi 0 = Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s)`. Use extensionality with `p`. Simplify using `only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_image, pt_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `h3 : 0 < (Complex.measurableEquivRealProd.symm p).im` using `by simpa using h2`. Use `⟨_, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[ofComplex_apply_of_im_pos h3]`.

Introduce and unpack `⟨z, hz, hzp⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hzp, ofComplex_apply]`. Conclude with `hz`. Establish `h3 : 0 < (Complex.measurableEquivRealProd.symm p).im`.

Rewrite using `[← hzp]`. Conclude with `z.im_pos`. Simplify using `using h3`. Rewrite using `[Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset, volume_eq_lintegral, ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb Complex.measurableEquivRealProd.symm.measurableEmbedding]`. Use `lintegral_congr fun p => ?_` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_coe_nnreal]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem volMap : VolMap := by
  have hm : Measurable (fun p : ℝ × ℝ => pt p.1 p.2) := by
    simp only [pt_eq]
    exact measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' s ∩ univ ×ˢ Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_image, pt_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

end UpperTheory.V.Af.Rs
