import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set
open UpperHalfPlane hiding I

/- English proof (translation)
Rewrite using `[UpperTheory.V.Af.Rs.pt, ← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]`. Simplify using the standard rewrite rules.
-/
private theorem pt_re_im (x y : ℝ) (hy : 0 < y) :
    (UpperTheory.V.Af.Rs.pt x y).re = x ∧ (UpperTheory.V.Af.Rs.pt x y).im = y := by
  rw [UpperTheory.V.Af.Rs.pt, ← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im,
    UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

/- English proof (translation)
Establish `hre : Continuous fun z : ℍ => z.re` using `Complex.continuous_re.comp UpperHalfPlane.continuous_coe`. Conclude with `(measurableSet_le measurable_const hre.measurable).inter (measurableSet_lt hre.measurable measurable_const)`.
-/
private theorem measurableSet_strip' : MeasurableSet UpperTheory.V.Af.Rs.strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

/- English proof (translation)
Take `⟨hf, hvol⟩` from `hV`. Establish `hs : MeasurableSet ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip)` using `hf measurableSet_strip'`. Establish `hset : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip ∩ (univ ×ˢ Ioi 0) = Ico (0:ℝ) 1 ×ˢ Ioi 0`. Use extensionality with `⟨x, y⟩`. Simplify using `only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico, UpperTheory.V.Af.Rs.strip, mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hy⟩`. Rewrite `h` using `[(pt_re_im x y hy).1]`. Conclude with `⟨h, hy⟩`. Introduce and unpack `⟨h, hy⟩`.

Rewrite using `[(pt_re_im x y hy).1]`. Conclude with `⟨h, hy⟩`. Establish `h0 : (volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ))) = ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0)`. Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hbase : ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))).restrict ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) = ((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))`.

Rewrite using `[h0, Measure.restrict_restrict hs, hset, ← Measure.prod_restrict]`. Rewrite using `[hvol, Measure.restrict_map hf measurableSet_strip', restrict_withDensity hs, hbase]`.
-/
private theorem volume_restrict_strip_eq_map_withDensity (hV : UpperTheory.V.Af.Rs.VolMap) :
    (volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip =
      Measure.map (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hf, hvol⟩ := hV
  have hs : MeasurableSet ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) :=
    hf measurableSet_strip'
  have hset : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip ∩ (univ ×ˢ Ioi 0)
      = Ico (0:ℝ) 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico,
      UpperTheory.V.Af.Rs.strip, mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1]
      exact ⟨h, hy⟩
  have h0 : (volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hbase : ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))).restrict
      ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) =
      ((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0)) := by
    rw [h0, Measure.restrict_restrict hs, hset, ← Measure.prod_restrict]
  rw [hvol, Measure.restrict_map hf measurableSet_strip', restrict_withDensity hs, hbase]

/- English proof (translation)
Introduce `hV φ hφ hint`. Establish `hf : Measurable fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2` using `hV.1`. Establish `hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)` using `by fun_prop`. Establish `hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))), ENNReal.ofReal (1 / p.2 ^ 2) < ⊤` using `Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top`. Establish `him : Continuous fun z : ℍ => z.im` using `Complex.continuous_im.comp UpperHalfPlane.continuous_coe`.

Establish `hm : Measurable fun z : ℍ => φ z.im` using `hφ.comp him.measurable`. Use `show Integrable (fun z : ℍ => φ z.im) ((volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip)`. Rewrite using `[volume_restrict_strip_eq_map_withDensity hV, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable, integrable_withDensity_iff_integrable_smul' hg hlt]`. Establish `h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1))` using `integrable_const 1`. Establish `h2 : Integrable (fun y => φ y / y ^ 2) (volume.restrict (Ioi (0:ℝ)))` using `hint`.

Use `(h1.mul_prod h2).congr ?_` and prove the remaining obligations. Use `filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)] with p hp`. Simplify using `only [Function.comp_apply, (pt_re_im p.1 p.2 hp).2, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / p.2 ^ 2), smul_eq_mul, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Af.Rs.stripIm :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripIm := by
  intro hV φ hφ hint
  have hf : Measurable fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have him : Continuous fun z : ℍ => z.im := Complex.continuous_im.comp UpperHalfPlane.continuous_coe
  have hm : Measurable fun z : ℍ => φ z.im := hφ.comp him.measurable
  show Integrable (fun z : ℍ => φ z.im) ((volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip)
  rw [volume_restrict_strip_eq_map_withDensity hV, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt]
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1)) := integrable_const 1
  have h2 : Integrable (fun y => φ y / y ^ 2) (volume.restrict (Ioi (0:ℝ))) := hint
  refine (h1.mul_prod h2).congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
    with p hp
  simp only [Function.comp_apply, (pt_re_im p.1 p.2 hp).2,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / p.2 ^ 2), smul_eq_mul, one_mul]
  ring
