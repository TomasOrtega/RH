import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
import ReciprocityTheory.SemistableReduction.SJCoreB
import ReciprocityTheory.SemistableReduction.SJCoreD
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanDrop

/- English proof (translation)
Use `haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)`. Use `set f : UnitSphereC n × Ioi (0:ℝ) → EuclideanSpace ℂ (Fin n) := fun p => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)) with hf_def`. Use `set S := (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hS`. Use `set R0 := Measure.volumeIoiPow (2 * n - 1) with hR0`. Use `set h : Ioi (0:ℝ) → ENNReal := fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)) with hh_def`.

Use `set g : EuclideanSpace ℂ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hg_def`. Establish `hfm : Measurable f`. Apply `Continuous.measurable` to reduce the goal to its premises. Conclude with `(continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)`. Establish `hhm : Measurable h` using `Measurable.ennreal_ofReal (by fun_prop)`.

Establish `hgm : Measurable g` using `Measurable.ennreal_ofReal (by fun_prop)`. Establish `hA : MeasurePreserving f (S.prod R0) volume`. Establish `h1` using `Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (EuclideanSpace ℂ (Fin n)))`. Rewrite `h1` using `[finrank_euclidean_complex]`. Establish `h2 : MeasurePreserving (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin n))).toMeasurableEquiv _ _` using `h1`.

Establish `h3` using `h2.symm`. Establish `h4 : MeasurePreserving (Subtype.val : ({(0 : EuclideanSpace ℂ (Fin n))}ᶜ : Set _) → _) ((volume : Measure (EuclideanSpace ℂ (Fin n))).comap Subtype.val) volume`. Use `⟨measurable_subtype_coe, ?_⟩` and prove the remaining obligations. Rewrite using `[map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]`. Establish `h5` using `h4.comp h3`.

Use `h5 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[hf_def]`. Establish `hB : MeasurePreserving f (S.prod (R0.withDensity h)) ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g)`. Use `⟨hfm, ?_⟩` and prove the remaining obligations.

Rewrite using `[prod_withDensity_right hhm]`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hfm hs, withDensity_apply _ (hfm hs), withDensity_apply _ hs]`. Establish `hpt : ∀ z : UnitSphereC n × Ioi (0:ℝ), h z.2 = g (f z)`. Introduce `z`.

Simplify using `only [hh_def, hg_def, hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < z.2 from z.2.2)]`. Establish `: ‖(z.1 : EuclideanSpace ℂ (Fin n))‖ = 1` using `by simp`. Rewrite using `[this, mul_one]`. Repeatedly rewrite using `[hpt]`. Conclude with `hA.setLIntegral_comp_preimage hs hgm`.

Establish `ha0 : S univ ≠ 0`. Rewrite using `[hS, Measure.toSphere_apply_univ, finrank_euclidean_complex]`. Conclude with `mul_ne_zero (by simp; omega) (Metric.measure_ball_pos _ _ one_pos).ne'`. Establish `haT : S univ ≠ ⊤` using `measure_ne_top _ _`. Establish `hsph : sphereProb n = (S univ)⁻¹ • S` using `sphereProb_eq n`.

Establish `hrad : radProb n = ((R0.withDensity h) univ)⁻¹ • R0.withDensity h`. Simplify using `only [radProb, ProbabilityTheory.cond, Measure.restrict_univ]`. Both sides reduce to the same expression. Establish `hgau : gaussProb n = (((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ)⁻¹ • (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g`. Simplify using `only [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ]`.

Both sides reduce to the same expression. Establish `hmass : ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ = S univ * (R0.withDensity h) univ`. Rewrite using `[← hB.map_eq, Measure.map_apply hfm MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod]`. Use `⟨hfm, ?_⟩` and prove the remaining obligations. Rewrite using `[hsph, hrad, hgau, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul, hB.map_eq, hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]`.
-/
theorem measurePreserving_polar_gaussProb (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)))
      ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  set f : UnitSphereC n × Ioi (0:ℝ) → EuclideanSpace ℂ (Fin n) :=
    fun p => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)) with hf_def
  set S := (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hS
  set R0 := Measure.volumeIoiPow (2 * n - 1) with hR0
  set h : Ioi (0:ℝ) → ENNReal := fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)) with hh_def
  set g : EuclideanSpace ℂ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hg_def
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
  have hhm : Measurable h := Measurable.ennreal_ofReal (by fun_prop)
  have hgm : Measurable g := Measurable.ennreal_ofReal (by fun_prop)

  have hA : MeasurePreserving f (S.prod R0) volume := by
    have h1 := Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))
    rw [finrank_euclidean_complex] at h1
    have h2 : MeasurePreserving (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin n))).toMeasurableEquiv
      _ _ := h1
    have h3 := h2.symm
    have h4 : MeasurePreserving (Subtype.val : ({(0 : EuclideanSpace ℂ (Fin n))}ᶜ : Set _) → _)
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).comap Subtype.val) volume := by
      refine ⟨measurable_subtype_coe, ?_⟩
      rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
    have h5 := h4.comp h3
    convert h5 using 1
    funext p
    simp [hf_def]

  have hB : MeasurePreserving f (S.prod (R0.withDensity h))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) := by
    refine ⟨hfm, ?_⟩
    rw [prod_withDensity_right hhm]
    ext s hs
    rw [Measure.map_apply hfm hs, withDensity_apply _ (hfm hs), withDensity_apply _ hs]
    have hpt : ∀ z : UnitSphereC n × Ioi (0:ℝ), h z.2 = g (f z) := by
      intro z
      simp only [hh_def, hg_def, hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < z.2 from z.2.2)]
      have : ‖(z.1 : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
      rw [this, mul_one]
    simp_rw [hpt]
    exact hA.setLIntegral_comp_preimage hs hgm

  have ha0 : S univ ≠ 0 := by
    rw [hS, Measure.toSphere_apply_univ, finrank_euclidean_complex]
    exact mul_ne_zero (by simp; omega) (Metric.measure_ball_pos _ _ one_pos).ne'
  have haT : S univ ≠ ⊤ := measure_ne_top _ _
  have hsph : sphereProb n = (S univ)⁻¹ • S := sphereProb_eq n
  have hrad : radProb n = ((R0.withDensity h) univ)⁻¹ • R0.withDensity h := by
    simp only [radProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hgau : gaussProb n = (((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g := by
    simp only [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hmass : ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ
      = S univ * (R0.withDensity h) univ := by
    rw [← hB.map_eq, Measure.map_apply hfm MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod]
  refine ⟨hfm, ?_⟩
  rw [hsph, hrad, hgau, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul, hB.map_eq, hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]

end GlobalTheory.SphereMeanDrop
