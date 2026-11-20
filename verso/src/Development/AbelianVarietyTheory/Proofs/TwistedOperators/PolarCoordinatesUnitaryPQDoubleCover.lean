import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigenStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitPStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitPStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementPStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementPStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLogStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnPStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoordsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatricesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversalStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

/- English proof (translation)
Use `set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS`. Use `set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP`. Establish `key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ)`. Use extensionality with `cd ab`. Establish `h1` using `congrFun (GlobalTheory.T.sinhcAd_mulVec_of_adSq_eigen p q _ _ _ (GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP p q h ab)) cd.1`.

Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1`. Rewrite `h1` using `[← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)]`. Rewrite `h1` using `[Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} => sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1) (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero]`. Simplify using `only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]`.

Rewrite using `[mul_comm (eigP _ _)]`. Conclude with `h1`. Establish `h2` using `congrArg Matrix.det key`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm]`. Establish `h3` using `mul_left_cancel₀ (GlobalTheory.T.det_adSqEigenvectorMatrix_ne_zero p q) h2`.

Unfold `polJ`. Rewrite using `[← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]`.
-/
theorem polJ_aOf_eq_prod (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (GlobalTheory.T.sinhcAd_mulVec_of_adSq_eigen p q _ _ _ (GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (GlobalTheory.T.det_adSqEigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

/- English proof (translation)
Unfold `shc`. Use `split_ifs with hx`. Conclude with `one_pos`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Conclude with `div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h`.

Conclude with `div_pos (Real.sinh_pos_iff.2 h) h`.
-/
theorem shc_pos (x : ℝ) : 0 < shc x := by
  unfold shc
  split_ifs with hx
  · exact one_pos
  · rcases lt_or_gt_of_ne hx with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

/- English proof (translation)
The claim follows from `GlobalTheory.T.polarJacobian_blockDiag_conj_invariant p q _ _ Y (by rw [← matG_mul, mul_inv_cancel, matG_one]) hk ((Ksub T).inv_mem hk)`.
-/
theorem polJ_conj {p q : ℕ} (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) (Y : Mat p q) :
    polJ (matG T k * Y * matG T k⁻¹) = polJ Y :=
  GlobalTheory.T.polarJacobian_blockDiag_conj_invariant p q _ _ Y (by rw [← matG_mul, mul_inv_cancel, matG_one]) hk ((Ksub T).inv_mem hk)

/- English proof (translation)
Take `⟨B, rfl⟩` from `exists_pY hY`. Take `⟨U, hU, V, hV, h, hB⟩` from `GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose p q (Matrix.of B)`. Take `⟨k, hk, hkm⟩` from `GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal p q T U hU V hV`. Use `⟨k, hk, h, ?_⟩` and prove the remaining obligations. Rewrite using `[matG_inv_of_mem T hk, hkm, pY, hB]`.

Simplify using `[aOf, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]`.
-/
theorem exists_conj_aOf {p q : ℕ} (T : GrpData p q) {Y : Mat p q} (hY : Y ∈ pR p q) :
    ∃ k ∈ T.Kset, ∃ h : ℕ → ℝ, Y = matG T k * aOf p q h * matG T k⁻¹ := by
  obtain ⟨B, rfl⟩ := exists_pY hY
  obtain ⟨U, hU, V, hV, h, hB⟩ := GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose p q (Matrix.of B)
  obtain ⟨k, hk, hkm⟩ := GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal p q T U hU V hV
  refine ⟨k, hk, h, ?_⟩
  rw [matG_inv_of_mem T hk, hkm, pY, hB]
  simp [aOf, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨k, hk, h, hB⟩` from `exists_conj_aOf T (pY_mem B)`. Rewrite using `[hB, polJ_conj T hk, polJ_aOf_eq_prod]`. Conclude with `Finset.prod_pos fun _ _ => shc_pos _`.
-/
theorem polJ_pos {p q : ℕ} (T : GrpData p q) (B : Fin p → Fin q → ℂ) : 0 < polJ (pY B) := by
  obtain ⟨k, hk, h, hB⟩ := exists_conj_aOf T (pY_mem B)
  rw [hB, polJ_conj T hk, polJ_aOf_eq_prod]
  exact Finset.prod_pos fun _ _ => shc_pos _

/- English proof (translation)
Distinguish the cases in `h : 1 ≤ p + q`. Conclude with `(GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q h T).2 g`. Establish `hp : p = 0` using `by omega`. Establish `hq : q = 0` using `by omega`. Substitute `hp hq` using the available equality.

Use `⟨g * (T.expt (pY 0))⁻¹, ?_, pY 0, pY_mem 0, by simp⟩` and prove the remaining obligations. Introduce `a`. Apply the tactic sequence `rcases a with a | a <;> exact a.elim0`.
-/
theorem cartan {p q : ℕ} (T : GrpData p q) (g : T.G) : ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  by_cases h : 1 ≤ p + q
  · exact (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q h T).2 g
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    refine ⟨g * (T.expt (pY 0))⁻¹, ?_, pY 0, pY_mem 0, by simp⟩
    intro a
    rcases a with a | a <;> exact a.elim0

/- English proof (translation)
Use `haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem isAddHaar_volume (p q : ℕ) : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

/- English proof (translation)
Take `⟨-, hinv, hlc, hsc, ht2⟩` from `GlobalTheory.T.unitaryPQCover_unimodular p q T`. Take `⟨mK, hprob, hK0, hleft, hright⟩` from `GlobalTheory.T.exists_biinvariant_probability_on_compact_subgroup' T.G (Ksub T) (GlobalTheory.T.isCompact_detSqrtCover_maxCompact p q T)`. Take `⟨L, hLc, hL⟩` from `GlobalTheory.T.exists_continuousOn_polar_log' p q`. Establish `hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B)` using `(GlobalTheory.T.continuous_polarCoordinatesJacobian p q).comp continuous_pY`. Establish `hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B))` using `ENNReal.measurable_ofReal.comp hJc.measurable`.

Establish `hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B)` using `fun B => GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ p q _ (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q B)`. Establish `hem : Measurable fun B : Fin p → Fin q → ℂ => T.expt (pY B)` using `(continuous_expt_pY T).measurable`. Use `haveI : IsLocallyFiniteMeasure ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) := IsLocallyFiniteMeasure.withDensity_ofReal hJc`. Take `⟨c, hc, hf⟩` from `GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal T.G (Fin p → Fin q → ℂ) T.haar mK (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) T.Kset (fun B => T.expt (pY B)) hem hK0 hright (by`. Introduce `h0`.

Rewrite `h0` using `[withDensity_eq_zero_iff hJm.aemeasurable]`. Use `haveI := isAddHaar_volume p q`. Use `haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot := ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ)) Set.univ_nonempty) (by rw [h]; rfl)`. Take `⟨B, hB⟩` from `h0.exists`. Conclude with `absurd hB (by simpa using polJ_pos T B))`.

Use the proof step `(by`. Introduce `C hC`. Establish `hcomp : IsCompact (L '' (matG T '' C))` using `(hC.image (continuous_matG T)).image_of_continuousOn (hLc.mono (by`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `Units.isUnit _))`.

Use `lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top` and prove the remaining obligations. Introduce and unpack `B ⟨k, hk, hB⟩`. Use `⟨_, ⟨_, hB, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[matG_mul, matG_expt]`. Conclude with `hL _ B (matG_star_mul T hk))`.

Use the proof step `(by`. Introduce `g`. Take `⟨ψ, hψc, hψb, hψ⟩` from `GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p p q T L hLc hL (cartan T) g`. Use `⟨ψ, hψc.measurable, GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices p q _ ψ hJc hψc hψb ?_, hψ⟩` and prove the remaining obligations. Use `GlobalTheory.T.jacobian_action_upperRightBlock_exp_coords p q (matG T g) ψ hψc (fun B => by` as an intermediate fact.

Take `⟨κ, hκ, h⟩` from `hψ B`. Take `⟨U, hU, V, hV, hm⟩` from `exists_blocks T hκ`. Use `⟨U, hU, V, hV, ?_⟩` and prove the remaining obligations. Use `congrArg (matG T) h` as an intermediate fact. Rewrite using `[matG_mul, matG_mul, matG_expt, matG_expt, hm] at this)` and apply the resulting hypothesis.

Use the proof step `(fun B => by rw [hdet]; exact polJ_pos T B) (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q)`. Use the proof step `(fun B => GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP p q B (GlobalTheory.T.hasDerivAt_exp_two_add_smul_sinhcAdjoint p q (pY B)))`. Simplify `this)` using `only [hdet]`. Use `⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩` and prove the remaining obligations. Rewrite using `[hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]`.

Use `congr 1`. Use `lintegral_congr fun B => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, mul_comm]`. Conclude with `Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × T.G => f (z.2 * T.expt (pY z.1))) (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))`.
-/
theorem haar_polar {p q : ℕ} (T : GrpData p q) :
    ∃ (c : ℝ) (mK : Measure T.G), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (T.Kset)ᶜ = 0 ∧
    (∀ k ∈ T.Kset, Measure.map (fun x => k * x) mK = mK) ∧
    ∀ f : T.G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂T.haar = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ,
          (∫⁻ k, f (k * T.expt (pY B)) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  obtain ⟨-, hinv, hlc, hsc, ht2⟩ := GlobalTheory.T.unitaryPQCover_unimodular p q T
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ := GlobalTheory.T.exists_biinvariant_probability_on_compact_subgroup' T.G (Ksub T) (GlobalTheory.T.isCompact_detSqrtCover_maxCompact p q T)
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.T.exists_continuousOn_polar_log' p q
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (GlobalTheory.T.continuous_polarCoordinatesJacobian p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ p q _ (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q B)
  have hem : Measurable fun B : Fin p → Fin q → ℂ => T.expt (pY B) := (continuous_expt_pY T).measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal T.G (Fin p → Fin q → ℂ) T.haar mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) T.Kset (fun B => T.expt (pY B)) hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI := isAddHaar_volume p q
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ)) Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using polJ_pos T B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (matG T '' C)) :=
        (hC.image (continuous_matG T)).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact Units.isUnit _))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [matG_mul, matG_expt]
      exact hL _ B (matG_star_mul T hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p p q T L hLc hL (cartan T) g
      refine ⟨ψ, hψc.measurable, GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := GlobalTheory.T.jacobian_action_upperRightBlock_exp_coords p q (matG T g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := exists_blocks T hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg (matG T) h
          rwa [matG_mul, matG_mul, matG_expt, matG_expt, hm] at this)
        (fun B => by rw [hdet]; exact polJ_pos T B) (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q)
        (fun B => GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP p q B (GlobalTheory.T.hasDerivAt_exp_two_add_smul_sinhcAdjoint p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × T.G => f (z.2 * T.expt (pY z.1)))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

/- English proof (translation)
Introduce `X p q`. Use `⟨haar_polar (X.grp p q), fun k hk Y _ => ?_, fun Y hY => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[← matG_inv]`. Conclude with `polJ_conj _ hk Y`. Take `⟨k, hk, h, hY⟩` from `exists_conj_aOf (X.grp p q) hY`.

Conclude with `⟨k, hk, h, by rw [← matG_inv]; exact hY⟩`. Rewrite using `[polJ_aOf_eq_prod, GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP]`.
-/
theorem polar_coordinates : ∀ X : ProvA, CoverHaarIntegration X := by
  intro X p q
  refine ⟨haar_polar (X.grp p q), fun k hk Y _ => ?_, fun Y hY => ?_, fun h => ?_⟩
  · rw [← matG_inv]; exact polJ_conj _ hk Y
  · obtain ⟨k, hk, h, hY⟩ := exists_conj_aOf (X.grp p q) hY
    exact ⟨k, hk, h, by rw [← matG_inv]; exact hY⟩
  · rw [polJ_aOf_eq_prod, GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP]

end GlobalTheory.PolarU
