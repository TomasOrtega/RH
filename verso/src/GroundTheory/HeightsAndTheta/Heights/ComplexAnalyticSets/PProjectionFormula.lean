import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFrameJacobianSum
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphAreaHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

/- English proof (translation)
Introduce `x y h`. Use extensionality with `i`. Use `congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h` as an intermediate fact. Simplify `this` using `[graphPt]`.
-/
theorem graphPt_injective {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by
  intro x y h
  ext i
  have := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h
  simpa [graphPt] using this

/- English proof (translation)
Rewrite using `[differentiableAt_piLp]`. Introduce `j`. Use `show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x`. Break down `hj : e j with i | i` into its components or cases. Simplify using `only [Sum.elim_inl]`.

Conclude with `(differentiableAt_piLp 2).1 differentiableAt_id i`. Simplify using `only [Sum.elim_inr]`. Conclude with `(differentiableAt_piLp 2).1 hF i`.
-/
theorem differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases hj : e j with i | i
  · simp only [Sum.elim_inl]
    exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · simp only [Sum.elim_inr]
    exact (differentiableAt_piLp 2).1 hF i

/- English proof (translation)
Establish `h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) = fun M => √((ContinuousLinearMap.adjoint M ∘L M).det)`. Use function extensionality and compare the values at `M`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `(ContinuousLinearMap.continuous_det.comp ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt`.
-/
theorem continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

/- English proof (translation)
Introduce `d m n e Ω F hΩ hF b B hB`. Establish `hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x` using `fun x hx => differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))`. Use `set A := Ω ∩ graphPt e F ⁻¹' B with hAdef`. Establish `hAΩ : A ⊆ Ω` using `Set.inter_subset_left`. Establish `hA : MeasurableSet A`.

Establish `hc : ContinuousOn (graphPt e F) Ω` using `fun x hx => (hGd x hx).continuousAt.continuousWithinAt`. Establish `hm` using `(hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n)))) hΩ.measurableSet) hB`. Establish `hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B`. Use extensionality with `x`. Simplify using `only [hAdef, Set.mem_inter_iff, Set.mem_preimage]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hx'⟩`. Conclude with `⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩`. Introduce and unpack `⟨hx, hx'⟩`. Conclude with `⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩`.

Rewrite using `[hEq]`. Conclude with `hΩ.measurableSet.inter hm`. Set `πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I` to `fun I => (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ`. Establish `hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) = ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpa …`. Introduce `x hx`.

Use `set L := fderiv ℂ (graphPt e F) x with hL`. Establish `e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) = (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ` using `LinearMap.ext fun v => rfl`. Establish `eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) = (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ` using `fun I => LinearMap.ext fun v => rfl`. Rewrite using `[(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]`. Simplify using `only [eI]`.

Conclude with `congrArg ENNReal.ofReal (h2 d n _ b)`. Conclude with `fun I _ => Real.sqrt_nonneg _`. Establish `hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I))) ((μH[((2 * d : ℕ) : ℝ)]).restrict A)` using `fun I => ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp (continuous_const.clm_comp continuous_id))).measurable.comp (measurable_fderiv ℝ (graphPt e F))).aemeasurable`. Rewrite using `[(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA, setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]`. Use `Finset.sum_congr rfl fun I hI => ?_` and prove the remaining obligations.

Establish `hcard : I.card = d` using `(Finset.mem_powersetCard.1 hI).2`. Establish `hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]`. Establish `hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]`.

Establish `hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x)) ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x` using `fun x hx => ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt`. Rewrite using `[h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Establish `hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} = graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y}`. Use extensionality with `z`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx, rfl⟩, hz⟩`. Conclude with `⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩`. Introduce and unpack `⟨x, ⟨hx, hxy⟩, rfl⟩`.

Conclude with `⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩`. Unfold `frameFibreCount`. Rewrite using `[hset, (graphPt_injective e F).injOn.encard_image]`.
-/
theorem ProjectionFormula.proof (h1 : AreaMultiplicity.Statement) (h2 : FrameJacobianSum.Statement)
    (h3 : GraphAreaHolomorphic.Statement) : ProjectionFormula.Statement := by
  classical
  intro d m n e Ω F hΩ hF b B hB
  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x := fun x hx =>
    differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))
  set A := Ω ∩ graphPt e F ⁻¹' B with hAdef
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hA : MeasurableSet A := by
    have hc : ContinuousOn (graphPt e F) Ω := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    have hm := (hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n))))
      hΩ.measurableSet) hB
    have hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩
    rw [hEq]
    exact hΩ.measurableSet.inter hm

  let πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I := fun I =>
    (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ
  have hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian
      (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) =
      ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian
        ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)) := by
    intro x hx
    set L := fderiv ℂ (graphPt e F) x with hL
    have e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
        (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      LinearMap.ext fun v => rfl
    have eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) =
        (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ :=
      fun I => LinearMap.ext fun v => rfl
    rw [(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]
    · simp only [eI]
      exact congrArg ENNReal.ofReal (h2 d n _ b)
    · exact fun I _ => Real.sqrt_nonneg _
  have hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian
      ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)))
      ((μH[((2 * d : ℕ) : ℝ)]).restrict A) := fun I =>
    ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp
      (continuous_const.clm_comp continuous_id))).measurable.comp
        (measurable_fderiv ℝ (graphPt e F))).aemeasurable
  rw [(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA,
    setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hcard : I.card = d := (Finset.mem_powersetCard.1 hI).2
  have hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  have hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x))
      ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x := fun x hx =>
    ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  rw [h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]
  refine lintegral_congr fun y => ?_
  have hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} =
      graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩
  unfold frameFibreCount
  rw [hset, (graphPt_injective e F).injOn.encard_image]

end

end GroundTheory.Heights₂.Heights
