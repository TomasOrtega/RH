import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphAreaHolomorphic
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

namespace GraphAreaHolomorphic

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_equiv e _ (fun s => ‖Sum.elim (fun i => a i) (fun i => b i) s‖ ^ 2) (fun j => rfl), Fintype.sum_sum_type]`. Apply the tactic sequence `all_goals rfl`.
-/
theorem norm_sq_sumElim {𝕜 : Type*} [RCLike 𝕜] {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (e : ν ≃ ι ⊕ κ) (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => a i) (fun i => b i) (e j)) : EuclideanSpace 𝕜 ν)‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_equiv e _ (fun s => ‖Sum.elim (fun i => a i) (fun i => b i) s‖ ^ 2) (fun j => rfl),
    Fintype.sum_sum_type]
  all_goals rfl

/- English proof (translation)
The claim follows from `norm_sq_sumElim (Equiv.refl _) a b`.
-/
theorem norm_sq_sumElim' {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (Sum.elim (fun i => a i) (fun i => b i)) : EuclideanSpace 𝕜 (ι ⊕ κ))‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
  norm_sq_sumElim (Equiv.refl _) a b

/- English proof (translation)
Use `LinearMap.ext fun v => ext_inner_right ℝ fun w => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply, inner_add_left, LinearMap.adjoint_inner_left]`. Simplify using `only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add]`. Establish `h1` using `h (v + w)`. Establish `h2` using `h v`.

Establish `h3` using `h w`. Simplify using `only [sq] at h1 h2 h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem adjoint_comp_self_of_norm {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    (T : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] H) (h : ∀ v, ‖T v‖ ^ 2 = ‖v‖ ^ 2 + ‖L v‖ ^ 2) :
    LinearMap.adjoint T ∘ₗ T = 1 + LinearMap.adjoint L ∘ₗ L := by
  refine LinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply, inner_add_left,
    LinearMap.adjoint_inner_left]
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  simp only [sq] at h1 h2 h3
  linarith

/- English proof (translation)
Rewrite using `[← LinearMap.det_conj (1 + LinearMap.adjoint L ∘ₗ L) φ.symm.toLinearEquiv]`. Use `congr 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]`.
-/
theorem det_one_add_comp {E E' H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (φ : E ≃ₗᵢ[ℝ] E') (L : E' →ₗ[ℝ] H) :
    LinearMap.det (1 + LinearMap.adjoint (L ∘ₗ φ.toLinearMap) ∘ₗ (L ∘ₗ φ.toLinearMap)) =
      LinearMap.det (1 + LinearMap.adjoint L ∘ₗ L) := by
  rw [← LinearMap.det_conj (1 + LinearMap.adjoint L ∘ₗ L) φ.symm.toLinearEquiv]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

/- English proof (translation)
Rewrite using `[differentiableAt_piLp]`. Introduce `j`. Use `show DifferentiableAt ℝ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x`. Break down `e j with i | i` into its components or cases. Conclude with `(differentiableAt_piLp 2).1 differentiableAt_id i`.

Conclude with `(differentiableAt_piLp 2).1 hF i`.
-/
theorem differentiableAt_graphPt_real {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℝ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hF i

/- English proof (translation)
Use extensionality with `j`. Take `⟨s, rfl⟩` from `e.symm.surjective j`. Establish `hj` using `(hasFDerivWithinAt_piLp 2).1 (hasFDerivWithinAt_univ.2 hG) (e.symm s)`. Rewrite `hj` using `[hasFDerivWithinAt_univ]`. Break down `s with i | i` into its components or cases.

Establish `h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inl i))) (PiLp.proj (𝕜` using `ℝ) 2 (fun _ : Fin d => ℂ) i) x := by`. Simplify `PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i` using `[graphPt]`. Simplify using `using congrArg (fun M => M v) (hj.unique h')`. Establish `hfun : (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i))) = (fun f : EuclideanSpace ℂ (Fin m) => f i) ∘ F`. Use function extensionality and compare the values at `y`.

Simplify using `[graphPt]`. Establish `h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i))) ((PiLp.proj (𝕜` using `ℝ) 2 (fun _ : Fin m => ℂ) i).comp L) x := by`. Rewrite using `[hfun]`. Conclude with `(PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).comp x hF`. Simplify using `using congrArg (fun M => M v) (hj.unique h')`.
-/
theorem hasFDerivAt_graphPt_apply {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    {L : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin m)} (hF : HasFDerivAt F L x)
    {T : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)} (hG : HasFDerivAt (graphPt e F) T x)
    (v : EuclideanSpace ℂ (Fin d)) :
    T v = WithLp.toLp 2 (fun j => Sum.elim (fun i => v i) (fun i => L v i) (e j)) := by
  ext j
  obtain ⟨s, rfl⟩ := e.symm.surjective j
  have hj := (hasFDerivWithinAt_piLp 2).1 (hasFDerivWithinAt_univ.2 hG) (e.symm s)
  rw [hasFDerivWithinAt_univ] at hj
  rcases s with i | i
  · have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inl i)))
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℂ) i) x := by
      simpa [graphPt] using PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i
    simpa using congrArg (fun M => M v) (hj.unique h')
  · have hfun : (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i))) =
        (fun f : EuclideanSpace ℂ (Fin m) => f i) ∘ F := by
      funext y
      simp [graphPt]
    have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i)))
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℂ) i).comp L) x := by
      rw [hfun]
      exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).comp x hF
    simpa using congrArg (fun M => M v) (hj.unique h')

/- English proof (translation)
Set `πd : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin d)` to `{ toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inl k)) map_add' := fun z w => by ext; simp map_smul' := fun c z => by ext; simp }`. Set `πm : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin m)` to `{ toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inr k)) map_add' := fun z w => by ext; simp map_smul' := fun c z => by ext; simp }`. Establish `hz : ∀ z : EuclideanSpace ℂ (Fin n), z = WithLp.toLp 2 (fun j => Sum.elim (fun i => πd z i) (fun i => πm z i) (e j))`. Introduce `z`. Use extensionality with `j`.

Take `⟨s, rfl⟩` from `e.symm.surjective j`. Apply the tactic sequence `rcases s with i | i <;> simp [πd, πm]`. Use `⟨fun z => WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)), ?_, ?_⟩` and prove the remaining obligations. Use `Isometry.of_dist_eq fun z w => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, dist_eq_norm]`.

Establish `hsub : (WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)) : EuclideanSpace ℝ (ι ⊕ κ)) - WithLp.toLp 2 (Sum.elim (fun i => φ (πd w) i) (fun i => φm (πm w) i)) = WithLp.toLp 2 (Sum.elim (fun i => φ (πd (z - w)) i) (fun i => φm (πm (z - w)) i))`. Use extensionality with `s`. Apply the tactic sequence `rcases s with i | i <;> simp [map_sub]`. Rewrite using `[hsub]`. Use `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_` and prove the remaining obligations.

Establish `hn` using `norm_sq_sumElim e (πd (z - w)) (πm (z - w))`. Rewrite `hn` using `[← hz (z - w)]`. Rewrite using `[norm_sq_sumElim', φ.norm_map, φm.norm_map, hn]`. Introduce `F x`. Establish `h1 : πd (graphPt e F x) = x` using `by ext k; simp [πd, graphPt]`.

Establish `h2 : πm (graphPt e F x) = F x` using `by ext k; simp [πm, graphPt]`. Simplify using `only [h1, h2]`.
-/
theorem exists_graph_isometry {d m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Fin n ≃ Fin d ⊕ Fin m) (φ : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (φm : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    ∃ ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℝ (ι ⊕ κ), Isometry ψ ∧
      ∀ (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) x,
        ψ (graphPt e F x) = WithLp.toLp 2 (Sum.elim (fun i => φ x i) (fun i => φm (F x) i)) := by
  let πd : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin d) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  let πm : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inr k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  have hz : ∀ z : EuclideanSpace ℂ (Fin n),
      z = WithLp.toLp 2 (fun j => Sum.elim (fun i => πd z i) (fun i => πm z i) (e j)) := by
    intro z
    ext j
    obtain ⟨s, rfl⟩ := e.symm.surjective j
    rcases s with i | i <;> simp [πd, πm]
  refine ⟨fun z => WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)), ?_, ?_⟩
  · refine Isometry.of_dist_eq fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)) :
        EuclideanSpace ℝ (ι ⊕ κ)) - WithLp.toLp 2 (Sum.elim (fun i => φ (πd w) i) (fun i => φm (πm w) i)) =
        WithLp.toLp 2 (Sum.elim (fun i => φ (πd (z - w)) i) (fun i => φm (πm (z - w)) i)) := by
      ext s
      rcases s with i | i <;> simp [map_sub]
    rw [hsub]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have hn := norm_sq_sumElim e (πd (z - w)) (πm (z - w))
    rw [← hz (z - w)] at hn
    rw [norm_sq_sumElim', φ.norm_map, φm.norm_map, hn]
  · intro F x
    have h1 : πd (graphPt e F x) = x := by ext k; simp [πd, graphPt]
    have h2 : πm (graphPt e F x) = F x := by ext k; simp [πm, graphPt]
    simp only [h1, h2]

end GraphAreaHolomorphic

open GraphAreaHolomorphic in
/- English proof (translation)
Introduce `d m n e Ω F hΩ hF A hAΩ hA`. Establish `hFcC : ContDiffOn ℂ 1 F Ω`. Use `contDiffOn_piLp' 2 fun j x hx => ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Establish `hU : IsOpen ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω)` using `hΩ.preimage (PiLp.continuous_toLp 2 _)`. Establish `hg : DifferentiableOn ℂ (fun w : Fin d → ℂ => F (WithLp.toLp 2 w) j) ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω)` using `fun w hw => (((differentiableAt_piLp 2).1 (hF.differentiableAt (hΩ.mem_nhds hw)) j).comp w (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 w).differentiableAt).differentiableWithinAt`.

Conclude with `((ReciprocityTheory.AnForm.Osgood.osgood d _ _ hU hg (WithLp.ofLp x) hx).contDiffAt).comp x PiLp.contDiff_ofLp.contDiffAt`. Establish `hFc : ContDiffOn ℝ 1 F Ω` using `hFcC.restrict_scalars ℝ`. Establish `hd : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`. Establish `hm : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m`.

Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`. Take `⟨φ⟩ : Nonempty (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * d)))` from `⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hd)).repr⟩`. Take `⟨φm⟩ : Nonempty (EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m)))` from `⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hm)).repr⟩`. Apply the tactic sequence `obtain ⟨ψ, hψ, hψG⟩ := exists_graph_isometry e φ φm`. Take `⟨F', hF'⟩ : ∃ F' : EuclideanSpace ℝ (Fin (2 * d)) → EuclideanSpace ℝ (Fin (2 * m)), F' = fun y => φm (F (φ.symm y))` from `⟨_, rfl⟩`.

Establish `hU : IsOpen (φ '' Ω)` using `φ.toHomeomorph.isOpenMap Ω hΩ`. Establish `hA' : MeasurableSet (φ '' A)` using `φ.toHomeomorph.measurableEmbedding.measurableSet_image.2 hA`. Establish `hF'c : ContDiffOn ℝ 1 F' (φ '' Ω)`. Rewrite using `[hF']`. Conclude with `φm.toContinuousLinearEquiv.contDiff.comp_contDiffOn (hFc.comp φ.symm.toContinuousLinearEquiv.contDiff.contDiffOn (by rintro _ ⟨y, hy, rfl⟩; simpa using hy))`.

Establish `hmp : MeasurePreserving φ μH[((2 * d : ℕ) : ℝ)] μH[((2 * d : ℕ) : ℝ)]` using `φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _`. Establish `himg : (fun x => ψ (graphPt e F x)) '' A = realGraphPt F' '' (φ '' A)`. Rewrite using `[Set.image_image]`. Use `Set.image_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hψG, hF']`.

Simplify using `[realGraphPt]`. Rewrite using `[← hψ.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)) (graphPt e F '' A), Set.image_image, himg, h (2 * d) (2 * m) (φ '' Ω) F' hU hF'c (φ '' A) (Set.image_mono hAΩ) hA', ← hmp.setLIntegral_comp_emb φ.toHomeomorph.measurableEmbedding]`. Use `setLIntegral_congr_fun hA fun x hx => ?_` and prove the remaining obligations. Establish `hFx : HasFDerivAt F (fderiv ℝ F x) x` using `((hF.differentiableAt (hΩ.mem_nhds (hAΩ hx))).restrictScalars ℝ).hasFDerivAt`. Establish `hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) x) x` using `(differentiableAt_graphPt_real e hFx.differentiableAt).hasFDerivAt`.

Use `set K : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) := (φm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin m) →L[ℝ] _).comp ((fderiv ℝ F x).comp (φ.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] _)) with hK`. Establish `hF'x : HasFDerivAt F' K (φ x)`. Rewrite using `[hF']`. Conclude with `φm.toContinuousLinearEquiv.hasFDerivAt.comp _ ((by simpa using hFx : HasFDerivAt F (fderiv ℝ F x) (φ.symm (φ x))).comp _ φ.symm.toContinuousLinearEquiv.hasFDerivAt)`. Simplify using `only [hF'x.fderiv, areaJacobian]`.

Use `congr 2`. Rewrite using `[adjoint_comp_self_of_norm _ ((K : EuclideanSpace ℝ (Fin (2 * d)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) ∘ₗ φ.toLinearMap), det_one_add_comp]`. Introduce `v`. Simplify using `only [ContinuousLinearMap.coe_coe]`. Rewrite using `[hasFDerivAt_graphPt_apply e hFx hG v, norm_sq_sumElim]`.

Simplify using `[hK]`.
-/
theorem GraphAreaHolomorphic.proof (h : AreaGraph.Statement) : GraphAreaHolomorphic.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA

  have hFcC : ContDiffOn ℂ 1 F Ω := by
    refine contDiffOn_piLp' 2 fun j x hx => ContDiffAt.contDiffWithinAt ?_
    have hU : IsOpen ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) :=
      hΩ.preimage (PiLp.continuous_toLp 2 _)
    have hg : DifferentiableOn ℂ (fun w : Fin d → ℂ => F (WithLp.toLp 2 w) j)
        ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) := fun w hw =>
      (((differentiableAt_piLp 2).1 (hF.differentiableAt (hΩ.mem_nhds hw)) j).comp w
        (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 w).differentiableAt).differentiableWithinAt
    exact ((ReciprocityTheory.AnForm.Osgood.osgood d _ _ hU hg (WithLp.ofLp x) hx).contDiffAt).comp x
      PiLp.contDiff_ofLp.contDiffAt
  have hFc : ContDiffOn ℝ 1 F Ω := hFcC.restrict_scalars ℝ
  have hd : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hm : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨φ⟩ : Nonempty (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * d))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hd)).repr⟩
  obtain ⟨φm⟩ : Nonempty (EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hm)).repr⟩
  obtain ⟨ψ, hψ, hψG⟩ := exists_graph_isometry e φ φm
  obtain ⟨F', hF'⟩ : ∃ F' : EuclideanSpace ℝ (Fin (2 * d)) → EuclideanSpace ℝ (Fin (2 * m)),
      F' = fun y => φm (F (φ.symm y)) := ⟨_, rfl⟩
  have hU : IsOpen (φ '' Ω) := φ.toHomeomorph.isOpenMap Ω hΩ
  have hA' : MeasurableSet (φ '' A) := φ.toHomeomorph.measurableEmbedding.measurableSet_image.2 hA
  have hF'c : ContDiffOn ℝ 1 F' (φ '' Ω) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hFc.comp φ.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (by rintro _ ⟨y, hy, rfl⟩; simpa using hy))
  have hmp : MeasurePreserving φ μH[((2 * d : ℕ) : ℝ)] μH[((2 * d : ℕ) : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have himg : (fun x => ψ (graphPt e F x)) '' A = realGraphPt F' '' (φ '' A) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hψG, hF']
    simp [realGraphPt]
  rw [← hψ.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)) (graphPt e F '' A), Set.image_image,
    himg, h (2 * d) (2 * m) (φ '' Ω) F' hU hF'c (φ '' A) (Set.image_mono hAΩ) hA',
    ← hmp.setLIntegral_comp_emb φ.toHomeomorph.measurableEmbedding]
  refine setLIntegral_congr_fun hA fun x hx => ?_
  have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableAt (hΩ.mem_nhds (hAΩ hx))).restrictScalars ℝ).hasFDerivAt
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) x) x :=
    (differentiableAt_graphPt_real e hFx.differentiableAt).hasFDerivAt
  set K : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    (φm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin m) →L[ℝ] _).comp
      ((fderiv ℝ F x).comp (φ.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] _))
    with hK
  have hF'x : HasFDerivAt F' K (φ x) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.hasFDerivAt.comp _
      ((by simpa using hFx : HasFDerivAt F (fderiv ℝ F x) (φ.symm (φ x))).comp _
        φ.symm.toContinuousLinearEquiv.hasFDerivAt)
  simp only [hF'x.fderiv, areaJacobian]
  congr 2
  rw [adjoint_comp_self_of_norm _
    ((K : EuclideanSpace ℝ (Fin (2 * d)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) ∘ₗ φ.toLinearMap),
    det_one_add_comp]
  intro v
  simp only [ContinuousLinearMap.coe_coe]
  rw [hasFDerivAt_graphPt_apply e hFx hG v, norm_sq_sumElim]
  simp [hK]

end

end GroundTheory.Heights₂.Heights
