import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Establish `hd : DiscreteTopology (G ⧸ J)`. Use `discreteTopology_iff_isOpen_singleton.2 fun c => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective c`. Establish `himg : ({(QuotientGroup.mk g : G ⧸ J)} : Set (G ⧸ J)) = QuotientGroup.mk '' ((fun h => g⁻¹ * h) ⁻¹' (J : Set G))`. Use extensionality with `c`.

Take `⟨h, rfl⟩` from `QuotientGroup.mk_surjective c`. Simplify using `only [Set.mem_singleton_iff, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Conclude with `⟨g * (g⁻¹ * h), by simpa using QuotientGroup.eq.1 e.symm, by simp⟩`.

Introduce and unpack `⟨a, ha, e⟩`. Rewrite using `[← e]`. Conclude with `(QuotientGroup.eq.2 ha).symm`. Rewrite using `[himg]`. Conclude with `QuotientGroup.isOpenMap_coe _ (ho.preimage (by fun_prop))`.

Establish `hS : {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} = (fun k => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G)`. Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]`. Conclude with `⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩⟩`. Rewrite using `[hS]`.

Conclude with `(hc.image ((QuotientGroup.continuous_mk).comp (continuous_id.mul continuous_const))).finite_of_discrete`.
-/
private theorem orbit_finite {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J : Subgroup G) (x : G) (ho : IsOpen (J : Set G)) (hc : IsCompact (J : Set G)) :
    {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite := by
  have hd : DiscreteTopology (G ⧸ J) := by
    refine discreteTopology_iff_isOpen_singleton.2 fun c => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have himg : ({(QuotientGroup.mk g : G ⧸ J)} : Set (G ⧸ J)) =
        QuotientGroup.mk '' ((fun h => g⁻¹ * h) ⁻¹' (J : Set G)) := by
      ext c
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
      simp only [Set.mem_singleton_iff, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · intro e
        exact ⟨g * (g⁻¹ * h), by simpa using QuotientGroup.eq.1 e.symm, by simp⟩
      · rintro ⟨a, ha, e⟩
        rw [← e]
        exact (QuotientGroup.eq.2 ha).symm
    rw [himg]
    exact QuotientGroup.isOpenMap_coe _ (ho.preimage (by fun_prop))
  have hS : {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} =
      (fun k => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
    exact ⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩⟩
  rw [hS]
  exact (hc.image ((QuotientGroup.continuous_mk).comp (continuous_id.mul continuous_const))).finite_of_discrete

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_` and prove the remaining obligations. Establish `h1 : ⟪A v, A v⟫_ℂ = ⟪v, v⟫_ℂ`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, h]`. Establish `: B (A v) = v`. Use `congrArg (fun S : H →L[ℂ] H => S v) hBA` as an intermediate fact.

Simplify using `using this`. Rewrite using `[this]`. Establish `h2 : ‖A v‖ ^ 2 = ‖v‖ ^ 2`. Rewrite using `[← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h1]`. Establish `h3 : ‖A v‖ = ‖v‖` using `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2`.

Rewrite using `[h3, one_mul]`.
-/
private theorem norm_le_one_of_adj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) (h : ContinuousLinearMap.adjoint A = B) (hBA : B ∘L A = 1) :
    ‖A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have h1 : ⟪A v, A v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, h]
    have : B (A v) = v := by
      have := congrArg (fun S : H →L[ℂ] H => S v) hBA
      simpa using this
    rw [this]
  have h2 : ‖A v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h1]
  have h3 : ‖A v‖ = ‖v‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  rw [h3, one_mul]

/- English proof (translation)
Establish `hB : (∑ᶠ c ∈ S, ρ c.out) = ∑ c ∈ hS.toFinset, ρ c.out` using `finsum_mem_eq_finite_toFinset_sum _ hS`. Rewrite `hA` using `[hB]`. Establish `hkey : ∀ (y : G) (c : G ⧸ J), (QuotientGroup.mk y : G ⧸ J) = c → ∀ v ∈ V, ρ c.out v = ρ y v`. Introduce and unpack `y _ rfl v hv`. Take `⟨j, hj⟩` from `QuotientGroup.mk_out_eq_mul J y`.

Rewrite using `[hj, hmul, ContinuousLinearMap.comp_apply, (hfix v).1 hv j j.2]`. Establish `hsm : ∀ k ∈ J, ∀ c ∈ S, k • c ∈ S`. Substitute `hSd` using the available equality. Introduce and unpack `k hk _ ⟨k', hk', rfl⟩`. Conclude with `⟨k * k', J.mul_mem hk hk', by rw [mul_assoc]; rfl⟩`.

Establish `hApply : ∀ v, A v = ∑ c ∈ hS.toFinset, ρ c.out (prj V v)` using `fun v => by`. Rewrite using `[hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]`. Establish `hinv : ∀ v, A v ∈ V`. Introduce `v`. Rewrite using `[hfix]`.

Introduce `k hk`. Rewrite using `[hApply, map_sum]`. Use `Finset.sum_equiv (MulAction.toPerm k) (fun c => ?_) (fun c _ => ?_)` and prove the remaining obligations. Simplify using `only [Set.Finite.mem_toFinset, MulAction.toPerm_apply]`. Use `⟨hsm k hk c, fun h => ?_⟩` and prove the remaining obligations.

Simplify using `using hsm k⁻¹ (J.inv_mem hk) _ h`. Use `hkey (k * c.out) (k • c) (by conv_rhs => rw [← QuotientGroup.out_eq' c] rfl) _ (a1 v)` as an intermediate fact. Simplify using `only [MulAction.toPerm_apply]`. Rewrite using `[this, hmul, ContinuousLinearMap.comp_apply]`. Establish `hAP : A ∘L prj V = A`.

Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, hApply, hApply, a2 _ (a1 v)]`. Use `⟨hinv, hAP, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ι _ y hy hr v hv`. Establish `hF : hS.toFinset = Finset.univ.image (fun i => (QuotientGroup.mk (y i) : G ⧸ J))`.

Use extensionality with `c`. Establish `hc : c ∈ S ↔ c ∈ Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J))` using `by rw [hr]`. Simplify using `using hc`. Rewrite using `[hApply, a2 v hv, hF, Finset.sum_image (fun a _ b _ h => hy h)]`. Conclude with `Finset.sum_congr rfl fun i _ => hkey (y i) _ rfl v hv`.

Introduce `T hT`. Rewrite using `[hA]`. Conclude with `(Commute.sum_right _ _ _ fun c _ => hT _).mul_right (hTP T hT)`. Rewrite using `[hA]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Set.ncard_eq_toFinset_card S hS]`. Simplify using the standard rewrite rules.
-/
private theorem hop_abs {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : G → H →L[ℂ] H) (hmul : ∀ g h, ρ (g * h) = ρ g ∘L ρ h)
    (hnorm : ∀ g, ‖ρ g‖ ≤ 1) (J : Subgroup G) (x : G) (V : Submodule ℂ H)
    (hfix : ∀ v, v ∈ V ↔ ∀ k ∈ J, ρ k v = v) (a1 : ∀ v, prj V v ∈ V) (a2 : ∀ v ∈ V, prj V v = v)
    (hP : ‖prj V‖ ≤ 1)
    (hTP : ∀ T : H →L[ℂ] H, (∀ g, Commute T (ρ g)) → Commute T (prj V))
    (S : Set (G ⧸ J)) (hSd : S = {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)})
    (hS : S.Finite) (A : H →L[ℂ] H) (hA : A = (∑ᶠ c ∈ S, ρ c.out) ∘L prj V) :
    (∀ v, A v ∈ V) ∧ A ∘L prj V = A ∧
      (∀ (ι : Type) [Fintype ι] (y : ι → G),
        Function.Injective (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) →
        Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) = S →
        ∀ v ∈ V, A v = ∑ i, ρ (y i) v) ∧
      (∀ T : H →L[ℂ] H, (∀ g, Commute T (ρ g)) → Commute T A) ∧
      ‖A‖ ≤ S.ncard := by
  classical
  have hB : (∑ᶠ c ∈ S, ρ c.out) = ∑ c ∈ hS.toFinset, ρ c.out :=
    finsum_mem_eq_finite_toFinset_sum _ hS
  rw [hB] at hA
  have hkey : ∀ (y : G) (c : G ⧸ J), (QuotientGroup.mk y : G ⧸ J) = c → ∀ v ∈ V,
      ρ c.out v = ρ y v := by
    rintro y _ rfl v hv
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J y
    rw [hj, hmul, ContinuousLinearMap.comp_apply, (hfix v).1 hv j j.2]
  have hsm : ∀ k ∈ J, ∀ c ∈ S, k • c ∈ S := by
    subst hSd
    rintro k hk _ ⟨k', hk', rfl⟩
    exact ⟨k * k', J.mul_mem hk hk', by rw [mul_assoc]; rfl⟩
  have hApply : ∀ v, A v = ∑ c ∈ hS.toFinset, ρ c.out (prj V v) := fun v => by
    rw [hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]
  have hinv : ∀ v, A v ∈ V := by
    intro v
    rw [hfix]
    intro k hk
    rw [hApply, map_sum]
    refine Finset.sum_equiv (MulAction.toPerm k) (fun c => ?_) (fun c _ => ?_)
    · simp only [Set.Finite.mem_toFinset, MulAction.toPerm_apply]
      refine ⟨hsm k hk c, fun h => ?_⟩
      simpa using hsm k⁻¹ (J.inv_mem hk) _ h
    · have := hkey (k * c.out) (k • c) (by
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rfl) _ (a1 v)
      simp only [MulAction.toPerm_apply]
      rw [this, hmul, ContinuousLinearMap.comp_apply]
  have hAP : A ∘L prj V = A := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, hApply, hApply, a2 _ (a1 v)]
  refine ⟨hinv, hAP, ?_, ?_, ?_⟩
  · intro ι _ y hy hr v hv
    have hF : hS.toFinset = Finset.univ.image (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) := by
      ext c
      have hc : c ∈ S ↔ c ∈ Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) := by rw [hr]
      simpa using hc
    rw [hApply, a2 v hv, hF, Finset.sum_image (fun a _ b _ h => hy h)]
    exact Finset.sum_congr rfl fun i _ => hkey (y i) _ rfl v hv
  · intro T hT
    rw [hA]
    exact (Commute.sum_right _ _ _ fun c _ => hT _).mul_right (hTP T hT)
  · rw [hA]
    calc ‖(∑ c ∈ hS.toFinset, ρ c.out) ∘L prj V‖
        ≤ ‖∑ c ∈ hS.toFinset, ρ c.out‖ * ‖prj V‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖∑ c ∈ hS.toFinset, ρ c.out‖ * 1 := by gcongr
      _ = ‖∑ c ∈ hS.toFinset, ρ c.out‖ := mul_one _
      _ ≤ ∑ c ∈ hS.toFinset, (1 : ℝ) := norm_sum_le_of_le _ fun c _ => hnorm _
      _ = S.ncard := by
        rw [Set.ncard_eq_toFinset_card S hS]
        simp

/- English proof (translation)
Introduce `K _ _ n μ _ w J x ho hc`. Take `⟨-, hmem, a1, a2, -, hmul, hone, hadj, hT⟩` from `UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))`. Establish `hfin` using `orbit_finite J x ho hc`. Establish `hfix : ∀ v, v ∈ fixL μ w J ↔ ∀ k ∈ J, rhoL μ w k v = v` using `fun v => by`. Unfold `fixL`.

Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h k hk => h _ (Subgroup.mem_map_of_mem _ hk)`. Introduce and unpack `h _ ⟨k, hk, rfl⟩`. Conclude with `h k hk`.

Establish `hρ : ∀ g h, rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h` using `fun g h => by`. Simplify using `only [rhoL, map_mul, hmul]`. Establish `hnorm : ∀ g, ‖rhoL μ w g‖ ≤ 1` using `fun g => by`. Use `norm_le_one_of_adj _ (rhoF μ (AdelicGLn.localEmbedding w g)⁻¹) (hadj _) ?_` and prove the remaining obligations. Unfold `rhoL`.

Rewrite using `[← hmul, inv_mul_cancel, hone]`. Establish `hP : ‖prj (fixL μ w J)‖ ≤ 1`. Unfold `prj`. Conclude with `Submodule.starProjection_norm_le _`. Establish `hTP : ∀ T : LL μ →L[ℂ] LL μ, (∀ g, Commute T (rhoL μ w g)) → Commute T (prj (fixL μ w J))`.

Introduce `T h`. Use `hT T ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, -, rfl⟩`. Conclude with `h k`. Take `⟨b1, b2, b3, b4, b5⟩` from `hop_abs (rhoL μ w) hρ hnorm J x (fixL μ w J) hfix a1 a2 hP hTP _ rfl hfin (Hop μ w J x) rfl`.

Conclude with `⟨hfin, b1, b2, b3, b4, b5⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.hopBasic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)),
      IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
      {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite ∧
      (∀ v, Hop μ w J x v ∈ fixL μ w J) ∧ Hop μ w J x ∘L prj (fixL μ w J) = Hop μ w J x ∧
      (∀ (ι : Type) [Fintype ι] (y : ι → GL (Fin n) (w.adicCompletion K)), Function.Injective (fun i => (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) →
        Set.range (fun i => (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} →
        ∀ v ∈ fixL μ w J, Hop μ w J x v = ∑ i, rhoL μ w (y i) v) ∧
      (∀ T : LL μ →L[ℂ] LL μ, (∀ g, Commute T (rhoL μ w g)) → Commute T (Hop μ w J x)) ∧
      ‖Hop μ w J x‖ ≤ {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.ncard := by
  intro K _ _ n μ _ w J x ho hc
  obtain ⟨-, hmem, a1, a2, -, hmul, hone, hadj, hT⟩ :=
    UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  have hfin := orbit_finite J x ho hc
  have hfix : ∀ v, v ∈ fixL μ w J ↔ ∀ k ∈ J, rhoL μ w k v = v := fun v => by
    unfold fixL
    rw [hmem]
    constructor
    · exact fun h k hk => h _ (Subgroup.mem_map_of_mem _ hk)
    · rintro h _ ⟨k, hk, rfl⟩
      exact h k hk
  have hρ : ∀ g h, rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := fun g h => by
    simp only [rhoL, map_mul, hmul]
  have hnorm : ∀ g, ‖rhoL μ w g‖ ≤ 1 := fun g => by
    refine norm_le_one_of_adj _ (rhoF μ (AdelicGLn.localEmbedding w g)⁻¹) (hadj _) ?_
    unfold rhoL
    rw [← hmul, inv_mul_cancel, hone]
  have hP : ‖prj (fixL μ w J)‖ ≤ 1 := by
    unfold prj
    exact Submodule.starProjection_norm_le _
  have hTP : ∀ T : LL μ →L[ℂ] LL μ, (∀ g, Commute T (rhoL μ w g)) → Commute T (prj (fixL μ w J)) := by
    intro T h
    refine hT T ?_
    rintro _ ⟨k, -, rfl⟩
    exact h k
  obtain ⟨b1, b2, b3, b4, b5⟩ := hop_abs (rhoL μ w) hρ hnorm J x (fixL μ w J) hfix a1 a2 hP hTP _ rfl hfin
    (Hop μ w J x) rfl
  exact ⟨hfin, b1, b2, b3, b4, b5⟩
