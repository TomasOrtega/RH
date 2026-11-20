import Mathlib

namespace GlobalTheory

open IsLocalRing

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O M`. Establish `hΦ : Continuous (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M)`. Establish `: (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) = fun v => ∑ i, v i • b i`. Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const`. Set `H : (Module.Free.ChooseBasisIndex O M → O) ≃ₜ M` to `hΦ.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)`. Establish `hH : ∀ v, H v = b.equivFun.symm v` using `fun v => rfl`. Establish `hcpt : CompactSpace M`.

Use `⟨?_⟩` and prove the remaining obligations. Use `isCompact_univ.image H.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ, H.surjective.range_eq]`. Then use the resulting hypothesis. Use `⟨hcpt, ?_, ?_⟩` and prove the remaining obligations. Establish `hm : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)`.

Use `(isAdic_iff.mp hadic).1 1` as an intermediate fact. Simplify using `using this`. Set `S : Set (Module.Free.ChooseBasisIndex O M → O)` to `⋂ i, (fun v => v i) ⁻¹' ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)`. Establish `hS : IsOpen S` using `isOpen_iInter_of_finite fun i => hm.preimage (continuous_apply i)`. Establish `heq : (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) = H '' S`.

Use extensionality with `m`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.lsmul_apply, S, Set.mem_image, Set.mem_iInter, Set.mem_preimage, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton', hH]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Use `⟨b.equivFun (ϖ • x), fun i => ⟨b.equivFun x i, ?_⟩, by simp⟩` and prove the remaining obligations.

Simplify using `[mul_comm]`. Introduce and unpack `⟨v, hv, rfl⟩ choose c hc using hv`. Use `⟨b.equivFun.symm c, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearEquiv.map_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[← hc i, mul_comm]`. Rewrite using `[heq]`. Conclude with `H.isOpenMap S hS`. Use `(continuous_const_smul ϖ).isClosedEmbedding ?_` and prove the remaining obligations.

Conclude with `smul_right_injective M hϖ.ne_zero`.
-/
theorem finite_free_compact_adic_dvr
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧
      Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  classical
  let b := Module.Free.chooseBasis O M
  have hΦ : Continuous (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) := by
    have : (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) =
        fun v => ∑ i, v i • b i := by
      funext v; simp
    rw [this]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  let H : (Module.Free.ChooseBasisIndex O M → O) ≃ₜ M :=
    hΦ.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
  have hH : ∀ v, H v = b.equivFun.symm v := fun v => rfl
  have hcpt : CompactSpace M := by
    refine ⟨?_⟩
    have := isCompact_univ.image H.continuous
    rwa [Set.image_univ, H.surjective.range_eq] at this
  refine ⟨hcpt, ?_, ?_⟩
  · have hm : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
      have := (isAdic_iff.mp hadic).1 1
      simpa using this
    let S : Set (Module.Free.ChooseBasisIndex O M → O) :=
      ⋂ i, (fun v => v i) ⁻¹' ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)
    have hS : IsOpen S := isOpen_iInter_of_finite fun i => hm.preimage (continuous_apply i)
    have heq : (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) = H '' S := by
      ext m
      simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.lsmul_apply, S,
        Set.mem_image, Set.mem_iInter, Set.mem_preimage, hϖ.maximalIdeal_eq,
        Ideal.mem_span_singleton', hH]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨b.equivFun (ϖ • x), fun i => ⟨b.equivFun x i, ?_⟩, by simp⟩
        simp [mul_comm]
      · rintro ⟨v, hv, rfl⟩
        choose c hc using hv
        refine ⟨b.equivFun.symm c, ?_⟩
        rw [← LinearEquiv.map_smul]
        congr 1
        funext i
        simp [← hc i, mul_comm]
    rw [heq]
    exact H.isOpenMap S hS
  · refine (continuous_const_smul ϖ).isClosedEmbedding ?_
    exact smul_right_injective M hϖ.ne_zero

end GlobalTheory
