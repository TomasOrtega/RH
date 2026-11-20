import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts

open UpperTheory.V.Cj.A

/- English proof (translation)
Introduce `Γ V S _ _ _ d G T K`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ s p`. Simplify using `only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨δ, t, ht, hT, hK⟩`. Use `⟨δ * γ, t, ht, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Equiv.Perm.mul_apply]`. Conclude with `hT`. Rewrite using `[map_mul, ContinuousLinearMap.mul_apply]`.

Conclude with `hK`. Introduce and unpack `⟨δ, t, ht, hT, hK⟩`. Use `⟨δ * γ⁻¹, t, ht, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]`. Conclude with `hT`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_right]`. Conclude with `hK`. Introduce `hK s`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `p ⟨γ, t, ht, hT, hp⟩`.

Establish `hc : Continuous fun q : V => t • (G.ρ γ) q` using `continuous_const.smul (G.ρ γ).continuous`. Use `filter_upwards [(hK.preimage hc).mem_nhds hp] with q hq`. Conclude with `⟨γ, t, ht, hT, hq⟩`. Introduce and unpack `K' hKK' s p ⟨γ, t, ht, hT, hp⟩`. Conclude with `⟨γ, t, ht, hT, hKK' hp⟩`.

Introduce `s p t ht`. Simplify using `only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq, map_smul, smul_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, u, hu, hT, hK⟩`. Conclude with `⟨γ, u * t, mul_pos hu ht, hT, hK⟩`.

Introduce and unpack `⟨γ, u, hu, hT, hK⟩`. Use `⟨γ, u / t, div_pos hu ht, hT, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀ u ht.ne']` and apply the resulting hypothesis.
-/
theorem UpperTheory.V.Cj.A.satFacts :
    SatFacts := by
  intro Γ V S _ _ _ d G T K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ s p
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq]
    constructor
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ, t, ht, ?_, ?_⟩
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact hT
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact hK
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ⁻¹, t, ht, ?_, ?_⟩
      · rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hT
      · rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hK
  · intro hK s
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨γ, t, ht, hT, hp⟩
    have hc : Continuous fun q : V => t • (G.ρ γ) q :=
      continuous_const.smul (G.ρ γ).continuous
    filter_upwards [(hK.preimage hc).mem_nhds hp] with q hq
    exact ⟨γ, t, ht, hT, hq⟩
  · rintro K' hKK' s p ⟨γ, t, ht, hT, hp⟩
    exact ⟨γ, t, ht, hT, hKK' hp⟩
  · intro s p t ht
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq, map_smul, smul_smul]
    constructor
    · rintro ⟨γ, u, hu, hT, hK⟩
      exact ⟨γ, u * t, mul_pos hu ht, hT, hK⟩
    · rintro ⟨γ, u, hu, hT, hK⟩
      refine ⟨γ, u / t, div_pos hu ht, hT, ?_⟩
      rwa [div_mul_cancel₀ u ht.ne']
