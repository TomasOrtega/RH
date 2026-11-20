import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KernelIndexFullLattice.absIrr_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsIrr := by
  intro G G₁ H L _ _ _ _ _ _ _ _ π ρ J r hr hρ X hXJ hX
  obtain ⟨⟨hXc, hXinv⟩, hXne, hXmin⟩ := hX
  have hVc : IsClosed ((Submodule.comap J.toLinearMap X : Submodule ℂ H) : Set H) :=
    hXc.preimage J.continuous
  haveI hVcomp : CompleteSpace (Submodule.comap J.toLinearMap X) := hVc.completeSpace_coe
  have hinv : π.IsInvariant (Submodule.comap J.toLinearMap X) := by
    intro g₁ v hv
    obtain ⟨g, rfl⟩ := hr g₁
    show J (π (r g) v) ∈ X
    rw [← hρ]
    exact hXinv g _ hv
  refine ⟨hVcomp, hinv, ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    obtain ⟨h, rfl⟩ := hXJ hx
    refine nontrivial_of_ne (⟨h, hx⟩ : Submodule.comap J.toLinearMap X) 0 ?_
    intro e
    apply hx0
    have e' : h = 0 := congrArg Subtype.val e
    rw [e', map_zero]
  · intro U' hU'c hU'inv
    let V := Submodule.comap J.toLinearMap X
    let U : Submodule ℂ L := (U'.map V.subtype).map J.toLinearMap
    have hUX : U ≤ X := by
      rintro _ ⟨_, ⟨u, _, rfl⟩, rfl⟩
      exact u.2
    have hU'H : IsClosed ((U'.map V.subtype : Submodule ℂ H) : Set H) := by
      rw [Submodule.map_coe]
      exact hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hU'c
    have hUc : IsClosed (U : Set L) := by
      rw [Submodule.map_coe]
      exact J.isometry.isClosedEmbedding.isClosedMap _ hU'H
    have hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
      rintro g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨_, ⟨⟨π (r g) u, hinv _ _ u.2⟩, hU'inv (r g) u hu, rfl⟩, ?_⟩
      exact (hρ g u).symm
    rcases hXmin U hUX ⟨hUc, hUinv⟩ with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have hJu : J u ∈ U := ⟨u, ⟨u, hu, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hJu
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have hn : ‖(u : H)‖ = 0 := by rw [← J.norm_map, hJu, norm_zero]
      simpa using hn
    · right
      rw [eq_top_iff]
      intro u _
      have hJu : J u ∈ U := by
        rw [h]
        exact u.2
      obtain ⟨_, ⟨u', hu', rfl⟩, he⟩ := hJu
      have : u' = u := Subtype.ext (J.injective he)
      rw [← this]
      exact hu'
