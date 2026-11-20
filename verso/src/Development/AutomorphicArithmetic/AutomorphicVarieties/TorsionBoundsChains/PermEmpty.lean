import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G X _ _ _ j`. Establish `hC : Subsingleton ((groupHomology.inhomogeneousChains (permRep G X)).X j)`. Express the relevant statement in the definitionally equal form `Subsingleton ((Fin j → G) →₀ (X →₀ ℤ))`. Use `infer_instance`. Establish `hZ : Subsingleton (groupHomology.cycles (permRep G X) j)`.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Conclude with `(ModuleCat.mono_iff_injective (groupHomology.iCycles (permRep G X) j)).1 inferInstance (Subsingleton.elim _ _)`. Establish `hH : Subsingleton (groupHomology (permRep G X) j)`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using groupHomology_induction_on with`.

Consider the case `h a`. Proceed by induction on `b using groupHomology_induction_on with`. Consider the case `h b => rw [Subsingleton.elim a b]`. Use `haveI := hH`. Conclude with `⟨Finite.of_subsingleton, (Finite.card_le_one_iff_subsingleton).2 hH⟩`.
-/
theorem UpperTheory.V.KH.permEmpty :
    ∀ (G X : Type) [Group G] [MulAction G X] [IsEmpty X] (j : ℕ),
      CardLe (groupHomology (permRep G X) j) 1 := by
  intro G X _ _ _ j
  have hC : Subsingleton ((groupHomology.inhomogeneousChains (permRep G X)).X j) := by
    change Subsingleton ((Fin j → G) →₀ (X →₀ ℤ))
    infer_instance
  have hZ : Subsingleton (groupHomology.cycles (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    exact (ModuleCat.mono_iff_injective (groupHomology.iCycles (permRep G X) j)).1
      inferInstance (Subsingleton.elim _ _)
  have hH : Subsingleton (groupHomology (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    induction a using groupHomology_induction_on with
    | h a =>
      induction b using groupHomology_induction_on with
      | h b => rw [Subsingleton.elim a b]
  haveI := hH
  exact ⟨Finite.of_subsingleton, (Finite.card_le_one_iff_subsingleton).2 hH⟩
