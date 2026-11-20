import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.Gys.descend :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContAction ρ → UnrOut ρ S →
      ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, ρS.comp (toGS Ω _) = ρ ∧ ContAction ρS := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ S hρ hU
  have hclosed : IsClosed (ρ.ker : Set (G F Ω)) := by
    have hset : (ρ.ker : Set (G F Ω)) = ⋂ m : M, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    rw [hset]
    refine isClosed_iInter fun m => ?_
    have hc : Continuous fun g : G F Ω => ρ g m :=
      hρ.comp (continuous_id.prodMk continuous_const)
    exact isClosed_eq hc continuous_const
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hg
    obtain ⟨v, hv, A, hA, hgA⟩ := hg
    exact hU v hv A hA g (mem_Ine.mpr hgA)
  refine ⟨QuotientGroup.lift _ ρ hle, ?_, ?_⟩
  · exact MonoidHom.ext fun g => rfl
  · have h2 := (QuotientGroup.isOpenQuotientMap_mk (N := NS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).prodMap
      (IsOpenQuotientMap.id (X := M))).continuous_comp_iff
      (g := fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => (QuotientGroup.lift _ ρ hle) p.1 p.2)
    exact h2.mp hρ
