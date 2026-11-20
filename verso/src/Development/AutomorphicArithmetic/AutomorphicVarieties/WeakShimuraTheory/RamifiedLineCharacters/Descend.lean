import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ S hρ hU`. Establish `hclosed : IsClosed (ρ.ker : Set (G F Ω))`. Establish `hset : (ρ.ker : Set (G F Ω)) = ⋂ m : M, {g | ρ g m = m}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h m`. Rewrite using `[h]`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `LinearMap.ext h`. Rewrite using `[hset]`. Use `isClosed_iInter fun m => ?_` and prove the remaining obligations. Establish `hc : Continuous fun g : G F Ω => ρ g m` using `hρ.comp (continuous_id.prodMk continuous_const)`. Conclude with `isClosed_eq hc continuous_const`.

Establish `hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker`. Unfold `NS`. Use `Subgroup.topologicalClosure_minimal _ ?_ hclosed` and prove the remaining obligations. Use `Subgroup.normalClosure_le_normal ?_` and prove the remaining obligations. Introduce `g hg`.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq] at hg`. Take `⟨v, hv, A, hA, hgA⟩` from `hg`. Conclude with `hU v hv A hA g (mem_Ine.mpr hgA)`. Use `⟨QuotientGroup.lift _ ρ hle, ?_, ?_⟩` and prove the remaining obligations. Conclude with `MonoidHom.ext fun g => rfl`.

Establish `h2` using `(QuotientGroup.isOpenQuotientMap_mk (N := NS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).prodMap (IsOpenQuotientMap.id (X := M))).continuous_comp_iff (g := fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => (QuotientGroup.lift _ ρ hle) p.1 p.2)`. Conclude with `h2.mp hρ`.
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
