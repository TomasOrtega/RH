import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ A v hA`. Take `⟨σ, hσ⟩` from `ReciprocityTheory.Gal.exists_isFrob hA`. Establish `hσv : artCl K Ω σ = primeCl v` using `artFrob K Ω A v σ hA hσ`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subgroup.map_le_iff_le_comap]`.

Use `decGen K Ω A v σ _ hA hσ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(artSurj K Ω).2 (Subgroup.zpowers (primeCl v) : Set (ClassGroup (𝓞 K)))`. Introduce `g hg`. Rewrite using `[Subgroup.mem_comap, (artIne K Ω).1 A g hg]`. Conclude with `one_mem _`.

Rewrite using `[Subgroup.mem_comap, hσv]`. Conclude with `Subgroup.mem_zpowers _`. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `⟨σ, hσ.1, hσv⟩`.
-/
theorem UpperTheory.V.Kum.artDec :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (Dec (F := K) A).map (artCl K Ω) = Subgroup.zpowers (primeCl v) := by
  intro K Ω _ _ _ _ _ A v hA
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hσv : artCl K Ω σ = primeCl v := artFrob K Ω A v σ hA hσ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine decGen K Ω A v σ _ hA hσ ?_ ?_ ?_
    · exact (artSurj K Ω).2 (Subgroup.zpowers (primeCl v) : Set (ClassGroup (𝓞 K)))
    · intro g hg
      rw [Subgroup.mem_comap, (artIne K Ω).1 A g hg]
      exact one_mem _
    · rw [Subgroup.mem_comap, hσv]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨σ, hσ.1, hσv⟩
