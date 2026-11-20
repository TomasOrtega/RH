import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.InfUnram

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank
open scoped Pointwise

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ S A hA R _ M _ _ _ _ _ _ ρ hρ`. Establish `hI` using `(infUnram F Ω (S : Set (HeightOneSpectrum (𝓞 F))) R M ρ hρ).2`. Establish `key : ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S A) (continuous_locFam S A) ↔ ∀ v : S, ∃ m, ∀ g ∈ Dec (F` using `F) (A v), z.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := by`. Introduce `z`. Use `(Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)` and prove the remaining obligations.

Conclude with `((Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)).trans (exists_congr fun _ => ⟨fun h g hg => h ⟨g, hg⟩, fun h (g : Dec (F := F) (A v)) => h g.1 g.2⟩)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `(mem_ShaAbs _ _ _).2 ⟨?_, (hI _).1 ⟨y, rfl⟩⟩` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Introduce `v hv A' hA'`. Take `⟨m, hm⟩` from `(key z).1 hy ⟨v, hv⟩`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hv⟩) hA'`. Use `(Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ?_)` and prove the remaining obligations.

Set `w` to `restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z`. Use `⟨ρ (toGS Ω _ g) m - w.1 g, fun σ => ?_⟩` and prove the remaining obligations. Establish `h1 : (σ : G F Ω) ∈ Dec (F` using `F) (g • A ⟨v, hv⟩) := by rw [hg]; exact σ.2`. Establish `h2` using `GlobalTheory.Cut.ShaBound.coc_conj _ _ w.2.2 g _ m (hm _ (GlobalTheory.Cut.ShaBound.conj_mem_Dec h1))`. Establish `h3 : g * (g⁻¹ * σ * g) * g⁻¹ = σ` using `by group`.

Rewrite `h2` using `[h3]`. Conclude with `h2`. Introduce `hx`. Take `⟨h1, h2⟩` from `(mem_ShaAbs _ _ _).1 hx`. Take `⟨y, rfl⟩` from `(hI x).2 h2`.

Use `⟨y, ?_, rfl⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `(key z).2 fun v => ((mk_mem_ShaAbs _ _ (restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z)).1 hx).1 v.1 v.2 _ (hA v)`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.shaInfl :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [T2Space M] (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction ρ →
      (Sha1 ρ (locFam S A) (continuous_locFam S A)).map (resH1 ρ (toGS Ω _) (continuous_toGS Ω _)) = ShaAbs (ρ.comp (toGS Ω _)) (S : Set (HeightOneSpectrum (𝓞 F))) := by
  intro F Ω _ _ _ _ _ S A hA R _ M _ _ _ _ _ _ ρ hρ
  have hI := (infUnram F Ω (S : Set (HeightOneSpectrum (𝓞 F))) R M ρ hρ).2
  have key : ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S A) (continuous_locFam S A) ↔
      ∀ v : S, ∃ m, ∀ g ∈ Dec (F := F) (A v), z.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := by
    intro z
    refine (Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)
    exact ((Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)).trans
      (exists_congr fun _ => ⟨fun h g hg => h ⟨g, hg⟩, fun h (g : Dec (F := F) (A v)) => h g.1 g.2⟩)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (mem_ShaAbs _ _ _).2 ⟨?_, (hI _).1 ⟨y, rfl⟩⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    intro v hv A' hA'
    obtain ⟨m, hm⟩ := (key z).1 hy ⟨v, hv⟩
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hv⟩) hA'
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ?_)
    let w := restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z
    refine ⟨ρ (toGS Ω _ g) m - w.1 g, fun σ => ?_⟩
    have h1 : (σ : G F Ω) ∈ Dec (F := F) (g • A ⟨v, hv⟩) := by rw [hg]; exact σ.2
    have h2 := GlobalTheory.Cut.ShaBound.coc_conj _ _ w.2.2 g _ m (hm _ (GlobalTheory.Cut.ShaBound.conj_mem_Dec h1))
    have h3 : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rw [h3] at h2
    exact h2
  · intro hx
    obtain ⟨h1, h2⟩ := (mem_ShaAbs _ _ _).1 hx
    obtain ⟨y, rfl⟩ := (hI x).2 h2
    refine ⟨y, ?_, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact (key z).2 fun v => ((mk_mem_ShaAbs _ _ (restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z)).1 hx).1 v.1 v.2 _ (hA v)
