import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.DecLocal

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ v A hv hA`. Take `⟨j, hj⟩` from `GlobalTheory.PlaceBridge.exists_embedding (l := l) F Ω v A hv hA`. Set `K : Formalism.BasicNotions.Loc.FinExt l` to `⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩`. Establish `hK` using `K.2`. Take `⟨e, he, he', hec⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl`.

Take `⟨hf, hf'⟩` from `GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (PadicAlgCl l) K.1`. Use `⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf', fun r g => Units.ext ?_⟩` and prove the remaining obligations. Establish `hl : l.Prime` using `Fact.out`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: CharZero Ω` using `j.charZero`.

Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ hl.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)`. Establish `hζ'` using `hζ.map_of_injective j.injective`. Establish `ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ hζ.pow_eq_one`.

Use `set σ : GK l K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ`. Establish `hb : σ (j ζ) = j ζ ^ ((cycK l K.1 r σ : ZMod (l ^ r))).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GK l K.1) (PadicAlgCl l) σ) _ hζ'.pow_eq_one`. Establish `hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ)` using `hec g ζ`. Rewrite `hb` using `[hc, ha, map_pow]`. Conclude with `(ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm`.
-/
theorem exists_mulEquiv_cyc : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (e : Dec (F := F) A ≃* GK l K), Continuous e ∧ Continuous e.symm ∧ ∀ (r : ℕ) (g : Dec (F := F) A), cycK l K r (e g) = cycMod F Ω l r (g : G F Ω) := by
  intro F Ω _ _ _ _ _ l _ v A hv hA
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := l) F Ω v A hv hA
  let K : Formalism.BasicNotions.Loc.FinExt l :=
    ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (PadicAlgCl l) K.1
  refine ⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf',
    fun r g => Units.ext ?_⟩
  have hl : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := j.charZero
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have hζ' := hζ.map_of_injective j.injective
  have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
      hζ.pow_eq_one
  set σ : GK l K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ
  have hb : σ (j ζ) = j ζ ^ ((cycK l K.1 r σ : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GK l K.1) (PadicAlgCl l) σ) _
      hζ'.pow_eq_one
  have hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := hec g ζ
  rw [hc, ha, map_pow] at hb
  exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

end GlobalTheory.DecLocal
