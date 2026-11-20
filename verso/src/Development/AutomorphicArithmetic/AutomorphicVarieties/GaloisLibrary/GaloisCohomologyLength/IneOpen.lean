import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ v A hl hA`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: Algebra.IsAlgebraic ℚ Ω` using `Algebra.IsAlgebraic.trans ℚ F Ω`. Establish `: IsAlgClosure ℚ Ω` using `⟨inferInstance, inferInstance⟩`.

Establish `: IsGalois ℚ Ω` using `IsAlgClosure.isGalois ℚ Ω`. Establish `: IsGalois F Ω` using `IsAlgClosure.isGalois F Ω`. Establish `hl' : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal` using `hl`. Establish `hv : A.valuation (l : Ω) < 1`. Simplify using `using (hA _).2 hl'`.

Set `K : IntermediateField ℚ Ω` to `(IsScalarTower.toAlgHom ℚ F Ω).fieldRange`. Establish `hK : Module.finrank ℚ F = K.fixingSubgroup.index`. Rewrite using `[← IntermediateField.finrank_eq_fixingSubgroup_index]`. Conclude with `(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finrank_eq`. Establish `hK0 : K.fixingSubgroup.index ≠ 0`.

Rewrite using `[← hK]`. Conclude with `Module.finrank_pos.ne'`. Set `I : Subgroup (G ℚ Ω)` to `Ine (F := ℚ) A`. Set `f : I →* ℤ_[l]ˣ` to `(cycZ ℚ Ω l).comp I.subtype`. Establish `hf : Function.Surjective f` using `fun u => by`.

Take `⟨σ, hσ, h⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u`. Conclude with `⟨⟨σ, hσ⟩, h⟩`. Establish `hle : (K.fixingSubgroup.subgroupOf I).map f ≤ ineImage F l A`. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Establish `hmem : σ.1 ∈ K.fixingSubgroup` using `hσ`.

Set `g : G F Ω` to `{ σ.1.toRingEquiv with commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }`. Conclude with `⟨g, σ.2, rfl⟩`. Establish `hrel0 : K.fixingSubgroup.relIndex ⊤ ≠ 0` using `by rwa [Subgroup.relIndex_top_right]`. Establish `hrel : K.fixingSubgroup.relIndex I ≤ K.fixingSubgroup.index`. Rewrite using `[← Subgroup.relIndex_top_right]`.

Conclude with `Subgroup.relIndex_le_of_le_right le_top hrel0`. Establish `hrelI : K.fixingSubgroup.relIndex I ≠ 0` using `fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)`. Establish `hdvd : (ineImage F l A).index ∣ K.fixingSubgroup.relIndex I` using `(Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)`. Establish `h0 : (ineImage F l A).index ≠ 0` using `ne_zero_of_dvd_ne_zero hrelI hdvd`. Use `⟨?_, h0, ?_⟩` and prove the remaining obligations.

Establish `: (ineImage F l A).FiniteIndex` using `⟨h0⟩`. Use `Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_` and prove the remaining obligations. Conclude with `((isClosed_Ine (F := F) A).isCompact.image (continuous_cycZ F Ω l)).isClosed`. Rewrite using `[hK]`. Conclude with `(Nat.le_of_dvd (Nat.pos_of_ne_zero hrelI) hdvd).trans hrel`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.ineOpen :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), v ∈ Above F l → IsPlaceOver A v → IsOpen (ineImage F l A : Set ℤ_[l]ˣ) ∧ (ineImage F l A).index ≠ 0 ∧ (ineImage F l A).index ≤ Module.finrank ℚ F := by
  intro F Ω _ _ _ _ _ l _ v A hl hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hl' : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := hl
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl'
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have hK : Module.finrank ℚ F = K.fixingSubgroup.index := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finrank_eq
  have hK0 : K.fixingSubgroup.index ≠ 0 := by
    rw [← hK]; exact Module.finrank_pos.ne'
  let I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A
  let f : I →* ℤ_[l]ˣ := (cycZ ℚ Ω l).comp I.subtype
  have hf : Function.Surjective f := fun u => by
    obtain ⟨σ, hσ, h⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
    exact ⟨⟨σ, hσ⟩, h⟩
  have hle : (K.fixingSubgroup.subgroupOf I).map f ≤ ineImage F l A := by
    rintro _ ⟨σ, hσ, rfl⟩
    have hmem : σ.1 ∈ K.fixingSubgroup := hσ
    let g : G F Ω := { σ.1.toRingEquiv with
      commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
    exact ⟨g, σ.2, rfl⟩
  have hrel0 : K.fixingSubgroup.relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  have hrel : K.fixingSubgroup.relIndex I ≤ K.fixingSubgroup.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top hrel0
  have hrelI : K.fixingSubgroup.relIndex I ≠ 0 := fun h =>
    hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
  have hdvd : (ineImage F l A).index ∣ K.fixingSubgroup.relIndex I :=
    (Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)
  have h0 : (ineImage F l A).index ≠ 0 := ne_zero_of_dvd_ne_zero hrelI hdvd
  refine ⟨?_, h0, ?_⟩
  · have : (ineImage F l A).FiniteIndex := ⟨h0⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    exact ((isClosed_Ine (F := F) A).isCompact.image (continuous_cycZ F Ω l)).isClosed
  · rw [hK]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hrelI) hdvd).trans hrel
