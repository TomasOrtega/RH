import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.UnramifiedRootsOfUnity
import GroundTheory.LocalFields.UnramifiedGalois

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IntermediateField

section Card

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem card_residueField_of_unramified (h : ramificationIndex K L = 1) :
    Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ Module.finrank K L := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[L]
  rw [← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])]

end Card

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adjoin_gen_eq_top (α : Ksep) : K⟮AdjoinSimple.gen K α⟯ = ⊤ := by
  apply map_injective K⟮α⟯.val
  rw [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]
  exact congrArg (fun x ↦ K⟮x⟯) (AdjoinSimple.coe_gen K α)

def IsUnramifiedSubextension (E : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), ramificationIndex K E = 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isUnramifiedSubextension_iff_exists (E : IntermediateField K Ksep) :
    IsUnramifiedSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), ramificationIndex K E = 1 := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsUnramifiedSubextension.ramificationIndex_eq_one {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] : ramificationIndex K E = 1 :=
  hE.2 inferInstance inferInstance inferInstance inferInstance

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem IsUnramifiedSubextension.isGalois {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsGalois K E := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isGalois_of_unramified K E hE.ramificationIndex_eq_one

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem IsUnramifiedSubextension.isCyclic {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsCyclic (E ≃ₐ[K] E) := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isCyclic_of_unramified K E hE.ramificationIndex_eq_one

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem IsUnramifiedSubextension.card_algEquiv {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
  have := hE.1
  have := hE.isGalois
  exact IsGalois.card_aut_eq_finrank K E

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isPrimitiveRoot_card_pow_sub_one [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : Ksep, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  have hK := natCast_ne_zero_of_residueField (natCast_card_pow_sub_one_ne_zero (K := K) hn)
  have : NeZero ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).mpr hK⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ksep _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isUnramifiedSubextension_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n := by
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hpos : 0 < Nat.card 𝓀[K] ^ n - 1 := by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega
  have hint : IsIntegral K ζ := (hζ.isIntegral hpos).tower_top
  have hfin : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hint
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  have htop := adjoin_gen_eq_top (K := K) ζ
  refine ⟨⟨hfin, fun _ _ _ _ ↦ ramificationIndex_eq_one_of_adjoin_eq_top hζ' hm htop⟩, ?_⟩
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  exact finrank_eq_of_adjoin_eq_top hn hζ' htop

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsUnramifiedSubextension.eq_adjoin {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hEn : Module.finrank K E = n) (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E = K⟮ζ⟯ := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  have h := hE.ramificationIndex_eq_one
  obtain ⟨ξ, hξ, -⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K E h
  rw [card_residueField_of_unramified K E h, hEn] at hξ
  have hξ' : IsPrimitiveRoot (ξ : Ksep) (Nat.card 𝓀[K] ^ n - 1) :=
    hξ.map_of_injective (f := E.val) Subtype.val_injective
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega⟩
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hζE : ζ ∈ E := hi ▸ pow_mem ξ.2 i
  have hle : K⟮ζ⟯ ≤ E := adjoin_simple_le_iff.mpr hζE
  refine (eq_of_le_of_finrank_eq hle ?_).symm
  rw [(isUnramifiedSubextension_adjoin hn hζ).2, hEn]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem existsUnique_isUnramifiedSubextension [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃! E : IntermediateField K Ksep, IsUnramifiedSubextension E ∧ Module.finrank K E = n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ksep) hn
  exact ⟨K⟮ζ⟯, isUnramifiedSubextension_adjoin hn hζ,
    fun E ⟨hE, hEn⟩ ↦ hE.eq_adjoin hEn hn hζ⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isUnramifiedSubextension_adjoin_spec {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n ∧ IsGalois K K⟮ζ⟯ ∧
      IsCyclic (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) ∧ Nat.card (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) = n ∧
      ∀ E : IntermediateField K Ksep, IsUnramifiedSubextension E → Module.finrank K E = n →
        E = K⟮ζ⟯ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  exact ⟨hE, hEn, hE.isGalois, hE.isCyclic, hE.card_algEquiv.trans hEn,
    fun E hE' hE'n ↦ hE'.eq_adjoin hE'n hn hζ⟩

variable {E : IntermediateField K Ksep} (hE : IsUnramifiedSubextension E)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
include hE

end SeparableClosure

end GroundTheory.LocalField
