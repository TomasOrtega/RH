import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob.ResRange

variable (Ω K L : Type) [Field Ω] [Field K] [Algebra K Ω] [Field L] [Algebra L Ω] [Algebra K L]
  [IsScalarTower K L Ω]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resG_apply (τ : G L Ω) (z : Ω) : resG K L Ω τ z = τ z := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem resG_injective : Function.Injective (resG K L Ω) := by
  intro a b h
  ext z
  have := congrArg (fun σ : G K Ω => σ z) h
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mem_range_iff (σ : G K Ω) :
    σ ∈ (resG K L Ω).range ↔ ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    refine ⟨{ σ.toRingEquiv with commutes' := h }, ?_⟩
    ext z
    rfl

def embAction : MulAction (G K Ω) (L →ₐ[K] Ω) where
  smul σ φ := (σ : Ω →ₐ[K] Ω).comp φ
  one_smul φ := by ext; rfl
  mul_smul σ τ φ := by ext; rfl

attribute [local instance] embAction

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem stabilizer_eq :
    MulAction.stabilizer (G K Ω) (IsScalarTower.toAlgHom K L Ω) =
      (resG K L Ω).range := by
  ext σ
  rw [mem_range_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : L →ₐ[K] Ω => φ x) h
    exact this
  · intro h
    show (σ : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω) = IsScalarTower.toAlgHom K L Ω
    ext x
    exact h x

end GlobalTheory.DelGlob.ResRange

namespace GlobalTheory.DelGlob.ResRange

variable (Ω K L : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

attribute [local instance] embAction

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem orbit_eq_univ :
    MulAction.orbit (G K Ω) (IsScalarTower.toAlgHom K L Ω) = Set.univ := by
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  ext φ
  simp only [Set.mem_univ, iff_true]
  let ψ : Ω →ₐ[K] Ω := φ.liftNormal Ω
  let σ : G K Ω := AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ)
  refine ⟨σ, ?_⟩
  show (σ : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω) = φ
  ext x
  exact AlgHom.liftNormal_commutes φ Ω x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem index_range : (resG K L Ω).range.index = Module.finrank K L := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  rw [← stabilizer_eq, MulAction.index_stabilizer, orbit_eq_univ Ω K L, Set.ncard_univ,
    Nat.card_eq_fintype_card, AlgHom.card]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isOpen_map (N : Subgroup (G L Ω)) (hN : IsOpen (N : Set (G L Ω))) :
    IsOpen (N.map (resG K L Ω) : Set (G K Ω)) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨E, hE, hEN⟩ := (krullTopology_mem_nhds_one_iff L Ω (N : Set (G L Ω))).mp
    (hN.mem_nhds N.one_mem)
  have hfin : FiniteDimensional K ↥(E.restrictScalars K) :=
    (Module.Finite.trans (R := K) L ↥E : FiniteDimensional K ↥E)
  refine Subgroup.isOpen_mono (H₁ := (E.restrictScalars K).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro σ hσ
  have hfix : ∀ z ∈ E, σ z = z := fun z hz =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ z hz
  obtain ⟨τ, hτ⟩ := (mem_range_iff Ω K L σ).2 (fun x => hfix _ (E.algebraMap_mem x))
  refine ⟨τ, hEN ?_, hτ⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  rw [← resG_apply Ω K L, hτ]
  exact hfix z hz

end GlobalTheory.DelGlob.ResRange

namespace GlobalTheory.DelGlob

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem resG_range_spec : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω], Function.Injective (resG K L Ω) ∧ (∀ (τ : G L Ω) (z : Ω), resG K L Ω τ z = τ z) ∧ (∀ σ : G K Ω, σ ∈ (resG K L Ω).range ↔ ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ∧ IsOpen ((resG K L Ω).range : Set (G K Ω)) ∧ (resG K L Ω).range.index = Module.finrank K L ∧ ∀ N : Subgroup (G L Ω), IsOpen (N : Set (G L Ω)) → IsOpen (N.map (resG K L Ω) : Set (G K Ω)) := by
  intro Ω _ K _ _ _ _ L _ _ _ _ _ _
  refine ⟨ResRange.resG_injective Ω K L, ResRange.resG_apply Ω K L, ResRange.mem_range_iff Ω K L, ?_,
    ResRange.index_range Ω K L, ResRange.isOpen_map Ω K L⟩
  have h := ResRange.isOpen_map Ω K L ⊤ isOpen_univ
  rwa [← MonoidHom.range_eq_map] at h

end GlobalTheory.DelGlob
