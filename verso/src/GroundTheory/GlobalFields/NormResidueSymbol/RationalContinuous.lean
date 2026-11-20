import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.Rational

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_cycRestrict : Continuous cycRestrict := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @Normal ℚ maxCyclotomic _ _ (IntermediateField.algebra' maxCyclotomic) := by
    convert isGalois_maxCyclotomic.to_normal
    exact Subsingleton.elim _ _
  have hc := @InfiniteGalois.restrictNormalHom_continuous ℚ ℚ̄ _ _ _ maxCyclotomic h
  exact hc

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_cycCharacter : Continuous cycCharacter := by
  have : T2Space Gal(maxCyclotomic/ℚ) := krullTopology_t2
  have hq : IsQuotientMap cycRestrict :=
    continuous_cycRestrict.isClosedMap.isQuotientMap continuous_cycRestrict cycRestrict_surjective
  rw [hq.continuous_iff]
  exact continuous_character.congr fun σ ↦ (cycCharacter_cycRestrict σ).symm

def cycCharacterHomeomorph : Gal(maxCyclotomic/ℚ) ≃ₜ* ℤ̂ˣ where
  toMulEquiv := cycCharacter
  continuous_toFun := continuous_cycCharacter
  continuous_invFun :=
    (continuous_cycCharacter.homeoOfEquivCompactToT2 (f := cycCharacter.toEquiv)).symm.continuous

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cycCharacterHomeomorph_apply (τ : Gal(maxCyclotomic/ℚ)) :
    cycCharacterHomeomorph τ = cycCharacter τ :=
  rfl

def unitsPadicHomeomorph : (Π q : Nat.Primes, ℤ_[q])ˣ ≃ₜ* ℤ̂ˣ :=
  unitsContinuousMulEquiv padicEquiv.symm.toMulEquiv continuous_ofPadics continuous_toPadics

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitPart_eq (x : IdeleClassGroup ℚ) :
    unitPart x = unitsPadicHomeomorph (RationalIdeles.ideleClassGroupEquiv x).2 :=
  Units.ext rfl

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_unitPart : Continuous unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.continuous.comp
    (continuous_snd.comp RationalIdeles.ideleClassGroupEquiv.continuous)

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpenMap_unitPart : IsOpenMap unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.toHomeomorph.isOpenMap.comp
    (isOpenMap_snd.comp RationalIdeles.ideleClassGroupEquiv.toHomeomorph.isOpenMap)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reciprocityMap_eq_comp :
    (reciprocityMap : IdeleClassGroup ℚ → Gal(maxCyclotomic/ℚ)) =
      cycCharacterHomeomorph.symm ∘ (·⁻¹) ∘ unitPart :=
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_reciprocityMap : Continuous reciprocityMap := by
  rw [reciprocityMap_eq_comp]
  exact cycCharacterHomeomorph.symm.continuous.comp (continuous_unitPart.inv)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpenMap_reciprocityMap : IsOpenMap reciprocityMap := by
  rw [reciprocityMap_eq_comp]
  exact cycCharacterHomeomorph.symm.toHomeomorph.isOpenMap.comp (IsOpenMap.comp (isOpenMap_inv _) isOpenMap_unitPart)

def positiveRealFactor : Subgroup (IdeleClassGroup ℚ) :=
  (MonoidHom.snd (Units.posSubgroup ℝ) (Π p : Nat.Primes, ℤ_[p])ˣ).ker.comap
    RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_positiveRealFactor_iff (x : IdeleClassGroup ℚ) :
    x ∈ positiveRealFactor ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 :=
  Iff.rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_positiveRealFactor_iff_exists (x : IdeleClassGroup ℚ) :
    x ∈ positiveRealFactor ↔
      ∃ r : Units.posSubgroup ℝ, RationalIdeles.ideleClassGroupEquiv.symm (r, 1) = x := by
  rw [mem_positiveRealFactor_iff]
  constructor
  · intro h
    refine ⟨(RationalIdeles.ideleClassGroupEquiv x).1, ?_⟩
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact Prod.ext rfl h.symm
  · rintro ⟨r, rfl⟩
    rw [ContinuousMulEquiv.apply_symm_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem ker_reciprocityMap : reciprocityMap.ker = positiveRealFactor := by
  ext x
  rw [MonoidHom.mem_ker, reciprocityMap_eq_one_iff, mem_positiveRealFactor_iff]

instance : positiveRealFactor.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def quotientPositiveRealFactorMulEquiv :
    IdeleClassGroup ℚ ⧸ positiveRealFactor ≃* Gal(maxCyclotomic/ℚ) :=
  (QuotientGroup.quotientMulEquivOfEq ker_reciprocityMap.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ reciprocityMap_surjective)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotientPositiveRealFactorMulEquiv_mk (x : IdeleClassGroup ℚ) :
    quotientPositiveRealFactorMulEquiv (x : IdeleClassGroup ℚ ⧸ positiveRealFactor) =
      reciprocityMap x :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_quotientPositiveRealFactorMulEquiv :
    Continuous quotientPositiveRealFactorMulEquiv :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    (continuous_reciprocityMap.congr fun x ↦ (quotientPositiveRealFactorMulEquiv_mk x).symm)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isOpenMap_quotientPositiveRealFactorMulEquiv :
    IsOpenMap quotientPositiveRealFactorMulEquiv := by
  intro U hU
  rw [← Set.image_preimage_eq U QuotientGroup.mk_surjective, Set.image_image]
  simp only [quotientPositiveRealFactorMulEquiv_mk]
  exact isOpenMap_reciprocityMap _ (hU.preimage QuotientGroup.continuous_mk)

def quotientPositiveRealFactorEquiv :
    IdeleClassGroup ℚ ⧸ positiveRealFactor ≃ₜ* Gal(maxCyclotomic/ℚ) where
  toMulEquiv := quotientPositiveRealFactorMulEquiv
  continuous_toFun := continuous_quotientPositiveRealFactorMulEquiv
  continuous_invFun := quotientPositiveRealFactorMulEquiv.toEquiv.continuous_symm_iff.2
    isOpenMap_quotientPositiveRealFactorMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quotientPositiveRealFactorEquiv_mk (x : IdeleClassGroup ℚ) :
    quotientPositiveRealFactorEquiv (x : IdeleClassGroup ℚ ⧸ positiveRealFactor) =
      reciprocityMap x :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compactSpace_gal_maxCyclotomic : CompactSpace Gal(maxCyclotomic/ℚ) :=
  inferInstance

instance compactSpace_quotientPositiveRealFactor :
    CompactSpace (IdeleClassGroup ℚ ⧸ positiveRealFactor) :=
  quotientPositiveRealFactorEquiv.toHomeomorph.symm.compactSpace

end RationalSymbol

end

end GroundTheory.Global
