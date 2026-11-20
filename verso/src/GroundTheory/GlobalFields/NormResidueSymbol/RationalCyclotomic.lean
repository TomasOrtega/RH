import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.Rational
import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

instance isGalois_maxCyclotomic : IsGalois ℚ maxCyclotomic := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ maxCyclotomic _ (IntermediateField.algebra' maxCyclotomic) := by
    rw [← InfiniteGalois.normal_iff_isGalois, ← ker_character]
    infer_instance
  convert h
  exact Subsingleton.elim _ _

abbrev cycRestrict : Gal(ℚ̄/ℚ) →* Gal(maxCyclotomic/ℚ) :=
  AlgEquiv.restrictNormalHom maxCyclotomic

/- English proof (translation)
Establish `: IsGalois ℚ ℚ̄` using `IsAlgClosure.isGalois ℚ ℚ̄`. Conclude with `AlgEquiv.restrictNormalHom_surjective ℚ̄`.
-/
theorem cycRestrict_surjective : Function.Surjective cycRestrict := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  exact AlgEquiv.restrictNormalHom_surjective ℚ̄

/- English proof (translation)
The claim follows from `AlgEquiv.restrictNormal_commutes σ maxCyclotomic x`.
-/
theorem coe_cycRestrict_apply (σ : Gal(ℚ̄/ℚ)) (x : maxCyclotomic) :
    ((cycRestrict σ x : maxCyclotomic) : ℚ̄) = σ x :=
  AlgEquiv.restrictNormal_commutes σ maxCyclotomic x

/- English proof (translation)
Rewrite using `[ker_character]`. Use extensionality with `σ`. Rewrite using `[MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Use `coe_cycRestrict_apply σ ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[h, AlgEquiv.one_apply]`. Conclude with `this.symm`. Introduce `h`. Use extensionality with `x`.

Rewrite using `[coe_cycRestrict_apply, AlgEquiv.one_apply]`. Conclude with `h x x.2`.
-/
theorem ker_cycRestrict : cycRestrict.ker = character.ker := by
  rw [ker_character]
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := coe_cycRestrict_apply σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at this
    exact this.symm
  · intro h
    ext x
    rw [coe_cycRestrict_apply, AlgEquiv.one_apply]
    exact h x x.2

def cycCharacter : Gal(maxCyclotomic/ℚ) ≃* ℤ̂ˣ :=
  (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_cycRestrict).trans
      (QuotientGroup.quotientKerEquivOfSurjective character character_surjective))

/- English proof (translation)
Establish `h : (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm (cycRestrict σ) = (σ : Gal(ℚ̄/ℚ) ⧸ cycRestrict.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[cycCharacter, MulEquiv.trans_apply, MulEquiv.trans_apply, h]`. Both sides reduce to the same expression.
-/
theorem cycCharacter_cycRestrict (σ : Gal(ℚ̄/ℚ)) : cycCharacter (cycRestrict σ) = character σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm
      (cycRestrict σ) = (σ : Gal(ℚ̄/ℚ) ⧸ cycRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [cycCharacter, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

/- English proof (translation)
Take `⟨σ, rfl⟩` from `cycRestrict_surjective τ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[cycCharacter_cycRestrict, SubmonoidClass.coe_pow]`. Rewrite using `[coe_cycRestrict_apply]`. Conclude with `character_spec σ n (by rw [← SubmonoidClass.coe_pow, hζ, OneMemClass.coe_one])`.
-/
theorem cycCharacter_spec (τ : Gal(maxCyclotomic/ℚ)) (n : ℕ+) {ζ : maxCyclotomic}
    (hζ : ζ ^ (n : ℕ) = 1) :
    τ ζ = ζ ^ (ProfiniteInteger.proj n (cycCharacter τ : ℤ̂)).val := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  apply Subtype.ext
  rw [cycCharacter_cycRestrict, SubmonoidClass.coe_pow]
  rw [coe_cycRestrict_apply]
  exact character_spec σ n (by rw [← SubmonoidClass.coe_pow, hζ, OneMemClass.coe_one])

def unitPart : IdeleClassGroup ℚ →* ℤ̂ˣ :=
  (Units.map padicEquiv.symm.toRingHom.toMonoidHom).comp
    ((MonoidHom.snd _ _).comp RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom)

/- English proof (translation)
Introduce `w`. Take `⟨x, hx⟩` from `RationalIdeles.ideleClassGroupEquiv.surjective (1, Units.map padicEquiv.toRingHom.toMonoidHom w)`. Use `⟨x, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [unitPart, MonoidHom.comp_apply, MonoidHom.coe_snd, Units.coe_map]`. Express the relevant statement in the definitionally equal form `padicEquiv.symm ((RationalIdeles.ideleClassGroupEquiv x).2 : _) = _`.

Rewrite using `[hx]`. Simplify using `[ofPadics_toPadics]`.
-/
theorem unitPart_surjective : Function.Surjective unitPart := by
  intro w
  obtain ⟨x, hx⟩ := RationalIdeles.ideleClassGroupEquiv.surjective
    (1, Units.map padicEquiv.toRingHom.toMonoidHom w)
  refine ⟨x, Units.ext ?_⟩
  simp only [unitPart, MonoidHom.comp_apply, MonoidHom.coe_snd, Units.coe_map]
  change padicEquiv.symm ((RationalIdeles.ideleClassGroupEquiv x).2 : _) = _
  rw [hx]
  simp [ofPadics_toPadics]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toPadics (padicEquiv.symm _) q = _`. Rewrite using `[← padicEquiv_apply, RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem toPadicInt_unitPart (x : IdeleClassGroup ℚ) (q : Nat.Primes) :
    toPadicInt q (unitPart x : ℤ̂) =
      ((RationalIdeles.ideleClassGroupEquiv x).2 : Π p : Nat.Primes, ℤ_[p]) q := by
  change toPadics (padicEquiv.symm _) q = _
  rw [← padicEquiv_apply, RingEquiv.apply_symm_apply]
  rfl

def reciprocityMap : IdeleClassGroup ℚ →* Gal(maxCyclotomic/ℚ) :=
  cycCharacter.symm.toMonoidHom.comp unitPart⁻¹

/- English proof (translation)
Simplify using `[reciprocityMap]`.
-/
theorem cycCharacter_reciprocityMap (x : IdeleClassGroup ℚ) :
    cycCharacter (reciprocityMap x) = (unitPart x)⁻¹ := by
  simp [reciprocityMap]

/- English proof (translation)
Introduce `τ`. Take `⟨x, hx⟩` from `unitPart_surjective (cycCharacter τ)⁻¹`. Use `⟨x, cycCharacter.injective ?_⟩` and prove the remaining obligations. Rewrite using `[cycCharacter_reciprocityMap, hx, inv_inv]`.
-/
theorem reciprocityMap_surjective : Function.Surjective reciprocityMap := by
  intro τ
  obtain ⟨x, hx⟩ := unitPart_surjective (cycCharacter τ)⁻¹
  refine ⟨x, cycCharacter.injective ?_⟩
  rw [cycCharacter_reciprocityMap, hx, inv_inv]

/- English proof (translation)
Rewrite using `[← cycCharacter.injective.eq_iff, map_one, cycCharacter_reciprocityMap, inv_eq_one]`. Establish `h : unitPart x = Units.map padicEquiv.symm.toRingHom.toMonoidHom (RationalIdeles.ideleClassGroupEquiv x).2`. Both sides reduce to the same expression. Rewrite using `[h, ← map_one (Units.map padicEquiv.symm.toRingHom.toMonoidHom)]`. Conclude with `(Units.map_injective (f := padicEquiv.symm.toRingHom.toMonoidHom) padicEquiv.symm.injective).eq_iff`.
-/
theorem reciprocityMap_eq_one_iff (x : IdeleClassGroup ℚ) :
    reciprocityMap x = 1 ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 := by
  rw [← cycCharacter.injective.eq_iff, map_one, cycCharacter_reciprocityMap, inv_eq_one]
  have h : unitPart x =
      Units.map padicEquiv.symm.toRingHom.toMonoidHom (RationalIdeles.ideleClassGroupEquiv x).2 :=
    rfl
  rw [h, ← map_one (Units.map padicEquiv.symm.toRingHom.toMonoidHom)]
  exact (Units.map_injective (f := padicEquiv.symm.toRingHom.toMonoidHom)
    padicEquiv.symm.injective).eq_iff

end RationalSymbol

end

end GroundTheory.Global
