import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RationalDiagonal
import GroundTheory.GlobalFields.NormResidueSymbol.RationalCyclotomic

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

attribute [local instance] galCommGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

section Unit

def unitAt (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℤ_[prime v]ˣ :=
  Units.map ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv :
    v.adicCompletionIntegers ℚ →* ℤ_[prime v]) ((RationalIdeles.positiveSubgroupEquiv y).2 v)

/- English proof (translation)
Rewrite using `[pow_zero, mul_one]`. Both sides reduce to the same expression.
-/
theorem padicRingEquiv_finiteProj (y : RationalIdeles.positiveSubgroup)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    padicRingEquiv v (finiteProj v (y : IdeleGroup ℚ) : v.adicCompletion ℚ) =
      ((unitAt y v : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ (0 : ℕ) := by
  rw [pow_zero, mul_one]
  rfl

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

/- English proof (translation)
Establish `hn : prime v₀ ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero`. Rewrite using `[ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀} fun v hv ↦ by`. Rewrite using `[localSymbol_apply_of_pow_eq_one_of_coprime v L _ (unitAt y v) 0 (padicRingEquiv_finiteProj y v) (Nat.Coprime.pow_left n (coprime_prime (by simpa using hv : v ≠ v₀).symm)) hζ, pow_zero, pow_one],`. Use the proof step `Finset.prod_singleton, infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ,`. Use the proof step `extensionEmbeddingOfIsReal_infiniteProj,`.

Use `if_neg (not_lt.2 (RationalIdeles.mem_positiveSubgroup.1 y.2).2.le)]`. Conclude with `localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (unitAt y v₀) 0 (by rw [padicRingEquiv_finiteProj y v₀, pow_zero, zpow_zero]) hζ`.
-/
theorem ideleSymbol_apply_of_mem_positiveSubgroup (y : RationalIdeles.positiveSubgroup)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    ideleSymbol ℚ L y ζ =
      ζ ^ (PadicInt.toZModPow n (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀} fun v hv ↦ by
      rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (unitAt y v) 0
        (padicRingEquiv_finiteProj y v)
        (Nat.Coprime.pow_left n (coprime_prime (by simpa using hv : v ≠ v₀).symm)) hζ,
        pow_zero, pow_one],
    Finset.prod_singleton, infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ,
    extensionEmbeddingOfIsReal_infiniteProj,
    if_neg (not_lt.2 (RationalIdeles.mem_positiveSubgroup.1 y.2).2.le)]
  exact localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (unitAt y v₀) 0
    (by rw [padicRingEquiv_finiteProj y v₀, pow_zero, zpow_zero]) hζ

end Unit

/- English proof (translation)
Establish `h` using `toPadicInt_unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) (Rat.HeightOneSpectrum.primesEquiv v)`. Rewrite `h` using `[RationalIdeles.ideleClassGroupEquiv_mk]`. Use `h.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RationalIdeles.integersRingEquiv (fun v ↦ (((RationalIdeles.positiveSubgroupEquiv y).2 v : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)) (Rat.HeightOneSpectrum.primesEquiv v) = _`. Conclude with `Equiv.piCongrLeft_apply_apply (P := fun p : Nat.Primes ↦ ℤ_[p]) (e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (fun v' ↦ (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v').toAlgEquiv.toRingEquiv (((RationalIdeles.positiveSubgroupEquiv y).2 v' : (v'.adicCompletio …`.
-/
theorem toPadicInt_unitPart_mk (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    toPadicInt (prime v) (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℤ̂) =
      ((unitAt y v : ℤ_[prime v]ˣ) : ℤ_[prime v]) := by
  have h := toPadicInt_unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))
    (Rat.HeightOneSpectrum.primesEquiv v)
  rw [RationalIdeles.ideleClassGroupEquiv_mk] at h
  refine h.trans ?_
  change RationalIdeles.integersRingEquiv (fun v ↦ (((RationalIdeles.positiveSubgroupEquiv y).2 v :
    (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ))
      (Rat.HeightOneSpectrum.primesEquiv v) = _
  exact Equiv.piCongrLeft_apply_apply (P := fun p : Nat.Primes ↦ ℤ_[p])
    (e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
    (fun v' ↦ (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v').toAlgEquiv.toRingEquiv
      (((RationalIdeles.positiveSubgroupEquiv y).2 v' : (v'.adicCompletionIntegers ℚ)ˣ) :
        v'.adicCompletionIntegers ℚ)) v

/- English proof (translation)
Rewrite using `[cycCharacter_spec _ (primePowPNat (prime v₀) n) hζ, cycCharacter_reciprocityMap, ← toZModPow_toPadicInt]`. Establish `h' : Units.map (toPadicInt (prime v₀)).toMonoidHom (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v₀` using `Units.ext (toPadicInt_unitPart_mk y v₀)`. Establish `h'' : toPadicInt (prime v₀) (((unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)))⁻¹ : ℤ̂ˣ) : ℤ̂) = (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])`. Rewrite using `[← h', Units.coe_map_inv]`. Both sides reduce to the same expression.

Rewrite using `[h'']`. Both sides reduce to the same expression.
-/
theorem reciprocityMap_apply_of_mem_positiveSubgroup (y : RationalIdeles.positiveSubgroup)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : maxCyclotomic} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    reciprocityMap (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) ζ =
      ζ ^ (PadicInt.toZModPow n (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val := by
  rw [cycCharacter_spec _ (primePowPNat (prime v₀) n) hζ, cycCharacter_reciprocityMap,
    ← toZModPow_toPadicInt]
  have h' : Units.map (toPadicInt (prime v₀)).toMonoidHom
      (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v₀ :=
    Units.ext (toPadicInt_unitPart_mk y v₀)
  have h'' : toPadicInt (prime v₀)
      (((unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)))⁻¹ : ℤ̂ˣ) : ℤ̂) =
        (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀]) := by
    rw [← h', Units.coe_map_inv]
    rfl
  rw [h'']
  rfl

instance (m : ℕ) [NeZero m] :
    IsMulCommutative (rootsOfUnityField m ≃ₐ[ℚ] rootsOfUnityField m) :=
  IsCyclotomicExtension.isMulCommutative {m} ℚ _

/- English proof (translation)
The claim follows from `adjoin_le_iff.2 fun _ hx ↦ subset_adjoin ℚ _ ⟨m, Nat.pos_of_neZero m, hx⟩`.
-/
theorem rootsOfUnityField_le_maxCyclotomic (m : ℕ) [NeZero m] :
    rootsOfUnityField m ≤ maxCyclotomic :=
  adjoin_le_iff.2 fun _ hx ↦ subset_adjoin ℚ _ ⟨m, Nat.pos_of_neZero m, hx⟩

/- English proof (translation)
Take `⟨⟨a, y⟩, rfl⟩` from `RationalIdeles.mulMap_bijective.2 x`. Simplify using `only [RationalIdeles.mulMap_apply] at hσ ⊢`. Establish `e : IdeleClassGroup.mk ℚ (diagonal ℚ a * (y : IdeleGroup ℚ)) = IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)`. Rewrite using `[map_mul, IdeleClassGroup.mk_diagonal]`. Conclude with `one_mul (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))`.

Rewrite `hσ` using `[e]`. Rewrite using `[map_mul, ideleSymbol_diagonal_eq_one _ {m} a, one_mul]`. Use `set L := rootsOfUnityField m`. Use `set σ₁ := ideleSymbol ℚ L (y : IdeleGroup ℚ)`. Use `set σ₂ := σ.restrictNormal L`.

Establish `key : ∀ (p k : ℕ) (hp : p.Prime) (ζ : L), ζ ^ (p ^ k) = 1 → σ₂ ζ = σ₁ ζ`. Introduce `p k hp ζ hζ`. Establish `hp' : ζ ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1` using `by rw [prime_placeOf ⟨p, hp⟩]; exact hζ`. Rewrite using `[ideleSymbol_apply_of_mem_positiveSubgroup L y _ hp']`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h1 : ((σ₂ ζ : L) : ℚ̄) = σ ζ` using `AlgEquiv.restrictNormal_commutes σ L ζ`. Establish `hmem : (ζ : ℚ̄) ∈ maxCyclotomic` using `rootsOfUnityField_le_maxCyclotomic m ζ.2`. Establish `hζ' : (⟨ζ, hmem⟩ : maxCyclotomic) ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1` using `Subtype.ext (by simpa using congrArg Subtype.val hp')`. Establish `h2` using `reciprocityMap_apply_of_mem_positiveSubgroup y (placeOf ⟨p, hp⟩) hζ'`. Rewrite `h2` using `[← hσ]`.

Establish `h3` using `congrArg Subtype.val h2`. Rewrite `h3` using `[coe_cycRestrict_apply]`. Rewrite using `[h1, h3, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]`. Use `IsCyclotomicExtension.algEquiv_eq_of_apply_eq {m} ℚ L fun n hn hn0 ↦ ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L hn hn0`.

Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Use `apply_eq_of_pow_eq_one_of_forall_prime_pow (σ₁⁻¹ * σ₂) (fun p k hp ζ hζ ↦ by` as an intermediate fact. Rewrite using `[AlgEquiv.mul_apply, key p k hp ζ hζ, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]) hn0 hr.pow_eq_one`. Rewrite `this` using `[AlgEquiv.mul_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem restrictNormal_eq_ideleSymbol (m : ℕ) [NeZero m] (x : IdeleGroup ℚ) (σ : Gal(ℚ̄/ℚ))
    (hσ : cycRestrict σ = reciprocityMap (IdeleClassGroup.mk ℚ x)) :
    σ.restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) x := by
  obtain ⟨⟨a, y⟩, rfl⟩ := RationalIdeles.mulMap_bijective.2 x
  simp only [RationalIdeles.mulMap_apply] at hσ ⊢
  have e : IdeleClassGroup.mk ℚ (diagonal ℚ a * (y : IdeleGroup ℚ)) =
      IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ) := by
    rw [map_mul, IdeleClassGroup.mk_diagonal]
    exact one_mul (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))
  rw [e] at hσ
  rw [map_mul, ideleSymbol_diagonal_eq_one _ {m} a, one_mul]
  set L := rootsOfUnityField m
  set σ₁ := ideleSymbol ℚ L (y : IdeleGroup ℚ)
  set σ₂ := σ.restrictNormal L

  have key : ∀ (p k : ℕ) (hp : p.Prime) (ζ : L), ζ ^ (p ^ k) = 1 → σ₂ ζ = σ₁ ζ := by
    intro p k hp ζ hζ
    have hp' : ζ ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1 := by rw [prime_placeOf ⟨p, hp⟩]; exact hζ
    rw [ideleSymbol_apply_of_mem_positiveSubgroup L y _ hp']
    apply Subtype.ext
    have h1 : ((σ₂ ζ : L) : ℚ̄) = σ ζ := AlgEquiv.restrictNormal_commutes σ L ζ
    have hmem : (ζ : ℚ̄) ∈ maxCyclotomic := rootsOfUnityField_le_maxCyclotomic m ζ.2
    have hζ' : (⟨ζ, hmem⟩ : maxCyclotomic) ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hp')
    have h2 := reciprocityMap_apply_of_mem_positiveSubgroup y (placeOf ⟨p, hp⟩) hζ'
    rw [← hσ] at h2
    have h3 := congrArg Subtype.val h2
    rw [coe_cycRestrict_apply] at h3
    rw [h1, h3, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
  refine IsCyclotomicExtension.algEquiv_eq_of_apply_eq {m} ℚ L fun n hn hn0 ↦ ?_
  obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L hn hn0
  refine ⟨r, hr, ?_⟩
  have := apply_eq_of_pow_eq_one_of_forall_prime_pow (σ₁⁻¹ * σ₂) (fun p k hp ζ hζ ↦ by
    rw [AlgEquiv.mul_apply, key p k hp ζ hζ, ← AlgEquiv.mul_apply, inv_mul_cancel,
      AlgEquiv.one_apply]) hn0 hr.pow_eq_one
  rw [AlgEquiv.mul_apply] at this
  calc σ₂ r = σ₁ (σ₁⁻¹ (σ₂ r)) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    _ = σ₁ r := by rw [this]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `cycRestrict_surjective (reciprocityMap (IdeleClassGroup.mk ℚ x))`. Rewrite using `[← restrictNormal_eq_ideleSymbol m x σ hσ, ← hσ, coe_cycRestrict_apply]`. Conclude with `AlgEquiv.restrictNormal_commutes σ (rootsOfUnityField m) z`.
-/
theorem coe_ideleSymbol_apply (m : ℕ) [NeZero m] (x : IdeleGroup ℚ) (z : rootsOfUnityField m) :
    ((ideleSymbol ℚ (rootsOfUnityField m) x z : rootsOfUnityField m) : ℚ̄) =
      ((reciprocityMap (IdeleClassGroup.mk ℚ x)
        ⟨z, rootsOfUnityField_le_maxCyclotomic m z.2⟩ : maxCyclotomic) : ℚ̄) := by
  obtain ⟨σ, hσ⟩ := cycRestrict_surjective (reciprocityMap (IdeleClassGroup.mk ℚ x))
  rw [← restrictNormal_eq_ideleSymbol m x σ hσ, ← hσ, coe_cycRestrict_apply]
  exact AlgEquiv.restrictNormal_commutes σ (rootsOfUnityField m) z

end RationalSymbol

end

end GroundTheory.Global
