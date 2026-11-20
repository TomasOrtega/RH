import Mathlib
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField

noncomputable section

section FiniteOrder

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

/- English proof (translation)
Use `isOfFinOrder_iff_pow_eq_one.2 ⟨Nat.card (charField χ ≃ₐ[K] charField χ), Nat.card_pos, ContinuousMonoidHom.ext fun c ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousMonoidHom.pow_apply]`. Express the relevant statement in the definitionally equal form `toCircleHom (charBar χ) (reciprocityMap K (charField χ) c) ^ _ = 1`. Rewrite using `[← map_pow, pow_card_eq_one', map_one]`.
-/
theorem isOfFinOrder_heckeCharacterOfChar : IsOfFinOrder (heckeCharacterOfChar χ) := by
  refine isOfFinOrder_iff_pow_eq_one.2
    ⟨Nat.card (charField χ ≃ₐ[K] charField χ), Nat.card_pos, ContinuousMonoidHom.ext fun c ↦ ?_⟩
  rw [ContinuousMonoidHom.pow_apply]
  change toCircleHom (charBar χ) (reciprocityMap K (charField χ) c) ^ _ = 1
  rw [← map_pow, pow_card_eq_one', map_one]

end FiniteOrder

section Existence

universe u

variable {K : Type u} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `isOfFinOrder_iff_pow_eq_one.1 hψ`. Establish `hval : ∀ c, ψ c ^ n = 1` using `fun c ↦ by`. Rewrite using `[← ContinuousMonoidHom.pow_apply, hpow]`. Both sides reduce to the same expression. Use `set f : IdeleClassGroup K →* Circle := ψ.toMonoidHom with hf`.

Establish `hS : {z : Circle | z ^ n = 1}.Finite`. Use `Set.Finite.of_finite_image ?_ Circle.coe_injective.injOn` and prove the remaining obligations. Use `(Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hz' : z ^ n = 1` using `hz`.

Rewrite using `[Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, ← Circle.coe_pow, hz', Circle.coe_one]`. Establish `hopen : IsOpen (f.ker : Set (IdeleClassGroup K))`. Establish `hU : IsOpen (({z : Circle | z ^ n = 1} \ {1})ᶜ)` using `(hS.sdiff).isClosed.isOpen_compl`. Establish `hker : (f.ker : Set (IdeleClassGroup K)) = ψ ⁻¹' ({z : Circle | z ^ n = 1} \ {1})ᶜ`. Use extensionality with `c`.

Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not]`. Conclude with `⟨fun h _ ↦ h, fun h ↦ h (hval c)⟩`. Rewrite using `[hker]`. Conclude with `hU.preimage ψ.continuous`. Establish `: Finite f.range` using `(hS.subset (by rintro _ ⟨c, rfl⟩; exact hval c)).to_subtype`.

Take `⟨L, _, _, _, hab, hL⟩` from `exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex f.ker hopen`. Set `χ : Gal(L/K) →* ℂˣ` to `Circle.toUnits.comp ((QuotientGroup.lift _ f hL.le).comp (reciprocityMapEquiv K L).symm.toMonoidHom)`. Establish `hχ : ∀ c, χ (reciprocityMap K L c) = Circle.toUnits (ψ c)`. Introduce `c`. Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective K c`.

Simplify using `only [χ, MonoidHom.comp_apply, reciprocityMap_mk, MulEquiv.coe_toMonoidHom, ← reciprocityMapEquiv_mk, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective χ`. Rewrite using `[injective_iff_map_eq_one]`. Introduce `σ hσ`.

Take `⟨c, rfl⟩` from `reciprocityMap_surjective (K := K) (L := L) σ`. Rewrite `hσ` using `[hχ, ← map_one Circle.toUnits]`. Establish `hc : c ∈ f.ker` using `unitSphereToUnits_injective hσ`. Rewrite `hc` using `[← hL, ← ker_reciprocityMap]`. Conclude with `hc`.

Use `⟨L, inferInstance, inferInstance, inferInstance, hab, χ, hinj, ContinuousMonoidHom.ext fun c ↦ Circle.ext ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective K c`. Rewrite using `[heckeCharacterOfChar_apply, reciprocityMap_mk, ← restrictNormal_ideleSymbol (charField χ) L x]`. Express the relevant statement in the definitionally equal form `((charBar χ (AlgEquiv.restrictNormalHom (charField χ) (ideleSymbol K L x)) : ℂˣ) : ℂ) = _`. Rewrite using `[charBar_restrictNormalHom, ← reciprocityMap_mk, hχ]`.

Both sides reduce to the same expression.
-/
theorem exists_heckeCharacterOfChar_eq (ψ : HeckeCharacter K) (hψ : IsOfFinOrder ψ) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L)
      (χ : Gal(L/K) →* ℂˣ), Function.Injective χ ∧ heckeCharacterOfChar χ = ψ := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hψ
  have hval : ∀ c, ψ c ^ n = 1 := fun c ↦ by
    rw [← ContinuousMonoidHom.pow_apply, hpow]
    rfl
  set f : IdeleClassGroup K →* Circle := ψ.toMonoidHom with hf

  have hS : {z : Circle | z ^ n = 1}.Finite := by
    refine Set.Finite.of_finite_image ?_ Circle.coe_injective.injOn
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ^ n = 1 := hz
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, ← Circle.coe_pow, hz',
      Circle.coe_one]

  have hopen : IsOpen (f.ker : Set (IdeleClassGroup K)) := by
    have hU : IsOpen (({z : Circle | z ^ n = 1} \ {1})ᶜ) :=
      (hS.sdiff).isClosed.isOpen_compl
    have hker : (f.ker : Set (IdeleClassGroup K)) = ψ ⁻¹' ({z : Circle | z ^ n = 1} \ {1})ᶜ := by
      ext c
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not]
      exact ⟨fun h _ ↦ h, fun h ↦ h (hval c)⟩
    rw [hker]
    exact hU.preimage ψ.continuous

  have : Finite f.range :=
    (hS.subset (by rintro _ ⟨c, rfl⟩; exact hval c)).to_subtype
  obtain ⟨L, _, _, _, hab, hL⟩ :=
    exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex f.ker hopen

  let χ : Gal(L/K) →* ℂˣ := Circle.toUnits.comp
    ((QuotientGroup.lift _ f hL.le).comp (reciprocityMapEquiv K L).symm.toMonoidHom)
  have hχ : ∀ c, χ (reciprocityMap K L c) = Circle.toUnits (ψ c) := by
    intro c
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
    simp only [χ, MonoidHom.comp_apply, reciprocityMap_mk, MulEquiv.coe_toMonoidHom,
      ← reciprocityMapEquiv_mk, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
    rfl
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨c, rfl⟩ := reciprocityMap_surjective (K := K) (L := L) σ
    rw [hχ, ← map_one Circle.toUnits] at hσ
    have hc : c ∈ f.ker := unitSphereToUnits_injective hσ
    rw [← hL, ← ker_reciprocityMap] at hc
    exact hc
  refine ⟨L, inferInstance, inferInstance, inferInstance, hab, χ, hinj,
    ContinuousMonoidHom.ext fun c ↦ Circle.ext ?_⟩
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [heckeCharacterOfChar_apply, reciprocityMap_mk,
    ← restrictNormal_ideleSymbol (charField χ) L x]
  change ((charBar χ (AlgEquiv.restrictNormalHom (charField χ) (ideleSymbol K L x)) : ℂˣ) : ℂ) = _
  rw [charBar_restrictNormalHom, ← reciprocityMap_mk, hχ]
  rfl

end Existence

end

end GroundTheory.Global
