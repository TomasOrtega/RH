import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohDefs

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

/- English proof (translation)
Introduce `l _ K r σ ζ hζ`. Conclude with `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl l) σ) ζ hζ`.
-/
theorem cycKSpec : Formalism.GaloisCohomology.CycKSpec := by
  intro l _ K r σ ζ hζ
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl l) σ) ζ hζ

/- English proof (translation)
Introduce `l hl K r`. Establish `: IsSepClosure ↥K (PadicAlgCl l)` using `⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩`. Establish `hn : ((l ^ r : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ hl.out.ne_zero⟩`. Take `⟨e⟩` from `nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl l) hn`.

Use `⟨e.symm, fun g m => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl l)), (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g x = (Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)).val • x`. Introduce `x`. Rewrite using `[galRootsOfUnity_ρ_apply]`. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Rewrite using `[toMul_ofMul, toMul_nsmul]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]`. Use `cycKSpec l K r g _ ?_` and prove the remaining obligations.

Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]`. Use `Eq.trans ?_ (key _).symm` and prove the remaining obligations. Use `Eq.trans ?_ (map_nsmul e.symm _ m)` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul, ZMod.natCast_zmod_val]`.
-/
theorem gcMu : SgcMu := by
  intro l hl K r
  have : IsSepClosure ↥K (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl l) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl l)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g x =
        (Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine cycKSpec l K r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end PositivityTheory.LocalTateOrthogonality.Gcoh
