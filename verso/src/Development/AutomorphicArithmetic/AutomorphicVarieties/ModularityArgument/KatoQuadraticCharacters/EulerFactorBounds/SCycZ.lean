import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Introduce `Ω _ _ _ l _ r s`. Establish `hl : l.Prime` using `Fact.out`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩`.

Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩ infer_instance`. Establish `hval : ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = PadicInt.toZModPow r (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l])` using `rfl`. Establish `hspec : ∀ z : Ω, z ^ (l ^ r) = 1 → s z = z ^ ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val`. Introduce `z hz`. Rewrite using `[hval]`.

Conclude with `cyclotomicCharacter.spec l s.toRingEquiv z hz`. Establish `hM` using `cycM_spec (l ^ r) s ⟨_, hspec⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)`. Establish `heq : ReciprocityTheory.Gal.cycMod ℚ Ω l r s = cycM (l ^ r) s`. Apply `Units.ext` to reduce the goal to its premises.

Apply `ZMod.val_injective` to reduce the goal to its premises. Conclude with `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hspec ζ hζ.pow_eq_one).symm.trans (hM ζ hζ.pow_eq_one))`. Use `⟨heq, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, ← heq, hval, sub_self]`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sCycZ :
    UpperTheory.V.Z.Kato.Nb.SCycZ := by
  intro Ω _ _ _ l _ r s
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hval : ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
      PadicInt.toZModPow r (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := rfl
  have hspec : ∀ z : Ω, z ^ (l ^ r) = 1 →
      s z = z ^ ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro z hz
    rw [hval]
    exact cyclotomicCharacter.spec l s.toRingEquiv z hz
  have hM := cycM_spec (l ^ r) s ⟨_, hspec⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have heq : ReciprocityTheory.Gal.cycMod ℚ Ω l r s = cycM (l ^ r) s := by
    apply Units.ext
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      ((hspec ζ hζ.pow_eq_one).symm.trans (hM ζ hζ.pow_eq_one))
  refine ⟨heq, ?_⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, ← heq, hval, sub_self]
