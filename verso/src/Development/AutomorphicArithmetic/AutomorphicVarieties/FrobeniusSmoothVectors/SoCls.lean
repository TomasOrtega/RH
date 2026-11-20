import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `(Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s _ (fun ζ hζ => ?_)` and prove the remaining obligations. Conclude with `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ`.
-/
private theorem so_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) :
    Chr.cls ℚ Ω (l ^ 1) s = cycMod ℚ Ω l 1 s := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s _ (fun ζ hζ => ?_)
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ

/- English proof (translation)
Introduce `Ω _ _ _ l _ O _ _ _`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩`. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `h1 : cycMod ℚ Ω l 1 s = 1`.

Rewrite using `[← so_cls]`. Use `(Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s 1 (fun ζ hζ => ?_)` and prove the remaining obligations. Rewrite `hζ` using `[pow_one]`. Rewrite using `[hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]`. Simplify using `only [omO, GC.cycF, MonoidHom.comp_apply, h1, map_one]`.

Establish `h1 : cycMod ℚ Ω l 1 σ = -1`. Rewrite using `[← so_cls]`. Conclude with `(Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ`. Simplify using `only [omO, GC.cycF, MonoidHom.comp_apply, h1]`. Use `ext`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Fr.sc_om :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l], Af.KillsMu l (omO Ω l O) ∧ ∀ σ : G ℚ Ω, IsCC σ → omO Ω l O σ = -1 := by
  intro Ω _ _ _ l _ O _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycMod ℚ Ω l 1 s = 1 := by
      rw [← so_cls]
      refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s 1 (fun ζ hζ => ?_)
      rw [pow_one] at hζ
      rw [hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1, map_one]
  · have h1 : cycMod ℚ Ω l 1 σ = -1 := by
      rw [← so_cls]
      exact (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1]
    ext
    simp
