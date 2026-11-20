import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ReductionToDirichletCharAnyLevelOfLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Introduce `E _ _ _ N _ H hH l _ hl2 c _ Ω' _ _ _ D Ω _ _ _ e he T hT`. Use `haveI : NeZero (Nat.totient N) := ⟨(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'⟩`. Use `haveI : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by`. Use `HasEnoughRootsOfUnity.of_dvd c.O (n := Nat.totient N) ?_` and prove the remaining obligations. Use `Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => ?_)` and prove the remaining obligations.

Proceed by induction on `g using QuotientGroup.induction_on with`. Consider the case `H x => rw [← QuotientGroup.mk_pow, ZMod.pow_totient, QuotientGroup.mk_one]`. Establish `hfr` using `(Chr.levGal E N H hH).2.1`. Establish `key` using `(Chr.reduction_to_dirichletChar_any_level_of_le E c.O D Ω hH hl2 he T (N' := N) (NeZero.ne N)).1 hT`. Rewrite `key` using `[hfr]`.

Conclude with `key`.
-/
theorem UpperTheory.V.HV.redAll :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), Chr.HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
      ∀ (c : Coef l) [HasEnoughRootsOfUnity c.O (Nat.totient N)] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
        (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), e ≠ 0 → ∀ T : Finset (DirichletCharacter c.O N), (T : Set _) = Chr.evenSet c.O H e →
        plusLen D e * eO l c.O ≤ ∑ ψ ∈ T, (Vlen Ω c e ψ + (lossAll l N H.index e : ℕ∞) * eO l c.O) := by
  intro E _ _ _ N _ H hH l _ hl2 c _ Ω' _ _ _ D Ω _ _ _ e he T hT
  haveI : NeZero (Nat.totient N) := ⟨(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'⟩
  haveI : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by
    refine HasEnoughRootsOfUnity.of_dvd c.O (n := Nat.totient N) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => ?_)
    induction g using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, ZMod.pow_totient, QuotientGroup.mk_one]
  have hfr := (Chr.levGal E N H hH).2.1
  have key := (Chr.reduction_to_dirichletChar_any_level_of_le E c.O D Ω hH hl2 he T (N' := N) (NeZero.ne N)).1 hT
  rw [hfr] at key
  exact key
