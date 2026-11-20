import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSplitFinite

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finite_resChar_eq (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) :
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | Formalism.MainNotions.S.Loc.resChar p = l}.Finite := by
  have hx : ((l : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hI : Ideal.span {((l : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold Formalism.MainNotions.S.Loc.resChar at hp
  rw [← hp]
  exact ringChar.Nat.cast_ringChar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Both sides reduce to the same expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.

A detailed English derivation is pending.
-/
theorem split_finite : ∀ (D : D7) (Z : LocDat D), {p : PlF D | (Z.M p).split ≠ none}.Finite := by
  intro D Z
  have h0 := finite_resChar_eq D.host.F (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := finite_resChar_eq D.host.F (D.host.g 1) (D.host.g_prime 1).ne_zero
  refine (h0.union h1).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    have ha := (Z.agree p).2.2.2.2.2
    revert ha
    cases h : (Z.M p).split with
    | none => exact absurd h hp
    | some g =>
      cases h' : (D.s.atP p).split with
      | none => intro ha; exact ha.elim
      | some sg => intro _; rfl
  have hm := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr hm

end GlobalTheory.LocSplitFinite
