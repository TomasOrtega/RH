import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSplitFinite

/- English proof (translation)
Establish `hx : ((l : 𝓞 F)) ≠ 0` using `Nat.cast_ne_zero.2 hl`. Establish `hI : Ideal.span {((l : 𝓞 F))} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hx`. Use `(Ideal.finite_factors hI).subset ?_` and prove the remaining obligations.

Introduce `p hp`. Simplify using `only [Set.mem_setOf_eq] at hp ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Unfold `Formalism.MainNotions.S.Loc.resChar at hp`.

Rewrite using `[← hp]`. Conclude with `ringChar.Nat.cast_ringChar`.
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
Introduce `D Z`. Establish `h0` using `finite_resChar_eq D.host.F (D.host.g 0) (D.host.g_prime 0).ne_zero`. Establish `h1` using `finite_resChar_eq D.host.F (D.host.g 1) (D.host.g_prime 1).ne_zero`. Use `(h0.union h1).subset ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Set.mem_setOf_eq] at hp`. Establish `hs : (D.s.atP p).split.isSome`. Establish `ha` using `(Z.agree p).2.2.2.2.2`. Use `revert ha`. Consider the cases of `h : (Z.M p).split with`.

Consider the case `none => exact absurd h hp`. Consider the case `some g`. Consider the cases of `h' : (D.s.atP p).split with`. Consider the case `none => intro ha`. Conclude with `ha.elim`.

Consider the case `some sg => intro _`. Both sides reduce to the same expression. Establish `hm` using `(D.s_split p).1 hs`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hm`. Break down `hm with hm | hm` into its components or cases.

Conclude with `Or.inl hm`. Conclude with `Or.inr hm`.
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
