import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeParametersWindowEndsStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Introduce `D L C j ε n g ψ hR hO`. Take `⟨hn, hg⟩` from `hO`. Substitute `hn` using the available equality. Establish `hgl : g = letter (g 0) ψ` using `funext fun a => hg a`. Rewrite using `[hgl]`.

Establish `hb` using `GlobalTheory.HTW.bHat_window L C hR`. Use `⟨?_, ?_, hb.1, hb.2⟩` and prove the remaining obligations. Introduce `a`. Take `⟨-, hM, hh, -⟩` from `GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a`. Rewrite using `[hM, hh]`.

Conclude with `GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height L C j ε (g 0) ψ hR a`. Introduce `a hnt`. Take `⟨hsz, -, -, hth⟩` from `GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a`. Take `⟨s, hs1, hs2, -, hs3⟩` from `GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds L C j ε (g 0) ψ hR a (fun h => hnt (hth.2 h))`. Use `⟨s, hs1, le_trans hs2 (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).1, ?_⟩` and prove the remaining obligations.

Establish `hc : (((recWord L j ε (letter (g 0) ψ)).sz a : ℕ) : ℝ) = (((pageWord L j ε (g 0) ψ).sz a : ℤ) : ℝ)`. Rewrite using `[← hsz]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hc]`.

Conclude with `hs3`.
-/
theorem recWord_wordBox : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := funext fun a => hg a
  rw [hgl]
  have hb := GlobalTheory.HTW.bHat_window L C hR
  refine ⟨?_, ?_, hb.1, hb.2⟩
  · intro a
    obtain ⟨-, hM, hh, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    rw [hM, hh]
    exact GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height L C j ε (g 0) ψ hR a
  · intro a hnt
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    obtain ⟨s, hs1, hs2, -, hs3⟩ := GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds L C j ε (g 0) ψ hR a (fun h => hnt (hth.2 h))
    refine ⟨s, hs1, le_trans hs2 (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).1, ?_⟩
    have hc : (((recWord L j ε (letter (g 0) ψ)).sz a : ℕ) : ℝ) = (((pageWord L j ε (g 0) ψ).sz a : ℤ) : ℝ) := by
      rw [← hsz]; push_cast; rfl
    rw [hc]; exact hs3

end GlobalTheory.HTW.Rec
