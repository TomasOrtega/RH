import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem RestTermWellDefined.proof (h1 : LemmaA.Statement) : RestTermWellDefined.Statement := by
  intro f N F Q Q' hQ hQ' k hk1 hkN τ G hG
  obtain ⟨c, -, -, hA⟩ := h1 f N
  obtain ⟨P, hP, -, S, hS, hI⟩ := hA F Q hQ k hk1 hkN τ G hG
  obtain ⟨P', hP', -, S', hS', hI'⟩ := hA F Q' hQ' k hk1 hkN τ G hG
  have hPP : P = P' :=
    IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)) (hP.trans hP'.symm)
  have hSS : S = S' := Flag.powerSumHom_injective N (by rw [hS, hS', hPP])
  simp only [restTerm, hI, hI', hSS]

end RestTerms

end GroundTheory.Heights₂.Heights
