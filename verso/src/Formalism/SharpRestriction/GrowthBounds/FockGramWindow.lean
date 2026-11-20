import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.InitialPointNumericBound
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.WinLvl
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatMin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiagRank

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

/- English proof (translation)
Introduce `Cc _`. Use `⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 h1 h2 => ⟨2, two_pos, fun CYb Cde Ck CD Cb a1 _ _ a4 a5 => ?_⟩⟩⟩` and prove the remaining obligations. Introduce `Ckap Cs CM hCM X _ hH`. Establish `hS : SegFacts C0 CE1 CE2 X` using `segFacts a1 (by linarith) (by linarith) (by linarith) (by linarith) hH`. Establish `hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ)`.

Take `⟨h0, -⟩` from `hH`. Take `⟨-, hpk, -⟩` from `h0`. Conclude with `hpk`. Conclude with `restWin_of_lvl (by linarith) (by linarith) (by linarith) hH CM winLvl (restWinNum_proved hS hpk CM hCM) (a_mem_win hS)`.
-/
theorem restWinE_proved (D : Formalism.BasicNotions.D7) : RestWinE D := by
  intro Cc _
  refine ⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 h1 h2 => ⟨2, two_pos, fun CYb Cde Ck CD Cb a1 _ _ a4 a5 => ?_⟩⟩⟩
  intro Ckap Cs CM hCM X _ hH
  have hS : SegFacts C0 CE1 CE2 X := segFacts a1 (by linarith) (by linarith) (by linarith) (by linarith) hH
  have hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ) := by
    obtain ⟨h0, -⟩ := hH
    obtain ⟨-, hpk, -⟩ := h0
    exact hpk
  exact restWin_of_lvl (by linarith) (by linarith) (by linarith) hH CM winLvl (restWinNum_proved hS hpk CM hCM)
    (a_mem_win hS)

/- English proof (translation)
The claim follows from `closed_of_minimal_vector D PI.exists_minimalNormVector diagonal_rank_bound (restWinE_proved D)`.
-/
theorem theorem_A_closed_form_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_minimal_vector D PI.exists_minimalNormVector diagonal_rank_bound (restWinE_proved D)

end Formalism.MainNotions.G.GramWindowAlt

end
