import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

/- English proof (translation)
Introduce `D C0 hC0 h`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩` from `h`. Use `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13, h14⟩` and prove the remaining obligations. Introduce `u`. Establish `hG : 0 < (D.mem u).A.GamP` using `lt_trans one_pos (D.mem u).A.one_lt_gammaP`.

Establish `hD : 0 < D.what₂.Dstar` using `by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos`. Establish `hC : 0 < C0` using `lt_of_lt_of_le one_pos hC0`. Establish `hpos : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0` using `by positivity`. Establish `: (0 : ℝ) < (D.duS u : ℝ)` using `lt_of_lt_of_le hpos (h10 u).1`. Conclude with `this` after adjusting the coercions.
-/
theorem rowColumnShape_of_windowData_width_ge_one : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  intro D C0 hC0 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13, h14⟩
  intro u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hC : 0 < C0 := lt_of_lt_of_le one_pos hC0
  have hpos : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 := by positivity
  have : (0 : ℝ) < (D.duS u : ℝ) := lt_of_lt_of_le hpos (h10 u).1
  exact_mod_cast this

end GlobalTheory.Core.Deg
