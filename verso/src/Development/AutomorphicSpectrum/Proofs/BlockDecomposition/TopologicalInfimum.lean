import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue.Gl0

/- English proof (translation)
Introduce `E _ _ _ τ`. Use `⟨rfl, fun u φ _ => ?_⟩` and prove the remaining obligations. Simplify using `[cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]`.
-/
theorem topInf : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  intro E _ _ _ τ
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

end GlobalTheory.CompanionTheory.EGlue.Gl0

end
