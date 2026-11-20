import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSimultaneousDiagonalisationPosDefHermitian.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G G' : Matrix ι ι ℂ), G.PosDef → G'.IsHermitian → ∃ (T : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit T.det ∧ Tᴴ * G * T = 1 ∧ Tᴴ * G' * T = Matrix.diagonal fun i => (d i : ℂ) := by
  first | exact @GlobalTheory.HSAmp.simultaneous_diagonalisation | exact GlobalTheory.HSAmp.simultaneous_diagonalisation | (intros; apply GlobalTheory.HSAmp.simultaneous_diagonalisation <;> assumption)
