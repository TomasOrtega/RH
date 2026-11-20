import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBound
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPsi0ZeroFreeRegionBound.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.exists_norm_psi0_le_exp_sqrt_log : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < c ∧ ∀ u : ℝ, 2 ≤ u → ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log | exact GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log | (intros; apply GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log <;> assumption)
