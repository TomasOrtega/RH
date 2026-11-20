import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTotalDegreeLeOfMemDualWeylLattice.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  first | exact @GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | exact GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | (intros; apply GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl <;> assumption)
