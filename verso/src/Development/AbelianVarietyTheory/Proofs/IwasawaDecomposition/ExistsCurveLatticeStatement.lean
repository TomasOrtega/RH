import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Col2.exists_curve_lattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCurveLattice.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.exists_periodPair_lattice_eq_lamOf : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  first | exact @GlobalTheory.Mem.Col2.exists_curve_lattice | exact GlobalTheory.Mem.Col2.exists_curve_lattice | (intros; apply GlobalTheory.Mem.Col2.exists_curve_lattice <;> assumption)
