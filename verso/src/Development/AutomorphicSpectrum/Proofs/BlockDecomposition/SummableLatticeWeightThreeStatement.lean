import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableLatticeWeightThree
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSummableLatticeWeightThree.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.summable_lattice_weight_three : ∀ M : ℕ, 0 < M → Summable (fun p : ℚ × ℚ × ℚ => if ((M : ℚ) * p.1).den = 1 ∧ ((M : ℚ) * p.2.1).den = 1 ∧ ((M : ℚ) * p.2.2).den = 1 then ((1 + |(p.1 : ℝ)| + |(p.2.1 : ℝ)|) ^ 3 * (1 + |(p.2.2 : ℝ)|) ^ 2)⁻¹ else (0 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.MajSum.summable_lattice_majorant | exact GlobalTheory.CompanionTheory.MajSum.summable_lattice_majorant | (intros; apply GlobalTheory.CompanionTheory.MajSum.summable_lattice_majorant <;> assumption)
