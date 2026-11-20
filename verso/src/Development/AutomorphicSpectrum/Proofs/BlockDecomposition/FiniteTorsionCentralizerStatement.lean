import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizer
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteTorsionCentralizer.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.finite_torsion_centralizer_alt : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | exact GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | (intros; apply GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer <;> assumption)
