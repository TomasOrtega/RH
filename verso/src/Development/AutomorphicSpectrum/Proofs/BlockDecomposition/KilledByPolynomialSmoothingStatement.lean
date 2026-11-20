import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KilledByPolynomialSmoothing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKilledByPolynomialSmoothing.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.killed_by_polynomial_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
  An.Kill r f p → An.Kill r (sm ν β f) p := by
  first | exact @GlobalTheory.CompanionTheory.Conc.kill_sm | exact GlobalTheory.CompanionTheory.Conc.kill_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.kill_sm <;> assumption)
