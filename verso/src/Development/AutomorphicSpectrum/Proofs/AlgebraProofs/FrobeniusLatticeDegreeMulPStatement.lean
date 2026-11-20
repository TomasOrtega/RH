import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFrobeniusLatticeDegreeMulP.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.frobenius_lattice_degree_mul_p : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L → IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat <;> assumption)
