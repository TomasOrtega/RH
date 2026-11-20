import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralWeightIndep
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FChernIntegralWeightIndep.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.chern_integral_weight_indep : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf | exact GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf | (intros; apply GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf <;> assumption)
