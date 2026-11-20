import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupport
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEulerCharZeroDimSupport.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.euler_char_zero_dim_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K X) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support | exact GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support <;> assumption)
