import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteGenericFibreClosureInterResidueCharFibre.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  first | exact @GlobalTheory.GenFibClosure.finite_closure_inter_fib | exact GlobalTheory.GenFibClosure.finite_closure_inter_fib | (intros; apply GlobalTheory.GenFibClosure.finite_closure_inter_fib <;> assumption)
