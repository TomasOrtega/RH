import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRestrictedFormNonzeroOnGenericPoint.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.restricted_form_nonzero_on_generic_point : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | exact GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | (intros; apply GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal <;> assumption)
