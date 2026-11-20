import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull
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
Apply `GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FZeroLocusRegularFunctionNull.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.zero_locus_regular_function_null : ∀ (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℤ) (σ : ℤ →+* ℂ) (D : ℕ) (c : GlobalTheory.AlgChart q σ D) (W : X.Opens)
    (h : genericPoint X ∈ W) (g : Γ(X, W)), fnOf W h g ≠ 0 →
    volume (c.e.target ∩ c.e.symm ⁻¹' {y | y ∈ ptsIn q σ W ∧ ev q σ W g y = 0}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf | exact GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf | (intros; apply GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf <;> assumption)
