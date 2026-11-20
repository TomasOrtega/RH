import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardBasisPolarisationPowerZeroEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.basisAlong_zero_card` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FCardBasisPolarisationPowerZeroEqOne.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.card_basis_polarisation_power_zero_eq_one : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  first | exact @GlobalTheory.basisAlong_zero_card | exact GlobalTheory.basisAlong_zero_card | (intros; apply GlobalTheory.basisAlong_zero_card <;> assumption)
