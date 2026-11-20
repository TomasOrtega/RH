import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioSameDivisorMultiplicities
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FUnitRatioSameDivisorMultiplicities.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unit_ratio_same_divisor_multiplicities : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq | exact GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq <;> assumption)
