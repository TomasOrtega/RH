import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSetFibreFiniteOfGoodProj.lean&line=376#L376)
-/
theorem _root_.GlobalTheory.T.setFibre_finite_of_goodProj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite <;> assumption)
