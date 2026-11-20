import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedPotentialIntegralFormulaStatement

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem anSys_proportional : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (S : AnSys D (Ψ × Fin N)), j ≤ N → D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH → ∃ v : ℝ, 0 < v ∧ toWt S.degPoly = C v * antisymDelta Ψ N := by
  intro hI Ψ _ _ N j D S hj hD hU
  obtain ⟨hO, hNull, -, -, -⟩ := anSys_open_basics D (Ψ × Fin N) S
  have hInt := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned D (Ψ × Fin N) S
  have hmain := GlobalTheory.T.uniformised_potential_integral_formula D S.X S.A Ψ N j S.open' S.th S.ph hj hD hO hNull
    (fun p => (S.sing p).1) (fun p => (S.sing p).2.1) hU (fun w => (hInt w).1)
  obtain ⟨v, hv, hEq⟩ := hmain
  refine ⟨v, hv, ?_⟩
  have hfun : (fun w : Fin D → Ψ × Fin N => mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) (fun _ => 1)) = S.degNum :=
    funext fun w => (hInt w).2
  rw [hfun] at hEq
  exact hEq

end GlobalTheory.CompanionTheory.Ar.PB
