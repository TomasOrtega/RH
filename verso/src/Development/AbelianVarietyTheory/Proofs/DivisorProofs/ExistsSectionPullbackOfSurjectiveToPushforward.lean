import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward : ∀ (X T : Scheme.{0}) (i : T ⟶ X) (M : LB X), M.IsLB → Function.Surjective ((GlobalTheory.LB.toPushforward M i).app ⊤) → ∀ σ : (M.pull i).Sec, ∃ u : M.Sec, GlobalTheory.secPull u i = σ := by
  intro X T i M _ hs σ
  obtain ⟨u', hu'⟩ := hs ((LB.globalEquiv (M.pull i)).symm σ)
  refine ⟨LB.globalEquiv M u', ?_⟩
  apply LB.f_injective
  funext j
  have key := LB.globalEquiv_pullSec_f i (LB.globalEquiv M u') j
  rw [← LB.globalEquiv_symm_apply, LinearEquiv.symm_apply_apply, ← LB.toPushforward_app, hu',
    LinearEquiv.apply_symm_apply] at key
  rw [key]
  exact chartSec_f _ _ _
