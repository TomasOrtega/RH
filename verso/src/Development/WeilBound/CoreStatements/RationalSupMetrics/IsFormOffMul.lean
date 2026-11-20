import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem MultiProjectiveCoordinates.isFormOff_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (u v : MRing ι), IsArithVar (mCoordIdeal y) d → IsFormOff (mCoordIdeal y) u → IsFormOff (mCoordIdeal y) v → IsFormOff (mCoordIdeal y) (u * v) := by
  intro K _ ι _ Ω _ y d u v hA hu hv
  obtain ⟨⟨a, ha⟩, hu⟩ := hu
  obtain ⟨⟨b, hb⟩, hv⟩ := hv
  refine ⟨⟨_, MultiProjectiveCoordinates.Val.mh_mul ha hb⟩, fun h => ?_⟩
  exact (hA.2.1.1.mem_or_mem h).elim hu hv
