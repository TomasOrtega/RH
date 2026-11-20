import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfLevInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfChiOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Lit.Geo.ptRetr :
    PtRetr := by
  intro E _ _ _ a ha U hU Ξ r χ G n e hD q α β hα hβ g
  have hv := Pf.levInv E a ha U hU Ξ r χ hD.one hD.tw
  obtain ⟨t, ht⟩ := (retrFacts E a).1 g
  obtain ⟨s, hs⟩ := hD.tw.1
  have h1 := Pf.chiOne E a χ s hs (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g)
  rw [Pf.ptIp_eq]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hc := ((Pf.ptInv E a χ _ G _ _).2.1 (hv q α hα fun i => e (I i)) (hv q β hβ fun i => e (I i))).centre t g
  rw [← hc, ← ht, Pf.pt, h1]
  simp
