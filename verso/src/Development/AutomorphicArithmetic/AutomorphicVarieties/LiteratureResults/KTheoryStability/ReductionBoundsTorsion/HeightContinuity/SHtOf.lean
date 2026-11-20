import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.ContinuousHt

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem PositivityTheory.KB.sHt_of : PositivityTheory.KB.SHt := by
  intro L _ _ hL N hN
  exact ⟨PositivityTheory.KB.HeightDistance.continuous_ht hN, PositivityTheory.KB.HeightDistance.ht_emb, PositivityTheory.KB.HeightDistance.ht_lower hN,
    PositivityTheory.KB.HeightDistance.ht_compact hN⟩
