import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.HermitianCurvature.BesselNonvanishingReduction

namespace PI.WBL.NIS

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem schurH : Formalism.FourierDecayAlt.ThreeDimData.SchurH := by
  intro k r ε lam H _ _ _ σ μG _ hσ hμ
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨d, hd⟩ := Formalism.MainNotions.SchurRelationsDiscreteSeries.fdeg_exists (ε := ε) (lam := lam)
    (σ := fun g => σ (P⁻¹ * g * P)) hDS
  exact Formalism.MainNotions.SchurRelationsDiscreteSeries.schur_hpk (σ := σ) (P := P) hP hd hμ

end PI.WBL.NIS
