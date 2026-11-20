import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.theta_tower_properties : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.TowerA ∧ GlobalTheory.ThK.TowerB := by
  first | exact @GlobalTheory.ThK.towerA_and_towerB | exact GlobalTheory.ThK.towerA_and_towerB | (intros; apply GlobalTheory.ThK.towerA_and_towerB <;> assumption)
