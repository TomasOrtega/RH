import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportExists
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | exact GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | (intros; apply GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cuspidal_support_exists : ReciprocityTheory.Ty.Fin.St.SupportExistsAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | exact GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | (intros; apply GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll <;> assumption)
