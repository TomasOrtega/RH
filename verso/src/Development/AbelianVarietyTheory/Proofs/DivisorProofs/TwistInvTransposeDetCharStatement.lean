import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InvTransposeTwist.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwistInvTransposeDetChar.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.twist_inv_transpose_det_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  first | exact @GlobalTheory.InvTransposeTwist.main | exact GlobalTheory.InvTransposeTwist.main | (intros; apply GlobalTheory.InvTransposeTwist.main <;> assumption)
