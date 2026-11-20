import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmega
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCmConjugationOmega.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_cm_conjugation_omega : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂), ∃ c : nd.Om ≃+* nd.Om, IsCMConjOm H.E nd.Om c := by
  first | exact @GlobalTheory.MemN.exists_isCMConjOm_nData | exact GlobalTheory.MemN.exists_isCMConjOm_nData | (intros; apply GlobalTheory.MemN.exists_isCMConjOm_nData <;> assumption)
