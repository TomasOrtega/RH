import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomCompleteDVRPrincipalMaximalIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrInjectiveLocal
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalHomCompleteDVRPrincipalMaximalIdeal.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_localHom_completeDVR_principal_maximalIdeal : ∀ (B : Type) [CommRing B] [IsLocalRing B] (ϖ : B), maximalIdeal B = Ideal.span {ϖ} → ϖ ∈ nonZeroDivisors B → CharZero (ResidueField B) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (h : B →+* W), GlobalTheory.LN.CDvr W ∧ IsLocalHom h ∧ h ϖ ≠ 0 := by
  first | exact @GlobalTheory.PrincDvr.exists_cDvr_localHom | exact GlobalTheory.PrincDvr.exists_cDvr_localHom | (intros; apply GlobalTheory.PrincDvr.exists_cDvr_localHom <;> assumption)
