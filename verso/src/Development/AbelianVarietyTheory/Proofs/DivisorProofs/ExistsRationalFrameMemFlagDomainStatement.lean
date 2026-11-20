import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomain
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OrthoFrame.exists_frm_mem_dom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRationalFrameMemFlagDomain.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.exists_rational_frame_mem_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.exists_frm_mem_dom | exact GlobalTheory.OrthoFrame.exists_frm_mem_dom | (intros; apply GlobalTheory.OrthoFrame.exists_frm_mem_dom <;> assumption)
