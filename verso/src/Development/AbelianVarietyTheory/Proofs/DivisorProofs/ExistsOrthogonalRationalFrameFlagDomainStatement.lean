import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomain
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOrthogonalRationalFrameFlagDomain.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E), GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E, (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | exact GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | (intros; apply GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm <;> assumption)
