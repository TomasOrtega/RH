import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFundamentalDomainCovers
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusFundamentalDomainCovers.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.torus_fundamental_domain_covers : ∀ {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ), (A.map Complex.im).det ≠ 0 → ∀ z : Fin g → ℂ, ∃ x ∈ Set.Icc (0 : Fl g) 1, ∃ l ∈ stdLat g, z = per A x + per A l := by
  first | exact @GlobalTheory.FundDom.fund_dom | exact GlobalTheory.FundDom.fund_dom | (intros; apply GlobalTheory.FundDom.fund_dom <;> assumption)
