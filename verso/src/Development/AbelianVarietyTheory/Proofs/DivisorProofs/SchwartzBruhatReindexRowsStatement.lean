import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemNsp
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzBruhatReindexRows.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.schwartzBruhat_reindex_rows : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) (e : A ≃ A'), (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧ (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν, (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  first | exact @GlobalTheory.RankStrata.rowRenum_SB_Nsp | exact GlobalTheory.RankStrata.rowRenum_SB_Nsp | (intros; apply GlobalTheory.RankStrata.rowRenum_SB_Nsp <;> assumption)
