import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchroedingerOperatorHeisenbergPreservesSchwartzB.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat | exact GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat | (intros; apply GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat <;> assumption)
