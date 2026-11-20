import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwist
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoinvariantOfLocallyConstantTwist.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.coinvariant_of_locally_constant_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (R : Finset (GL (Fin a) k)),
    Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) → IsLocallyConstant χ →
    (∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y) →
    (∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) → Φ ∈ coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | exact GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | (intros; apply GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum <;> assumption)
