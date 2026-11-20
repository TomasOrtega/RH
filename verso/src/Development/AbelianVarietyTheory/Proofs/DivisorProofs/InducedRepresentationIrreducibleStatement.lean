import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInducedRepresentationIrreducible.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.induced_representation_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ), IsSmU α → IsSmU β →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ f ∈ N, ∀ x, (fun h => f (h * x)) ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β := by
  first | exact @GlobalTheory.KSplit.indSp_irreducible | exact GlobalTheory.KSplit.indSp_irreducible | (intros; apply GlobalTheory.KSplit.indSp_irreducible <;> assumption)
