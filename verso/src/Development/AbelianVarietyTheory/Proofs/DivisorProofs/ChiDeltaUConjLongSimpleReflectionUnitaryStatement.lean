import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChiDeltaUConjLongSimpleReflectionUnitary.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.chiDeltaU_conj_longSimpleReflection_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  first | exact @GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | exact GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | (intros; apply GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long <;> assumption)
