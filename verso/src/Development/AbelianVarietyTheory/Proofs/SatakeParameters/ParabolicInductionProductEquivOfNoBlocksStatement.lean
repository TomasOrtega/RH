import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocks
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FParabolicInductionProductEquivOfNoBlocks.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α'] [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)] (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)), Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  first | exact @GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | exact GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | (intros; apply GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty <;> assumption)
