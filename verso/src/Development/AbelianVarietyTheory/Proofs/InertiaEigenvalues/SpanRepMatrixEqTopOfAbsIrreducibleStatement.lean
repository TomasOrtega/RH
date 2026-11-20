import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSpanRepMatrixEqTopOfAbsIrreducible.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_absIrreducible : ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub <;> assumption)
