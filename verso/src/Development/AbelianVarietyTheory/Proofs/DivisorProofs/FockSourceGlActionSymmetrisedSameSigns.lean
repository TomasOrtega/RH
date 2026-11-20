import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColLie

/- English proof (translation)
Introduce `D a b τ ε ε' Y h`. Establish `hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k = (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ (MvPolynomial.pd …`. Introduce `i j k`. Establish `hjk : ε j = ε k` using `(h i j).symm.trans (h i k)`. Establish `h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1`.

Apply the tactic sequence `rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO`. Rewrite using `[if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]`. Both sides reduce to the same expression. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer`.

Simplify using `only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockS_eq_colDer_of_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  intro D a b τ ε ε' Y h
  have hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k =
      (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ
        (MvPolynomial.pderiv (τ, i, k)).toLinearMap : Module.End ℂ (PolF D b a)) := by
    intro i j k
    have hjk : ε j = ε k := (h i j).symm.trans (h i k)
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1 := by
      rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO
    rw [if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer
  simp only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  · simp only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory.ColLie
