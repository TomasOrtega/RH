import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.StepOne
import Lemmata.PartialDerivativeDegree.PderivTdSuccLe

open Matrix MvPolynomial

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCompose

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.PartialDerivativeDegree.goal1 .. | (apply Bl.PartialDerivativeDegree.goal1 <;> assumption) | (intros; apply Bl.PartialDerivativeDegree.goal1 <;> assumption) | (apply @Bl.PartialDerivativeDegree.goal1 <;> assumption) | (intros; apply @Bl.PartialDerivativeDegree.go …`.
-/
theorem deg_pderiv_mul {σ : Type*} (i : σ) (q L : MvPolynomial σ ℂ) (hL : L.totalDegree ≤ 1) :
    (pderiv i q * L).totalDegree ≤ q.totalDegree := by
  first | exact Bl.PartialDerivativeDegree.goal1 .. | (apply Bl.PartialDerivativeDegree.goal1 <;> assumption) | (intros; apply Bl.PartialDerivativeDegree.goal1 <;> assumption) | (apply @Bl.PartialDerivativeDegree.goal1 <;> assumption) | (intros; apply @Bl.PartialDerivativeDegree.goal1 <;> assumption) | (apply @Bl.PartialDerivativeDegree.goal1 <;> first | assumption | infer_instance) | exact @Bl.PartialDerivativeDegree.goal1 σ i q L hL | exact @Bl.PartialDerivativeDegree.goal1 σ i q L | exact @Bl.PartialDerivativeDegree.goal1 σ i q | exact @Bl.PartialDerivativeDegree.goal1 σ i | exact @Bl.PartialDerivativeDegree.goal1 σ

/- English proof (translation)
The claim follows from `(totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])`.
-/
theorem deg_CX {σ : Type*} (a : ℂ) (v : σ) : (C a * X v : MvPolynomial σ ℂ).totalDegree ≤ 1 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/- English proof (translation)
Break down `i with x | x` into its components or cases. Conclude with `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => deg_CX _ _)`. Conclude with `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => deg_CX _ _)`.
-/
theorem deg_lin {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : Vr N) : (lin X i).totalDegree ≤ 1 := by
  rcases i with x | x
  · exact (totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => deg_CX _ _)
  · exact (totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => deg_CX _ _)

/- English proof (translation)
The claim follows from `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => deg_pderiv_mul i q _ (deg_lin X i))`.
-/
theorem degDP {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Vr N) ℂ) :
    (dP X q).totalDegree ≤ q.totalDegree :=
  (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => deg_pderiv_mul i q _ (deg_lin X i))

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun τ _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ ℂ).totalDegree = 0`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp`.

Establish `h2 : (∏ i, M (τ i) i).totalDegree ≤ n`. Use `(totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers.
-/
theorem deg_det {σ : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : ∀ a b, (M a b).totalDegree ≤ 1) : M.det.totalDegree ≤ n := by
  rw [Matrix.det_apply']
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun τ _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ ℂ).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp
  have h2 : (∏ i, M (τ i) i).totalDegree ≤ n := by
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (M (τ i) i).totalDegree ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => hM _ _
      _ = n := by simp
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨deg_det _ fun a b => by simp [zP, totalDegree_X], deg_det _ fun a b => by simp [zPb, totalDegree_X]⟩`.
-/
theorem degD (k j ρ : ℕ) : (qD k j ρ).totalDegree ≤ j ∧ (qDb k j ρ).totalDegree ≤ j :=
  ⟨deg_det _ fun a b => by simp [zP, totalDegree_X], deg_det _ fun a b => by simp [zPb, totalDegree_X]⟩

end PI.UnitaryGroupMassFormula.UsCompose
