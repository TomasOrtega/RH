import Mathlib
import Formalism.PeriodIntegrals.Minkowski
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSumStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.Assemble

namespace PI.Mk

open Finset Polynomial

noncomputable def schurPoly (N ℓ m : ℕ) : ℤ[X] :=
  ∏ y ∈ range m, (X - C ((N : ℤ) - (ℓ : ℤ) * ((y + 1 : ℕ) : ℤ)))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem schurPoly_eval_top (N ℓ m : ℕ) :
    (schurPoly N ℓ m).eval (N : ℤ) = ((ℓ ^ m * m.factorial : ℕ) : ℤ) := by
  unfold schurPoly
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_sub_cancel]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]
  push_cast
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem schurPoly_eval_zero (N ℓ m y : ℕ) (h1 : y ≠ 0) (h2 : y ≤ m) :
    (schurPoly N ℓ m).eval ((N : ℤ) - (ℓ : ℤ) * (y : ℤ)) = 0 := by
  unfold schurPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := y - 1) (Finset.mem_range.2 (by omega))
  have : y - 1 + 1 = y := by omega
  simp [this]

/- English proof (translation)
Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem dvd_sum_eval (hb : PowerSumStep) (N : ℕ)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (f : ℤ[X]) :
    (Fintype.card P : ℤ) ∣ ∑ g : P, f.eval (Matrix.trace
      ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ)) := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro k _
  rw [← Finset.mul_sum]
  exact Dvd.dvd.mul_left (hb N P k) _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem pGroupStep_of (ha : TraceStep) (hb : PowerSumStep) : PGroupStep := by
  intro N ℓ hℓ P hfin hP
  have : Fintype P := Fintype.ofFinite P
  set m := N / (ℓ - 1) with hm
  have hdvd := dvd_sum_eval hb N P (schurPoly N ℓ m)
  rw [Finset.sum_eq_single (1 : P)] at hdvd
  · have h1 : Matrix.trace (((1 : P) : Matrix.GeneralLinearGroup (Fin N) ℤ) :
        Matrix (Fin N) (Fin N) ℤ) = (N : ℤ) := by
      simp
    rw [h1, schurPoly_eval_top, Int.natCast_dvd_natCast, ← Nat.card_eq_fintype_card] at hdvd
    exact hdvd
  · intro g _ hg
    obtain ⟨a, hga⟩ := hP g
    have hmat : ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ) ^ (ℓ ^ a)
        = 1 := by
      have := congrArg (fun x : P => ((x : Matrix.GeneralLinearGroup (Fin N) ℤ) :
        Matrix (Fin N) (Fin N) ℤ)) hga
      simpa using this
    obtain ⟨y, hy, htr, hy0⟩ := ha N ℓ a hℓ _ hmat
    rw [htr]
    apply schurPoly_eval_zero _ _ _ _ _ hy
    intro h0
    apply hg
    apply Subtype.ext
    apply Units.ext
    simpa using hy0 h0
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem minkowskiBound_of_steps (ha : TraceStep) (hb : PowerSumStep) : PI.MinkowskiBound :=
  minkowskiBound_of (pGroupStep_of ha hb)

end PI.Mk
