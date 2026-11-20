import Mathlib
import Formalism.PeriodIntegrals.Minkowski
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSumStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.Assemble

namespace PI.Mk

open Finset Polynomial

noncomputable def schurPoly (N ℓ m : ℕ) : ℤ[X] :=
  ∏ y ∈ range m, (X - C ((N : ℤ) - (ℓ : ℤ) * ((y + 1 : ℕ) : ℤ)))

/- English proof (translation)
Unfold `schurPoly`. Rewrite using `[eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C, sub_sub_cancel]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]`. Use `push_cast`.

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
Unfold `schurPoly`. Rewrite using `[eval_prod]`. Apply `Finset.prod_eq_zero (i := y - 1) (Finset.mem_range.2 (by omega))` to reduce the goal to its premises. Establish `: y - 1 + 1 = y` using `by omega`. Simplify using `[this]`.
-/
theorem schurPoly_eval_zero (N ℓ m y : ℕ) (h1 : y ≠ 0) (h2 : y ≤ m) :
    (schurPoly N ℓ m).eval ((N : ℤ) - (ℓ : ℤ) * (y : ℤ)) = 0 := by
  unfold schurPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := y - 1) (Finset.mem_range.2 (by omega))
  have : y - 1 + 1 = y := by omega
  simp [this]

/- English proof (translation)
Repeatedly rewrite using `[eval_eq_sum_range]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[← Finset.mul_sum]`.

Conclude with `Dvd.dvd.mul_left (hb N P k) _`.
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
Introduce `N ℓ hℓ P hfin hP`. Establish `: Fintype P` using `Fintype.ofFinite P`. Use `set m := N / (ℓ - 1) with hm`. Establish `hdvd` using `dvd_sum_eval hb N P (schurPoly N ℓ m)`. Rewrite `hdvd` using `[Finset.sum_eq_single (1 : P)]`.

Establish `h1 : Matrix.trace (((1 : P) : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ) = (N : ℤ)`. Simplify using the standard rewrite rules. Rewrite `hdvd` using `[h1, schurPoly_eval_top, Int.natCast_dvd_natCast, ← Nat.card_eq_fintype_card]`. Conclude with `hdvd`. Introduce `g _ hg`.

Take `⟨a, hga⟩` from `hP g`. Establish `hmat : ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ) ^ (ℓ ^ a) = 1`. Use `congrArg (fun x : P => ((x : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ)) hga` as an intermediate fact. Simplify using `using this`. Take `⟨y, hy, htr, hy0⟩` from `ha N ℓ a hℓ _ hmat`.

Rewrite using `[htr]`. Apply `schurPoly_eval_zero _ _ _ _ _ hy` to reduce the goal to its premises. Introduce `h0`. Apply `hg` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `using hy0 h0`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
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
The claim follows from `minkowskiBound_of (pGroupStep_of ha hb)`.
-/
theorem minkowskiBound_of_steps (ha : TraceStep) (hb : PowerSumStep) : PI.MinkowskiBound :=
  minkowskiBound_of (pGroupStep_of ha hb)

end PI.Mk
