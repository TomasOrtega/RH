import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Rewrite using `[pow_succ', mul_assoc, mahlerMul n e h _ _ hq (mul_ne_zero (pow_ne_zero _ hq) hg), ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mahler_pow_mul {n e : ℕ} (h : HermNorm n) {q g : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) (hg : g ≠ 0) (a : ℕ) :
    mahler h e (q ^ a * g) = (a : ℝ) * mahler h e q + mahler h e g := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', mul_assoc, mahlerMul n e h _ _ hq (mul_ne_zero (pow_ne_zero _ hq) hg), ih]
    push_cast
    ring

/- English proof (translation)
Introduce `n e h ι s q d a c hc hq`. Use `revert hq`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `[mahler_C]`.

Introduce `i s hi ih hq`. Establish `hrest : ∀ j ∈ s, q j ≠ 0 ∧ IsMultiHomog (d j) (q j)` using `fun j hj => hq j (Finset.mem_insert_of_mem hj)`. Establish `hne : C c * ∏ j ∈ s, q j ^ a j ≠ 0` using `mul_ne_zero (by simpa using hc) (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hrest j hj).1)`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, mul_left_comm (C c) (q i ^ a i), mahler_pow_mul h (hq i (Finset.mem_insert_self i s)).1 hne (a i), ih hrest]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mahler_C_mul_prod_pow : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  classical
  intro n e h ι s q d a c hc hq
  revert hq
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [mahler_C]
  · intro i s hi ih hq
    have hrest : ∀ j ∈ s, q j ≠ 0 ∧ IsMultiHomog (d j) (q j) := fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hne : C c * ∏ j ∈ s, q j ^ a j ≠ 0 :=
      mul_ne_zero (by simpa using hc) (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hrest j hj).1)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_left_comm (C c) (q i ^ a i),
      mahler_pow_mul h (hq i (Finset.mem_insert_self i s)).1 hne (a i), ih hrest]
    ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
