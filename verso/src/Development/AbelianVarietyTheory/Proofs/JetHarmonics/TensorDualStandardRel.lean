import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ n E Et Om hE hsym hEt hOm`. Establish `hE' : ∀ a b c d (v : V), E a b (E c d v) - E c d (E a b v) = (if b = c then E a d v else 0) - if d = a then E c b v else 0`. Introduce `a b c d v`. Use `congrArg (fun T : Module.End ℂ V => T v) (hE a b c d)` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at this`.

Apply the tactic sequence `rw [this]; split_ifs <;> simp`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b c d`. Use extensionality with `y e`. Establish `key : E a b (E c d (y.ofLp e)) = E c d (E a b (y.ofLp e)) + ((if b = c then E a d (y.ofLp e) else 0) - if d = a then E c b (y.ofLp e) else 0)`.

Establish `h` using `hE' a b c d (y.ofLp e)`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws. Apply the tactic sequence `have hR : (((if b = c then Et a d else 0) - if d = a then Et c b else 0) y).ofLp e = (if b = c then (Et a d y).ofLp e else 0) - (if d = a then (Et c b y).ofLp e else 0) := by split_ifs <;> simp`.

Rewrite using `[hR]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply]`. Rewrite using `[WithLp.ofLp_sub, Pi.sub_apply, hEt, hEt, hEt, hEt, hEt, hEt, map_sub, map_sub, key]`. Apply the tactic sequence `split_ifs <;> simp only [hEt, map_zero, sub_zero, zero_sub] <;> subst_vars <;> first | abel1 | (exfalso; tauto) | (simp_all; done) | (split_ifs <;> subst_vars <;> first | abel1 | (exfalso; tauto) | (simp_all; done) | (simp_all; abel1))`. Introduce `a b x y`.

Simplify using `only [PiLp.inner_apply, hEt, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, hsym]`. Establish `h1 : ∀ i, inner ℂ (if i = b then x.ofLp a else 0) (y.ofLp i) = if i = b then inner ℂ (x.ofLp a) (y.ofLp b) else 0`. Apply the tactic sequence `intro i; split_ifs with h <;> simp [h]`. Establish `h2 : ∀ i, inner ℂ (x.ofLp i) (if i = a then y.ofLp b else 0) = if i = a then inner ℂ (x.ofLp a) (y.ofLp b) else 0`. Apply the tactic sequence `intro i; split_ifs with h <;> simp [h]`.

Simplify using `only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Introduce `x y`. Simplify using `only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hsym]`. Conclude with `Finset.sum_comm`. Introduce `a b`.

Use extensionality with `y e`. Simplify using `only [Module.End.mul_apply, hOm, hEt, map_sub, map_sum]`. Establish `key : ∀ i, E e i (E a b (y.ofLp i)) = E a b (E e i (y.ofLp i)) + (if i = a then E e b (y.ofLp i) else 0) - (if b = e then E a i (y.ofLp i) else 0)`. Introduce `i`. Establish `h` using `hE' e i a b (y.ofLp i)`.

Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws. Establish `h3 : ∀ i, E e i (if i = b then y.ofLp a else 0) = if i = b then E e b (y.ofLp a) else 0`. Apply the tactic sequence `intro i; split_ifs with h <;> simp [h]`.

Simplify using `only [key, h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Distinguish the cases in `h : e = b`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Normalize the expressions using the abelian group laws.

Simplify using `only [h, Ne.symm h, if_false, Finset.sum_const_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem _root_.GlobalTheory.tensor_dual_standard_rel : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), _root_.Formalism.REAL.GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → _root_.Formalism.REAL.GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hsym hEt hOm
  have hE' : ∀ a b c d (v : V), E a b (E c d v) - E c d (E a b v) = (if b = c then E a d v else 0) - if d = a then E c b v else 0 := by
    intro a b c d v
    have := congrArg (fun T : Module.End ℂ V => T v) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [this]; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    ext y e
    have key : E a b (E c d (y.ofLp e)) = E c d (E a b (y.ofLp e)) + ((if b = c then E a d (y.ofLp e) else 0) - if d = a then E c b (y.ofLp e) else 0) := by
      have h := hE' a b c d (y.ofLp e); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have hR : (((if b = c then Et a d else 0) - if d = a then Et c b else 0) y).ofLp e = (if b = c then (Et a d y).ofLp e else 0) - (if d = a then (Et c b y).ofLp e else 0) := by
      split_ifs <;> simp
    rw [hR]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [WithLp.ofLp_sub, Pi.sub_apply, hEt, hEt, hEt, hEt, hEt, hEt, map_sub, map_sub, key]
    split_ifs <;> simp only [hEt, map_zero, sub_zero, zero_sub] <;> subst_vars <;>
      first | abel1 | (exfalso; tauto) | (simp_all; done) | (split_ifs <;> subst_vars <;> first | abel1 | (exfalso; tauto) | (simp_all; done) | (simp_all; abel1))
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, hsym]
    have h1 : ∀ i, inner ℂ (if i = b then x.ofLp a else 0) (y.ofLp i) = if i = b then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    have h2 : ∀ i, inner ℂ (x.ofLp i) (if i = a then y.ofLp b else 0) = if i = a then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hsym]
    exact Finset.sum_comm
  · intro a b
    ext y e
    simp only [Module.End.mul_apply, hOm, hEt, map_sub, map_sum]
    have key : ∀ i, E e i (E a b (y.ofLp i)) = E a b (E e i (y.ofLp i)) + (if i = a then E e b (y.ofLp i) else 0) - (if b = e then E a i (y.ofLp i) else 0) := by
      intro i; have h := hE' e i a b (y.ofLp i); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have h3 : ∀ i, E e i (if i = b then y.ofLp a else 0) = if i = b then E e b (y.ofLp a) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [key, h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : e = b
    · subst h; simp only [if_true]; abel
    · simp only [h, Ne.symm h, if_false, Finset.sum_const_zero]; abel

end GlobalTheory
