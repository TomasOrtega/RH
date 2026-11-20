import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih]`. Establish `h` using `(Commute.one_right D).add_pow n`.

Simplify using `only [one_pow, mul_one] at h`. Rewrite using `[h]`. Repeatedly rewrite using `[Nat.choose_succ_succ', add_smul]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_range_succ (fun j => n.choose (j + 1) • D ^ j) n, Nat.choose_succ_self, zero_smul, add_zero, add_comm]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul, Nat.cast_comm]`.
-/
theorem geom_sum_add_one_eq_sum_choose {R : Type*} [Ring R] (D : R) (n : ℕ) :
    ∑ i ∈ Finset.range n, (D + 1) ^ i = ∑ j ∈ Finset.range n, n.choose (j + 1) • D ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := (Commute.one_right D).add_pow n
    simp only [one_pow, mul_one] at h
    rw [h]
    simp_rw [Nat.choose_succ_succ', add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun j => n.choose (j + 1) • D ^ j) n,
      Nat.choose_succ_self, zero_smul, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul, Nat.cast_comm]

/- English proof (translation)
Introduce `x hx`. Use `set M := max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ with hM`. Establish `hpowS : ∀ (i : ℕ), ∀ y ∈ S, (σ ^ i) y ∈ S`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ i ih => intro y hy`. Rewrite using `[pow_succ', AlgEquiv.mul_apply]`. Conclude with `hS _ (ih y hy)`.

Set `T : AddMonoid.End (Om l)` to `AddMonoidHom.mk' (fun y => σ y) (fun a b => map_add σ a b)`. Establish `hT : ∀ (i : ℕ) (y : Om l), (T ^ i) y = (σ ^ i) y`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro y`.

Both sides reduce to the same expression. Consider the case `succ i ih => intro y`. Rewrite using `[pow_succ', pow_succ', AlgEquiv.mul_apply, ← ih]`. Both sides reduce to the same expression. Establish `hD : ∀ (j : ℕ), ∀ y ∈ S, ((T - 1) ^ j) y ∈ S ∧ ‖((T - 1) ^ j) y‖ ≤ s ^ j * ‖y‖`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro y hy; rw [pow_zero]; exact ⟨hy, by rw [pow_zero, one_mul]; exact le_rfl⟩`. Consider the case `succ j ih`. Introduce `y hy`.

Take `⟨h1, h2⟩` from `ih y hy`. Rewrite using `[pow_succ']`. Express the relevant statement in the definitionally equal form `σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y ∈ S ∧ ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s ^ (j + 1) * ‖y‖`. Use `⟨S.sub_mem (hS _ h1) h1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hnat : ∀ n : ℕ, ‖((n : ℕ) : Om l)‖ ≤ 1`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Nat.cast_succ]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih norm_one.le)`. Establish `key` using `geom_sum_add_one_eq_sum_choose (T - 1) l`. Rewrite `key` using `[sub_add_cancel]`. Establish `hsum : ∑ i ∈ Finset.range l, (σ ^ i) x = ∑ j ∈ Finset.range l, l.choose (j + 1) • ((T - 1) ^ j) x`.

Set `ev : AddMonoid.End (Om l) →+ Om l` to `{ toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Establish `h` using `congrArg ev key`. Simplify using `only [map_sum, map_nsmul] at h`. Combine the equalities or inequalities in the displayed calculation. Establish `hbound : ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ M * ‖x‖`.

Rewrite using `[hsum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg (le_max_of_le_right (norm_nonneg _)) (norm_nonneg _)) fun j hj => ?_` and prove the remaining obligations. Take `⟨-, hle⟩` from `hD j x hx`. Establish `hsj : s ^ j ≤ 1` using `pow_le_one₀ hs0 hs1`. Rewrite using `[nsmul_eq_mul, norm_mul]`.

Break down `Nat.lt_or_ge (j + 1) l with hlt | hge` into its components or cases. Take `⟨m, hm⟩` from `(Fact.out : l.Prime).dvd_choose_self (Nat.succ_ne_zero j) hlt`. Rewrite using `[hm, Nat.cast_mul, norm_mul]`. Establish `h3 : ‖((T - 1) ^ j) x‖ ≤ 1 * ‖x‖` using `hle.trans (mul_le_mul_of_nonneg_right hsj (norm_nonneg _))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_one, one_mul]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)`. Establish `hjl : j = l - 1` using `by have := Finset.mem_range.mp hj; omega`. Establish `hc : l.choose (j + 1) = 1`. Rewrite using `[show j + 1 = l by have := Finset.mem_range.mp hj; omega, Nat.choose_self]`.

Rewrite using `[hc, Nat.cast_one, norm_one, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hjl]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)`. Use `set y := ∑ i ∈ Finset.range l, (σ ^ i) x with hy`.

Establish `hyS : y ∈ S` using `S.sum_mem fun i _ => hpowS i x hx`. Establish `htel : (σ ^ l) x - x = σ y - y`. Rewrite using `[hy, map_sum, ← Finset.sum_sub_distrib]`. Establish `h` using `Finset.sum_range_sub (fun i => (σ ^ i) x) l`. Simplify using `only [pow_zero, AlgEquiv.one_apply] at h`.

Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ', AlgEquiv.mul_apply]`. Use `⟨hbound, ?_⟩` and prove the remaining obligations. Rewrite using `[htel]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_geom_sum_galois_le (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) :
    ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧
      ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  intro x hx
  set M := max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ with hM

  have hpowS : ∀ (i : ℕ), ∀ y ∈ S, (σ ^ i) y ∈ S := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih => intro y hy; rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ (ih y hy)

  let T : AddMonoid.End (Om l) := AddMonoidHom.mk' (fun y => σ y) (fun a b => map_add σ a b)
  have hT : ∀ (i : ℕ) (y : Om l), (T ^ i) y = (σ ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [pow_succ', pow_succ', AlgEquiv.mul_apply, ← ih]; rfl
  have hD : ∀ (j : ℕ), ∀ y ∈ S, ((T - 1) ^ j) y ∈ S ∧ ‖((T - 1) ^ j) y‖ ≤ s ^ j * ‖y‖ := by
    intro j
    induction j with
    | zero => intro y hy; rw [pow_zero]; exact ⟨hy, by rw [pow_zero, one_mul]; exact le_rfl⟩
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      rw [pow_succ']
      change σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y ∈ S ∧
        ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s ^ (j + 1) * ‖y‖
      refine ⟨S.sub_mem (hS _ h1) h1, ?_⟩
      calc ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s * ‖((T - 1) ^ j) y‖ := hσ _ h1
        _ ≤ s * (s ^ j * ‖y‖) := mul_le_mul_of_nonneg_left h2 hs0
        _ = s ^ (j + 1) * ‖y‖ := by ring

  have hnat : ∀ n : ℕ, ‖((n : ℕ) : Om l)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih norm_one.le)

  have key := geom_sum_add_one_eq_sum_choose (T - 1) l
  rw [sub_add_cancel] at key
  have hsum : ∑ i ∈ Finset.range l, (σ ^ i) x =
      ∑ j ∈ Finset.range l, l.choose (j + 1) • ((T - 1) ^ j) x := by
    let ev : AddMonoid.End (Om l) →+ Om l :=
      { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev key
    simp only [map_sum, map_nsmul] at h
    calc ∑ i ∈ Finset.range l, (σ ^ i) x = ∑ i ∈ Finset.range l, (T ^ i) x :=
          Finset.sum_congr rfl fun i _ => (hT i x).symm
      _ = _ := h
  have hbound : ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ M * ‖x‖ := by
    rw [hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (le_max_of_le_right (norm_nonneg _)) (norm_nonneg _)) fun j hj => ?_
    obtain ⟨-, hle⟩ := hD j x hx
    have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0 hs1
    rw [nsmul_eq_mul, norm_mul]
    rcases Nat.lt_or_ge (j + 1) l with hlt | hge
    ·
      obtain ⟨m, hm⟩ := (Fact.out : l.Prime).dvd_choose_self (Nat.succ_ne_zero j) hlt
      rw [hm, Nat.cast_mul, norm_mul]
      have h3 : ‖((T - 1) ^ j) x‖ ≤ 1 * ‖x‖ :=
        hle.trans (mul_le_mul_of_nonneg_right hsj (norm_nonneg _))
      calc _ ≤ ‖((l : ℕ) : Om l)‖ * 1 * (1 * ‖x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ ≤ M * ‖x‖ := by
            rw [mul_one, one_mul]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    ·
      have hjl : j = l - 1 := by have := Finset.mem_range.mp hj; omega
      have hc : l.choose (j + 1) = 1 := by
        rw [show j + 1 = l by have := Finset.mem_range.mp hj; omega, Nat.choose_self]
      rw [hc, Nat.cast_one, norm_one, one_mul]
      calc _ ≤ s ^ j * ‖x‖ := hle
        _ ≤ M * ‖x‖ := by
            rw [hjl]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

  set y := ∑ i ∈ Finset.range l, (σ ^ i) x with hy
  have hyS : y ∈ S := S.sum_mem fun i _ => hpowS i x hx
  have htel : (σ ^ l) x - x = σ y - y := by
    rw [hy, map_sum, ← Finset.sum_sub_distrib]
    have h := Finset.sum_range_sub (fun i => (σ ^ i) x) l
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', AlgEquiv.mul_apply]
  refine ⟨hbound, ?_⟩
  rw [htel]
  calc ‖σ y - y‖ ≤ s * ‖y‖ := hσ y hyS
    _ ≤ s * (M * ‖x‖) := mul_le_mul_of_nonneg_left hbound hs0
    _ = M * s * ‖x‖ := by ring

end GlobalTheory.MemLoc
