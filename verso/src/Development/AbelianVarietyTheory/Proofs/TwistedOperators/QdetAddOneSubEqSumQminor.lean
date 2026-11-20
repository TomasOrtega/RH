import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset

namespace GlobalTheory.CapelliDiff

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `x y d h`. Simplify using `[h 0]`.

Consider the case `succ n ih`. Introduce `x y d h`. Rewrite using `[List.ofFn_succ (f := y), List.ofFn_succ (f := x), List.prod_cons, List.prod_cons, Fin.sum_univ_succ]`. Establish `key` using `ih (fun i => x i.succ) (fun i => y i.succ) (fun i => d i.succ) (fun i => h i.succ)`. Establish `e1 : y 0 * (List.ofFn fun i : Fin (n+1) => y i.succ).prod - x 0 * (List.ofFn fun i : Fin (n+1) => x i.succ).prod = algebraMap ℂ A (d 0) * (List.ofFn fun i : Fin (n+1) => y i.succ).prod + x 0 * ((List.ofFn fun i : Fin (n+1) => y i.succ).prod - (List.ofFn fun i : Fin (n+1) => x i.s …`.

Rewrite using `[h 0]`. Use `noncomm_ring`. Rewrite using `[e1, key, Finset.mul_sum]`. Use `congrArg₂ (· + ·) ?_ ?_` and prove the remaining obligations. Use `congr 2`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Establish `h0 : (Fin.castSucc (0 : Fin (n+1)) : Fin (n+2)) < k.succ` using `by simp [Fin.succ_pos]`. Rewrite using `[if_pos h0, Fin.castSucc_zero, ← mul_assoc (x 0), ← Algebra.commutes, mul_assoc]`.

Establish `hl : (List.ofFn fun j : Fin n => if j.castSucc < k then x j.castSucc.succ else y j.succ.succ) = (List.ofFn fun i : Fin n => if i.succ.castSucc < k.succ then x i.succ.castSucc else y i.succ.succ)`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `only [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]`. Rewrite using `[hl]`.
-/
theorem prod_ofFn_sub {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (n : ℕ) (x y : Fin (n + 1) → A) (d : Fin (n + 1) → ℂ),
      (∀ k, y k = x k + algebraMap ℂ A (d k)) →
      (List.ofFn y).prod - (List.ofFn x).prod =
        ∑ k : Fin (n + 1), algebraMap ℂ A (d k) *
          (List.ofFn fun j : Fin n => if Fin.castSucc j < k then x (Fin.castSucc j) else y j.succ).prod := by
  intro n
  induction n with
  | zero =>
    intro x y d h
    simp [h 0]
  | succ n ih =>
    intro x y d h
    rw [List.ofFn_succ (f := y), List.ofFn_succ (f := x), List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    have key := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => d i.succ) (fun i => h i.succ)
    have e1 : y 0 * (List.ofFn fun i : Fin (n+1) => y i.succ).prod - x 0 * (List.ofFn fun i : Fin (n+1) => x i.succ).prod
        = algebraMap ℂ A (d 0) * (List.ofFn fun i : Fin (n+1) => y i.succ).prod + x 0 * ((List.ofFn fun i : Fin (n+1) => y i.succ).prod - (List.ofFn fun i : Fin (n+1) => x i.succ).prod) := by
      rw [h 0]; noncomm_ring
    rw [e1, key, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · congr 2
    · apply Finset.sum_congr rfl
      intro k _
      rw [List.ofFn_succ, List.prod_cons]
      have h0 : (Fin.castSucc (0 : Fin (n+1)) : Fin (n+2)) < k.succ := by simp [Fin.succ_pos]
      rw [if_pos h0, Fin.castSucc_zero, ← mul_assoc (x 0), ← Algebra.commutes, mul_assoc]
      have hl : (List.ofFn fun j : Fin n => if j.castSucc < k then x j.castSucc.succ else y j.succ.succ) =
          (List.ofFn fun i : Fin n => if i.succ.castSucc < k.succ then x i.succ.castSucc else y i.succ.succ) := by
        congr 1; funext j; simp only [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]
      rw [hl]

/- English proof (translation)
Unfold `Tm`. Apply the tactic sequence `split_ifs <;> simp [map_add]; abel`.
-/
theorem Tm_add_one {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) :
    Tm E (v + 1) a b = Tm E v a b + algebraMap ℂ A (if a = b then 1 else 0) := by
  unfold Tm
  split_ifs <;> simp [map_add]; abel

def extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.ofSubtype ((finSuccAboveEquiv k).permCongr τ)

/- English proof (translation)
Establish `hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1))`. Rewrite using `[finSuccAboveEquiv_apply]`. Unfold `extAt`. Rewrite using `[hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply, finSuccAboveEquiv_apply]`.
-/
theorem extAt_succAbove {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    extAt k τ (k.succAbove j) = k.succAbove (τ j) := by
  have hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1)) := by
    rw [finSuccAboveEquiv_apply]
  unfold extAt
  rw [hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSuccAboveEquiv_apply]

/- English proof (translation)
Unfold `extAt`. Rewrite using `[Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]`.
-/
theorem sign_extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by
  unfold extAt
  rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]

/- English proof (translation)
Set `e : Equiv.Perm (Fin m) ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ a, ¬ (a ≠ k) → f a = a}` to `((finSuccAboveEquiv k).permCongr).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ≠ k))`. Rewrite using `[← Finset.sum_filter]`. Rewrite using `[Finset.sum_subtype (p := fun f : Equiv.Perm (Fin (m + 1)) => ∀ a, ¬ (a ≠ k) → f a = a)]`. Rewrite using `[← Equiv.sum_comp e]`. Both sides reduce to the same expression.

Introduce `σ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Rewrite using `[ha]`.

Conclude with `h`. Introduce `h`. Conclude with `h k rfl`.
-/
theorem sum_fix_eq {A : Type*} [AddCommMonoid A] {m : ℕ} (k : Fin (m + 1))
    (g : Equiv.Perm (Fin (m + 1)) → A) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ k = k then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin m), g (extAt k τ) := by
  let e : Equiv.Perm (Fin m) ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ a, ¬ (a ≠ k) → f a = a} :=
    ((finSuccAboveEquiv k).permCongr).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ≠ k))
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun f : Equiv.Perm (Fin (m + 1)) => ∀ a, ¬ (a ≠ k) → f a = a)]
  · rw [← Equiv.sum_comp e]
    rfl
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · intro h a ha; rw [ha]; exact h
    · intro h; exact h k rfl

/- English proof (translation)
Unfold `qdet qminor`. Rewrite using `[← Finset.sum_sub_distrib]`. Repeatedly rewrite using `[← mul_sub]`. Establish `step : ∀ σ : Equiv.Perm (Fin (m + 1)), (List.ofFn fun k : Fin (m + 1) => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)).prod - (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod = ∑ k : Fin (m + 1), algebraMap ℂ A (if σ k = k then 1 else 0) * (List.ofFn fun j …`. Introduce `σ`.

Rewrite using `[prod_ofFn_sub m (fun k => Tm E (u - (k : ℂ)) (id (σ k)) (id k)) (fun k => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)) (fun k => if σ k = k then 1 else 0)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Use `congr 2`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : Fin.castSucc j < k`. Rewrite using `[if_pos hj, Fin.succAbove_of_castSucc_lt k j hj]`. Simplify using `[Fin.coe_castSucc]`. Rewrite using `[if_neg hj, Fin.succAbove_of_le_castSucc k j (not_lt.mp hj)]`.

Simplify using `only [id, Fin.val_succ]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `k`.

Establish `: u + 1 - (k : ℂ) = (u - (k : ℂ)) + 1` using `by ring`. Simplify using `only [this, Tm_add_one, id]`. Repeatedly rewrite using `[step, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `k _`. Establish `h2 : ∀ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * (algebraMap ℂ A (if σ k = k then 1 else 0) * (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod) = if σ k = k then ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun j : Fin m = …`. Introduce `σ`. Apply the tactic sequence `split_ifs <;> simp`. Repeatedly rewrite using `[h2]`.

Rewrite using `[sum_fix_eq k (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `τ _`. Simplify using `only [sign_extAt, extAt_succAbove]`.
-/
theorem qdet_add_one_sub (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ) :
    qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  unfold qdet qminor
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have step : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn fun k : Fin (m + 1) => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)).prod -
        (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ k : Fin (m + 1), algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod := by
    intro σ
    rw [prod_ofFn_sub m (fun k => Tm E (u - (k : ℂ)) (id (σ k)) (id k))
      (fun k => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)) (fun k => if σ k = k then 1 else 0)]
    · apply Finset.sum_congr rfl
      intro k _
      congr 2
      congr 1
      funext j
      by_cases hj : Fin.castSucc j < k
      · rw [if_pos hj, Fin.succAbove_of_castSucc_lt k j hj]
        simp [Fin.coe_castSucc]
      · rw [if_neg hj, Fin.succAbove_of_le_castSucc k j (not_lt.mp hj)]
        simp only [id, Fin.val_succ]
        congr 1
        push_cast; ring
    · intro k
      have : u + 1 - (k : ℂ) = (u - (k : ℂ)) + 1 := by ring
      simp only [this, Tm_add_one, id]
  simp_rw [step, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤ) : A) * (algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod) =
      if σ k = k then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod else 0 := by
    intro σ
    split_ifs <;> simp
  simp_rw [h2]
  rw [sum_fix_eq k (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod)]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [sign_extAt, extAt_succAbove]

end GlobalTheory.CapelliDiff

/- English proof (translation)
The claim follows from `GlobalTheory.CapelliDiff.qdet_add_one_sub`.
-/
theorem GlobalTheory.qdet_add_one_sub_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u :=
  GlobalTheory.CapelliDiff.qdet_add_one_sub
