import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0), by simp, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [smul_add, sum_add_distrib, add_mul]`. Use `congr 1`. Rewrite using `[sum_range_succ' _ (d + 1), mul_sum]`. Simplify using `only [Nat.rec_zero, smul_zero, add_zero]`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]`. Rewrite using `[sum_range_succ _ (d + 1), mul_sum]`. Simplify using `only [lt_irrefl, if_false, smul_zero, add_zero]`. Use `sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[if_pos (mem_range.mp hi), mul_smul_comm]`.
-/
theorem affine_mul_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (d : ℕ) (p q : A) (c : ℕ → A) :
    ∃ c' : ℕ → A, c' (d + 1) = p * c d ∧ ∀ u : ℂ, (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • c' i := by
  refine ⟨fun i => (Nat.casesOn i 0 (fun j => p * c j) : A)
    + (if i < d + 1 then q * c i else 0), by simp, fun u => ?_⟩
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => exact ⟨fun _ => 1, by simp, fun u => by simp⟩`. Consider the case `succ t ih`. Take `⟨c, hct, hc⟩` from `ih (fun k => p k.succ) (fun k => q k.succ)`. Take `⟨c', hct', hc'⟩` from `affine_mul_polyMap_top t (p 0) (q 0) c`.

Use `⟨c', ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hct', hct, List.ofFn_succ, List.prod_cons]`. Rewrite using `[List.ofFn_succ, List.prod_cons, hc u, hc' u]`.
-/
theorem prod_affine_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (p q : Fin t → A) :
    ∃ c : ℕ → A, c t = (List.ofFn p).prod ∧ ∀ u : ℂ, (List.ofFn fun k => u • p k + q k).prod
      = ∑ i ∈ range (t + 1), u ^ i • c i := by
  induction t with
  | zero => exact ⟨fun _ => 1, by simp, fun u => by simp⟩
  | succ t ih =>
    obtain ⟨c, hct, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    obtain ⟨c', hct', hc'⟩ := affine_mul_polyMap_top t (p 0) (q 0) c
    refine ⟨c', ?_, fun u => ?_⟩
    · rw [hct', hct, List.ofFn_succ, List.prod_cons]
    · rw [List.ofFn_succ, List.prod_cons, hc u, hc' u]

/- English proof (translation)
Establish `h : ∀ σ : Equiv.Perm (Fin n), ∃ c : ℕ → A, c n = (List.ofFn fun k : Fin n => if σ k = k then (1 : A) else 0).prod ∧ ∀ u : ℂ, (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod = ∑ i ∈ range (n + 1), u ^ i • c i`. Introduce `σ`. Take `⟨c, hct, hc⟩` from `prod_affine_polyMap_top n (fun k => if σ k = k then (1 : A) else 0) (fun k => Tm E (-(k : ℂ)) (σ k) k)`. Use `⟨c, hct, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc u]`.

Use `congr 2`. Use function extensionality and compare the values at `k`. Unfold `Tm`. Simplify using `only [id]`. Use `split_ifs`.

Rewrite using `[← add_assoc, ← Algebra.algebraMap_eq_smul_one, ← map_add]`. Use `congr 2`. Apply the tactic sequence `all_goals ring`. Simplify using the standard rewrite rules. Use `choose c hct hc using h`.

Establish `htop : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → c σ n = 0`. Introduce `σ hσ`. Rewrite using `[hct σ]`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, σ k ≠ k := by`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Conclude with `hσ (Equiv.ext hne)`. Apply `List.prod_eq_zero` to reduce the goal to its premises. Rewrite using `[List.mem_ofFn]`. Conclude with `⟨k, if_neg hk⟩`.

Use `⟨fun i => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ?_, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Rewrite using `[hct 1]`. Simplify using the standard rewrite rules.

Introduce `σ _ hσ`. Rewrite using `[htop σ hσ, mul_zero]`. Introduce `h1`. Conclude with `absurd (Finset.mem_univ _) h1`. Unfold `qdet qminor`.

Simplify using `only [hc, mul_sum, smul_sum, mul_smul_comm]`. Conclude with `sum_comm`.
-/
theorem qdet_polyMap_monic (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  have h : ∀ σ : Equiv.Perm (Fin n), ∃ c : ℕ → A,
      c n = (List.ofFn fun k : Fin n => if σ k = k then (1 : A) else 0).prod ∧ ∀ u : ℂ,
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (n + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hct, hc⟩ := prod_affine_polyMap_top n
      (fun k => if σ k = k then (1 : A) else 0)
      (fun k => Tm E (-(k : ℂ)) (σ k) k)
    refine ⟨c, hct, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Tm
    simp only [id]
    split_ifs
    · rw [← add_assoc, ← Algebra.algebraMap_eq_smul_one, ← map_add]
      congr 2
      all_goals ring
    · simp
  choose c hct hc using h
  have htop : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → c σ n = 0 := by
    intro σ hσ
    rw [hct σ]
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext hne)
    apply List.prod_eq_zero
    rw [List.mem_ofFn]
    exact ⟨k, if_neg hk⟩
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [hct 1]
      simp
    · intro σ _ hσ
      rw [htop σ hσ, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  · unfold qdet qminor
    simp only [hc, mul_sum, smul_sum, mul_smul_comm]
    exact sum_comm

end GlobalTheory
