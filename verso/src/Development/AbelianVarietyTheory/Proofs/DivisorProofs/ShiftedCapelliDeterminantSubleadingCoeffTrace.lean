import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

namespace GlobalTheory.CapelliNext

open Finset

variable {A : Type} [Ring A] [Algebra ℂ A]

def shiftCoeff (d : ℕ) (p q : A) (c : ℕ → A) : ℕ → A :=
  fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0)

/- English proof (translation)
Unfold `shiftCoeff`. Simplify using `only [smul_add, sum_add_distrib, add_mul]`. Use `congr 1`. Rewrite using `[sum_range_succ' _ (d + 1), mul_sum]`. Simplify using `only [Nat.rec_zero, smul_zero, add_zero]`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]`. Rewrite using `[sum_range_succ _ (d + 1), mul_sum]`. Simplify using `only [lt_irrefl, if_false, smul_zero, add_zero]`. Use `sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[if_pos (mem_range.mp hi), mul_smul_comm]`.
-/
theorem affine_mul_eq (d : ℕ) (p q : A) (c : ℕ → A) (u : ℂ) :
    (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • shiftCoeff d p q c i := by
  unfold shiftCoeff
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
Proceed by induction on `t with`. Consider the case `zero`. Set `c : ℕ → A` to `fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0`. Use `⟨c, ?_, ?_, fun u => ?_⟩` and prove the remaining obligations. Simplify using `[c]`.

Simplify using `[c]`. Simplify using `[c, sum_range_succ, add_comm]`. Rewrite using `[mul_smul]`. Consider the case `succ t ih`. Take `⟨c, hc1, hc0, hc⟩` from `ih (fun k => p k.succ) (fun k => q k.succ)`.

Use `⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [shiftCoeff, lt_irrefl, if_false, add_zero]`. Rewrite using `[hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]`. Simplify using `only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]`. Rewrite using `[hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]`.

Use `conv_rhs => rw [Fin.sum_univ_succ]`. Use `congr 1`. Simplify using `[Fin.prod_univ_succ, smul_mul_assoc]`. Use `sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]`.

Rewrite using `[List.ofFn_succ, List.prod_cons, hc u]`. Establish `: (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0` using `by rw [smul_smul]`. Rewrite using `[this, affine_mul_eq]`.
-/
theorem prod_affine_two_top (t : ℕ) (p : Fin (t + 1) → ℂ) (q : Fin (t + 1) → A) :
    ∃ c : ℕ → A, c (t + 1) = (∏ k, p k) • (1 : A) ∧
      c t = ∑ k, (∏ j, (if j = k then (1 : ℂ) else p j)) • q k ∧
      ∀ u : ℂ, (List.ofFn fun k => (u * p k) • (1 : A) + q k).prod
        = ∑ i ∈ range (t + 1 + 1), u ^ i • c i := by
  induction t with
  | zero =>
    let c : ℕ → A := fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0
    refine ⟨c, ?_, ?_, fun u => ?_⟩
    · simp [c]
    · simp [c]
    · simp [c, sum_range_succ, add_comm]
      rw [mul_smul]
  | succ t ih =>
    obtain ⟨c, hc1, hc0, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    refine ⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩
    · simp only [shiftCoeff, lt_irrefl, if_false, add_zero]
      rw [hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]
    · simp only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]
      rw [hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]
      conv_rhs => rw [Fin.sum_univ_succ]
      congr 1
      · simp [Fin.prod_univ_succ, smul_mul_assoc]
      · refine sum_congr rfl fun k _ => ?_
        simp [Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]
    · rw [List.ofFn_succ, List.prod_cons, hc u]
      have : (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0 := by rw [smul_smul]
      rw [this, affine_mul_eq]

end GlobalTheory.CapelliNext

namespace GlobalTheory.CapelliNext
open Finset

/- English proof (translation)
Introduce `A _ _ m E s`. Establish `h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A, c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧ c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) • ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧ ∀ u : ℂ, …`. Introduce `σ`. Take `⟨c, hc1, hc0, hc⟩` from `prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0) (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)`. Use `⟨c, hc1, hc0, fun u => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc u]`. Use `congr 2`. Use function extensionality and compare the values at `k`. Unfold `Formalism.REAL.Tm`. Simplify using `only [id]`.

Use `split_ifs with hk`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Use `choose c hc1 hc0 hc using h`. Use `⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]`. Rewrite using `[hc1 1]`.

Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, σ k ≠ k := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Conclude with `hσ (Equiv.ext hne)`. Rewrite using `[hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]`. Introduce `h1`. Conclude with `absurd (mem_univ _) h1`. Simplify using `only`.

Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]`. Rewrite using `[hc0 1]`. Simplify using `only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id_eq, if_true, ite_self, prod_const_one, one_smul]`. Rewrite using `[sum_add_distrib, add_comm]`. Use `congr 1`.

Simplify using `only [Algebra.algebraMap_eq_smul_one, ← sum_smul]`. Introduce `σ _ hσ`. Choose the witnesses or unpack the hypotheses as in `⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Conclude with `hσ (Equiv.ext hne)`. Rewrite using `[hc0 σ]`. Establish `hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0`. Introduce `k`. Distinguish the cases in `hk : σ k = k`.

Use `Finset.prod_eq_zero (mem_univ k₀) ?_` and prove the remaining obligations. Establish `: k₀ ≠ k` using `fun e => hk₀ (e ▸ hk)`. Simplify using `[this, hk₀]`. Use `Finset.prod_eq_zero (mem_univ (σ k)) ?_` and prove the remaining obligations. Establish `h2 : σ (σ k) ≠ σ k` using `fun e => hk (σ.injective e)`.

Simplify using `[hk, h2]`. Simplify using `[hz]`. Introduce `h1`. Conclude with `absurd (mem_univ _) h1`. Unfold `Formalism.REAL.qdet Formalism.REAL.qminor`.

Rewrite using `[Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]`. Repeatedly rewrite using `[mul_sum, mul_smul_comm]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← smul_sum]`.
-/
theorem qdet_shift_next_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i,
    ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

end GlobalTheory.CapelliNext
