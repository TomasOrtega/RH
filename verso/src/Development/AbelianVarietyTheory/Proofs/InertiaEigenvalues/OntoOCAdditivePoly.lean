import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametricStatement
open Polynomial

/- English proof (translation)
Introduce `l hl E N a hNE ha haN b hb`. Use `set f : ℂ_[l][X] := (∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k)) - C b with hf`. Establish `hl1 : 1 < l` using `hl.out.one_lt`. Establish `hinj : Function.Injective (fun k : ℕ => l ^ k)` using `Nat.pow_right_injective hl.out.two_le`. Establish `hcoeff : ∀ j, f.coeff j = (∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0) - (if j = 0 then b else 0)`.

Introduce `j`. Simplify using `only [hf, coeff_sub, finsetSum_coeff, coeff_monomial, coeff_C]`. Establish `hcN : f.coeff (l ^ N) = a N`. Rewrite using `[hcoeff]`. Establish `h0 : l ^ N ≠ 0` using `pow_ne_zero _ (by omega)`.

Rewrite using `[if_neg h0, sub_zero, Finset.sum_eq_single N]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hk (hinj h)`. Introduce `h; exact absurd (Finset.mem_range.2 (by omega)) h`. Establish `hbound : ∀ j, ‖f.coeff j‖ ≤ 1`. Introduce `j`. Rewrite using `[hcoeff]`.

Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_` and prove the remaining obligations. Introduce `k hk`. Use `split_ifs`.

Conclude with `ha k (by have := Finset.mem_range.1 hk; omega)`. Simplify using the standard rewrite rules. Rewrite using `[norm_neg]`. Use `split_ifs`. Conclude with `hb`.

Simplify using the standard rewrite rules. Establish `hne : f.coeff (l ^ N) ≠ 0`. Rewrite using `[hcN]`. Introduce `h`. Rewrite `haN` using `[h, norm_zero]`.

Conclude with `zero_ne_one haN`. Establish `key` using `(GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] f 1 (l ^ N) zero_lt_one hne).1 (by`. Introduce `j`. Simplify using `only [one_pow, mul_one]`. Rewrite using `[hcN, haN]`.

Conclude with `hbound j)`. Establish `hpos : 0 < Multiset.card (f.roots.filter fun z => ‖z‖ ≤ 1)` using `lt_of_lt_of_le (pow_pos (by omega) N) key`. Take `⟨W, hW⟩` from `Multiset.card_pos_iff_exists_mem.1 hpos`. Rewrite `hW` using `[Multiset.mem_filter]`. Take `⟨hr, hWn⟩` from `hW`.

Use `⟨W, hWn, ?_⟩` and prove the remaining obligations. Establish `hroot` using `(mem_roots'.1 hr).2`. Rewrite `hroot` using `[IsRoot, hf, eval_sub, eval_finsetSum, eval_C]`. Simplify using `only [eval_monomial] at hroot`. Conclude with `sub_eq_zero.1 hroot`.
-/
theorem GlobalTheory.onto_OC_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  intro l hl E N a hNE ha haN b hb
  set f : ℂ_[l][X] := (∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k)) - C b with hf
  have hl1 : 1 < l := hl.out.one_lt
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl.out.two_le
  have hcoeff : ∀ j, f.coeff j = (∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0) - (if j = 0 then b else 0) := by
    intro j
    simp only [hf, coeff_sub, finsetSum_coeff, coeff_monomial, coeff_C]
  have hcN : f.coeff (l ^ N) = a N := by
    rw [hcoeff]
    have h0 : l ^ N ≠ 0 := pow_ne_zero _ (by omega)
    rw [if_neg h0, sub_zero, Finset.sum_eq_single N]
    · simp
    · intro k _ hk; rw [if_neg]; intro h; exact hk (hinj h)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hbound : ∀ j, ‖f.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro k hk
      split_ifs
      · exact ha k (by have := Finset.mem_range.1 hk; omega)
      · simp
    · rw [norm_neg]; split_ifs
      · exact hb
      · simp
  have hne : f.coeff (l ^ N) ≠ 0 := by
    rw [hcN]; intro h; rw [h, norm_zero] at haN; exact zero_ne_one haN
  have key := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] f 1 (l ^ N) zero_lt_one hne).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcN, haN]; exact hbound j)
  have hpos : 0 < Multiset.card (f.roots.filter fun z => ‖z‖ ≤ 1) :=
    lt_of_lt_of_le (pow_pos (by omega) N) key
  obtain ⟨W, hW⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  rw [Multiset.mem_filter] at hW
  obtain ⟨hr, hWn⟩ := hW
  refine ⟨W, hWn, ?_⟩
  have hroot := (mem_roots'.1 hr).2
  rw [IsRoot, hf, eval_sub, eval_finsetSum, eval_C] at hroot
  simp only [eval_monomial] at hroot
  exact sub_eq_zero.1 hroot
