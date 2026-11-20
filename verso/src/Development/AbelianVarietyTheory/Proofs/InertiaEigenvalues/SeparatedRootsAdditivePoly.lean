import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetManySeparatedPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FewRootsSmallDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametricStatement
open Polynomial
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ E M h a ρ hMh ha1 haMh hρ0 hρ1 haM hak`. Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hinj : Function.Injective (fun k : ℕ => l ^ k)` using `Nat.pow_right_injective hl`. Use `set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) with hG`. Establish `hcoeff : ∀ j, G.coeff j = ∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0`.

Introduce `j`. Simplify using `only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]`. Establish `hcd : G.coeff (l ^ (M + h)) = a (M + h)`. Rewrite using `[hcoeff, Finset.sum_eq_single (M + h)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `hh`. Conclude with `hb (hinj hh)`. Introduce `hn; exact absurd (Finset.mem_range.2 (by omega)) hn`.

Establish `hcd0 : G.coeff (l ^ (M + h)) ≠ 0`. Rewrite using `[hcd]`. Introduce `h0`. Rewrite `haMh` using `[h0, norm_zero]`. Conclude with `zero_ne_one haMh`.

Establish `hcle : ∀ j, ‖G.coeff j‖ ≤ 1`. Introduce `j`. Rewrite using `[hcoeff]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k hk => ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `ha1 k (by have := Finset.mem_range.1 hk; omega)`. Simplify using the standard rewrite rules. Establish `hrc` using `(GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] G 1 (l ^ (M + h)) one_pos hcd0).1 (by`. Introduce `j`. Simplify using `only [one_pow, mul_one]`.

Rewrite using `[hcd, haMh]`. Conclude with `hcle j)`. Use `set s := G.roots.filter fun z => ‖z‖ ≤ 1 with hs`. Establish `hG0 : G ≠ 0`. Introduce `h0`.

Apply `hcd0` to reduce the goal to its premises. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Take `⟨Z, hZc, hZs, hZsep⟩` from `GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster ℂ_[l] s ρ (l ^ h) (l ^ M) hρ0.le (pow_pos (by omega) _) (by rw [mul_comm, ← pow_add]; exact hrc) (by`. Introduce `W hW`.

Establish `hW1 : ‖W‖ ≤ 1` using `(Multiset.mem_filter.1 hW).2`. Use `le_trans (Multiset.card_le_card ?_) (GlobalTheory.T.card_roots_closedBall_le_prime_pow l E M a ρ W (by omega) ha1 hρ0 hρ1 haM hak hW1)` and prove the remaining obligations. Conclude with `Multiset.monotone_filter_left _ (Multiset.filter_le _ _))`. Use `⟨Z, hZc, fun W hW => ?_, hZsep⟩` and prove the remaining obligations. Establish `hWs` using `Multiset.mem_filter.1 (hZs W hW)`.

Use `⟨hWs.2, ?_⟩` and prove the remaining obligations. Establish `hr` using `(Polynomial.mem_roots hG0).1 hWs.1`. Use `hr.eq_zero` as an intermediate fact. Rewrite `this` using `[hG, Polynomial.eval_finsetSum]`. Simplify `this` using `[Polynomial.eval_monomial]`.
-/
theorem separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro l _ E M h a ρ hMh ha1 haMh hρ0 hρ1 haM hak
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) with hG
  have hcoeff : ∀ j, G.coeff j = ∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0 := by
    intro j
    simp only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  have hcd : G.coeff (l ^ (M + h)) = a (M + h) := by
    rw [hcoeff, Finset.sum_eq_single (M + h)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh; exact hb (hinj hh)
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hcd0 : G.coeff (l ^ (M + h)) ≠ 0 := by
    rw [hcd]; intro h0; rw [h0, norm_zero] at haMh; exact zero_ne_one haMh
  have hcle : ∀ j, ‖G.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k hk => ?_
    split_ifs
    · exact ha1 k (by have := Finset.mem_range.1 hk; omega)
    · simp
  have hrc := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] G 1 (l ^ (M + h)) one_pos hcd0).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcd, haMh]; exact hcle j)
  set s := G.roots.filter fun z => ‖z‖ ≤ 1 with hs
  have hG0 : G ≠ 0 := by
    intro h0; apply hcd0; rw [h0]; simp
  obtain ⟨Z, hZc, hZs, hZsep⟩ := GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster ℂ_[l] s ρ (l ^ h) (l ^ M) hρ0.le
    (pow_pos (by omega) _) (by rw [mul_comm, ← pow_add]; exact hrc) (by
      intro W hW
      have hW1 : ‖W‖ ≤ 1 := (Multiset.mem_filter.1 hW).2
      refine le_trans (Multiset.card_le_card ?_) (GlobalTheory.T.card_roots_closedBall_le_prime_pow l E M a ρ W (by omega) ha1 hρ0 hρ1 haM hak hW1)
      exact Multiset.monotone_filter_left _ (Multiset.filter_le _ _))
  refine ⟨Z, hZc, fun W hW => ?_, hZsep⟩
  have hWs := Multiset.mem_filter.1 (hZs W hW)
  refine ⟨hWs.2, ?_⟩
  have hr := (Polynomial.mem_roots hG0).1 hWs.1
  have := hr.eq_zero
  rw [hG, Polynomial.eval_finsetSum] at this
  simpa [Polynomial.eval_monomial] using this

end GlobalTheory
