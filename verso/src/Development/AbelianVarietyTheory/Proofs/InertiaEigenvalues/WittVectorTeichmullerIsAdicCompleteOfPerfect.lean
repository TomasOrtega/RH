import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit

open scoped NNReal
open Ideal Finset GlobalTheory.Per.AinfComplete

namespace GlobalTheory.WittTeichComplete

open scoped NNReal in
open Ideal Finset in
/- English proof (translation)
Establish `hsum` using `_root_.GlobalTheory.Per.AinfComplete.summ_of_precomplete y`. Unfold `_root_.GlobalTheory.Per.AinfComplete.Summ at hsum`. Unfold `_root_.GlobalTheory.Per.AinfComplete.Tails`. Introduce `b`. Use `choose L hL using fun n => hsum (fun k => b (n + k))`.

Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `key : ∀ m, y ^ m ∣ L n - y * L (n + 1) - b n`. Introduce `m`. Establish `h₁` using `Ideal.mem_span_singleton.1 (hL n (m + 1))`. Establish `h₂` using `Ideal.mem_span_singleton.1 (hL (n + 1) m)`.

Establish `hs : ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i) = b n + y * ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i)`. Rewrite using `[Finset.sum_range_succ', Finset.mul_sum, add_comm]`. Simplify using `only [pow_zero, one_mul, add_zero]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[pow_succ, show n + (i + 1) = n + 1 + i by omega]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : L n - y * L (n + 1) - b n = (L n - ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i)) - y * (L (n + 1) - ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i))`. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hd]`. Conclude with `dvd_sub ((pow_dvd_pow y (Nat.le_succ m)).trans h₁) (dvd_mul_of_dvd_right h₂ y)`. Establish `h0` using `_root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus y _ fun m => Ideal.mem_span_singleton.2 (key m)`. Conclude with `(sub_eq_zero.1 h0).symm`.
-/
private lemma tails_of_isAdicComplete_span {A : Type*} [CommRing A] (y : A)
    [IsAdicComplete (Ideal.span {y}) A] : _root_.GlobalTheory.Per.AinfComplete.Tails y := by
  have hsum := _root_.GlobalTheory.Per.AinfComplete.summ_of_precomplete y
  unfold _root_.GlobalTheory.Per.AinfComplete.Summ at hsum
  unfold _root_.GlobalTheory.Per.AinfComplete.Tails
  intro b
  choose L hL using fun n => hsum (fun k => b (n + k))
  refine ⟨L, fun n => ?_⟩
  have key : ∀ m, y ^ m ∣ L n - y * L (n + 1) - b n := by
    intro m
    have h₁ := Ideal.mem_span_singleton.1 (hL n (m + 1))
    have h₂ := Ideal.mem_span_singleton.1 (hL (n + 1) m)
    have hs : ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i) =
        b n + y * ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, one_mul, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, show n + (i + 1) = n + 1 + i by omega]
      ring
    have hd : L n - y * L (n + 1) - b n =
        (L n - ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i)) -
          y * (L (n + 1) - ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i)) := by
      rw [hs]; ring
    rw [hd]
    exact dvd_sub ((pow_dvd_pow y (Nat.le_succ m)).trans h₁) (dvd_mul_of_dvd_right h₂ y)
  have h0 := _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus y _ fun m => Ideal.mem_span_singleton.2 (key m)
  exact (sub_eq_zero.1 h0).symm

open scoped NNReal in
open Ideal Finset in

/- English proof (translation)
Introduce `l _ O _ _ _ _ x _ hc`. Use `haveI := hc`. Establish `hcc : WittVector.constantCoeff (WittVector.teichmuller l x) = x`. Simplify using `[WittVector.constantCoeff]`. Take `⟨h₁, h₂⟩` from `_root_.GlobalTheory.Per.AinfComplete.witt_complete (WittVector.teichmuller l x) (hcc ▸ tails_of_isAdicComplete_span x) (fun r hr => _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus x r fun n => Ideal.mem_span_singleton.2 (hcc ▸ hr n))`.

Use `⟨h₂, ?_⟩` and prove the remaining obligations. Rewrite `h₁` using `[Ideal.span_insert]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.WittTeichComplete.main : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
    [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O →
    IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧
      IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔
        Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  intro l _ O _ _ _ _ x _ hc
  haveI := hc
  have hcc : WittVector.constantCoeff (WittVector.teichmuller l x) = x := by
    simp [WittVector.constantCoeff]
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.Per.AinfComplete.witt_complete (WittVector.teichmuller l x)
    (hcc ▸ tails_of_isAdicComplete_span x) (fun r hr => _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus x r
      fun n => Ideal.mem_span_singleton.2 (hcc ▸ hr n))
  refine ⟨h₂, ?_⟩
  rwa [Ideal.span_insert] at h₁

end GlobalTheory.WittTeichComplete
