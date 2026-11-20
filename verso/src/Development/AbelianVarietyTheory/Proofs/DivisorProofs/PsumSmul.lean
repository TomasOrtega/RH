import Mathlib

set_option autoImplicit false

noncomputable section

open Finset

namespace GlobalTheory.PowerSumSmul

variable {ι : Type} [Fintype ι] {N : ℕ}

def psum (r : ι → Fin N → ℝ) (τ : ι) (m : ℕ) : ℝ := ∑ k ∈ (univ : Finset (Fin N)).filter (fun k : Fin N => k.val < m), r τ k

def DegData (j : ℕ) (q : ℝ) (r : ι → Fin N → ℝ) : Prop :=
  ∃ P e : ℝ, 0 ≤ P ∧ (q - 2) * P ≤ e ∧ (∀ τ (m : ℕ), 1 ≤ m → m < N → psum r τ m ≤ P) ∧
    (∀ τ, psum r τ N = 0) ∧ -2 * ∑ τ, psum r τ j = e

def ext (v : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then v ⟨k, h⟩ else 0

/- English proof (translation)
Simplify using `[ext, k.2]`.
-/
theorem ext_fin (v : Fin N → ℝ) (k : Fin N) : ext v k = v k := by simp [ext, k.2]

/- English proof (translation)
Unfold `psum`. Rewrite using `[Finset.sum_filter]`. Establish `e1 : ∑ k : Fin N, (if k.val < m then r τ k else 0) = ∑ k : Fin N, (fun i => if i < m then ext (r τ) i else 0) k.val` using `Finset.sum_congr rfl fun k _ => by simp only [ext_fin]`. Rewrite using `[e1, Fin.sum_univ_eq_sum_range (fun i => if i < m then ext (r τ) i else 0) N, ← Finset.sum_filter]`. Use `congr 1`.

Use extensionality with `k`. Simplify using `only [mem_filter, mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem psum_eq (r : ι → Fin N → ℝ) (τ : ι) {m : ℕ} (hm : m ≤ N) :
    psum r τ m = ∑ k ∈ range m, ext (r τ) k := by
  unfold psum
  rw [Finset.sum_filter]
  have e1 : ∑ k : Fin N, (if k.val < m then r τ k else 0) =
      ∑ k : Fin N, (fun i => if i < m then ext (r τ) i else 0) k.val :=
    Finset.sum_congr rfl fun k _ => by simp only [ext_fin]
  rw [e1, Fin.sum_univ_eq_sum_range (fun i => if i < m then ext (r τ) i else 0) N, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega

/- English proof (translation)
Unfold `psum`. Rewrite using `[Finset.mul_sum]`.
-/
theorem psum_smul (r : ι → Fin N → ℝ) (c : ℝ) (τ : ι) (m : ℕ) :
    psum (fun τ i => c * r τ i) τ m = c * psum r τ m := by
  unfold psum
  rw [Finset.mul_sum]

/- English proof (translation)
Take `⟨P, e, hP, hPe, h1, h2, h3⟩` from `h`. Use `⟨c * P, c * e, mul_nonneg hc hP, ?_, fun τ m a b => ?_, fun τ => ?_, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[psum_smul]`. Conclude with `mul_le_mul_of_nonneg_left (h1 τ m a b) hc`.

Rewrite using `[psum_smul, h2, mul_zero]`. Simplify using `only [psum_smul, ← Finset.mul_sum]`. Rewrite using `[← h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem DegData.smul {j : ℕ} {q : ℝ} {r : ι → Fin N → ℝ} (h : DegData j q r) {c : ℝ} (hc : 0 ≤ c) :
    DegData j q (fun τ i => c * r τ i) := by
  obtain ⟨P, e, hP, hPe, h1, h2, h3⟩ := h
  refine ⟨c * P, c * e, mul_nonneg hc hP, ?_, fun τ m a b => ?_, fun τ => ?_, ?_⟩
  · nlinarith
  · rw [psum_smul]; exact mul_le_mul_of_nonneg_left (h1 τ m a b) hc
  · rw [psum_smul, h2, mul_zero]
  · simp only [psum_smul, ← Finset.mul_sum]; rw [← h3]; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, le_rfl, by simp, fun _ _ _ _ => by simp [psum], fun _ => by simp [psum], by simp [psum]⟩`.
-/
theorem DegData.zero (j : ℕ) (q : ℝ) (hq : 2 ≤ q) : DegData j q (fun (_ : ι) (_ : Fin N) => (0 : ℝ)) :=
  ⟨0, 0, le_rfl, by simp, fun _ _ _ _ => by simp [psum], fun _ => by simp [psum], by simp [psum]⟩

/- English proof (translation)
Establish `e1 : ∑ i, -(w i) * r i = ∑ i ∈ range N, ext w i • (fun k => -ext r k) i`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => ext w i • (fun k => -ext r k) i) N]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [ext_fin, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, Finset.sum_range_by_parts]`. Simplify using `only [Finset.sum_neg_distrib, h0, neg_zero, smul_zero, zero_sub, smul_eq_mul, mul_neg, ← sub_eq_add_neg]`. Rewrite using `[← Finset.sum_neg_distrib]`. Simplify using the standard rewrite rules.
-/
theorem abel (w r : Fin N → ℝ) (h0 : ∑ k ∈ range N, ext r k = 0) :
    ∑ i, -(w i) * r i =
      ∑ i ∈ range (N - 1), (ext w (i + 1) - ext w i) * ∑ k ∈ range (i + 1), ext r k := by
  have e1 : ∑ i, -(w i) * r i = ∑ i ∈ range N, ext w i • (fun k => -ext r k) i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ext w i • (fun k => -ext r k) i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ext_fin, smul_eq_mul]
    ring
  rw [e1, Finset.sum_range_by_parts]
  simp only [Finset.sum_neg_distrib, h0, neg_zero, smul_zero, zero_sub, smul_eq_mul, mul_neg, ← sub_eq_add_neg]
  rw [← Finset.sum_neg_distrib]
  simp

/- English proof (translation)
Rewrite using `[abel w r h0]`. Establish `hmono : ∀ i ∈ range (N - 1), ext w (i + 1) - ext w i ≤ 0` using `fun i hi => by`. Rewrite `hi` using `[mem_range]`. Establish `h1 : i + 1 < N` using `by omega`. Establish `h2 : i < N` using `by omega`.

Simplify using `only [ext, h1, h2, dif_pos]`. Use `hdom ⟨i, h2⟩ ⟨i + 1, h1⟩ (by simp [Fin.le_iff_val_le_val])` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : ∀ i ∈ range (N - 1), (ext w (i + 1) - ext w i) * ∑ k ∈ range (i + 1), ext r k = P * (ext w (i + 1) - ext w i) + (ext w (i + 1) - ext w i) * (∑ k ∈ range (i + 1), ext r k - P)` using `fun i _ => by ring`. Rewrite using `[Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub]`.

Establish `hN1 : N - 1 = (N - 1 - 1) + 1` using `by omega`. Establish `hj' : j - 1 ∈ range (N - 1)` using `by rw [mem_range]; omega`. Establish `hnn : ∀ i ∈ range (N - 1), 0 ≤ (ext w (i + 1) - ext w i) * (∑ k ∈ range (i + 1), ext r k - P)` using `fun i hi => by`. Establish `h1` using `hmono i hi`. Establish `h2` using `hs (i + 1) (by omega) (by rw [mem_range] at hi; omega)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hsingle` using `Finset.single_le_sum hnn hj'`. Establish `hj2 : j - 1 + 1 = j` using `by omega`. Rewrite `hsingle` using `[hj2]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem term_ge (j : ℕ) (hj1 : 1 ≤ j) (hjN : j < N) (w r : Fin N → ℝ) (P : ℝ)
    (hdom : ∀ a b : Fin N, a ≤ b → w b ≤ w a)
    (hs : ∀ m, 1 ≤ m → m < N → ∑ k ∈ range m, ext r k ≤ P) (h0 : ∑ k ∈ range N, ext r k = 0) :
    P * (ext w (N - 1) - ext w 0) + (ext w (j - 1) - ext w j) * (P - ∑ k ∈ range j, ext r k) ≤
      ∑ i, -(w i) * r i := by
  rw [abel w r h0]
  have hmono : ∀ i ∈ range (N - 1), ext w (i + 1) - ext w i ≤ 0 := fun i hi => by
    rw [mem_range] at hi
    have h1 : i + 1 < N := by omega
    have h2 : i < N := by omega
    simp only [ext, h1, h2, dif_pos]
    have := hdom ⟨i, h2⟩ ⟨i + 1, h1⟩ (by simp [Fin.le_iff_val_le_val])
    linarith
  have hsplit : ∀ i ∈ range (N - 1), (ext w (i + 1) - ext w i) * ∑ k ∈ range (i + 1), ext r k =
      P * (ext w (i + 1) - ext w i) + (ext w (i + 1) - ext w i) * (∑ k ∈ range (i + 1), ext r k - P) :=
    fun i _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub]
  have hN1 : N - 1 = (N - 1 - 1) + 1 := by omega
  have hj' : j - 1 ∈ range (N - 1) := by rw [mem_range]; omega
  have hnn : ∀ i ∈ range (N - 1), 0 ≤ (ext w (i + 1) - ext w i) * (∑ k ∈ range (i + 1), ext r k - P) :=
    fun i hi => by
      have h1 := hmono i hi
      have h2 := hs (i + 1) (by omega) (by rw [mem_range] at hi; omega)
      nlinarith
  have hsingle := Finset.single_le_sum hnn hj'
  have hj2 : j - 1 + 1 = j := by omega
  rw [hj2] at hsingle
  nlinarith

/- English proof (translation)
Take `⟨P, e, hP, hPe, h1, h2, h3⟩` from `hD`. Break down `isEmpty_or_nonempty ι with hι | ⟨⟨τ₀⟩⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `hS0 : 0 ≤ S` using `le_trans (abs_nonneg _) (hS τ₀ ⟨0, by omega⟩)`. Establish `hq2 : 0 < q - 2` using `by linarith`.

Establish `hf0 : 0 ≤ f` using `le_trans (Nat.cast_nonneg _) hf`. Use `set G0 : ℝ := 4 * f * S / (q - 2) with hG0`. Establish `hG0nn : 0 ≤ G0` using `div_nonneg (by positivity) hq2.le`. Establish `hT : ∀ τ, -2 * S * P + G0 * (P - psum r τ j) ≤ ∑ i, -(w τ i) * r τ i` using `fun τ => by`. Establish `ht` using `term_ge j hj1 hjN (w τ) (r τ) P (hdom τ) (fun m a b => (psum_eq r τ b.le).symm.trans_le (h1 τ m a b)) ((psum_eq r τ le_rfl).symm.trans (h2 τ))`.

Rewrite `ht` using `[← psum_eq r τ hjN.le]`. Establish `hN1 : N - 1 < N` using `by omega`. Establish `e0 : ext (w τ) (N - 1) = w τ ⟨N - 1, hN1⟩` using `by simp [ext, hN1]`. Establish `e00 : ext (w τ) 0 = w τ ⟨0, by omega⟩` using `by simp [ext, show 0 < N by omega]`. Establish `ej : ext (w τ) (j - 1) = w τ ⟨j - 1, by omega⟩` using `by simp [ext, show j - 1 < N by omega]`.

Establish `ej' : ext (w τ) j = w τ ⟨j, hjN⟩` using `by simp [ext, hjN]`. Rewrite `ht` using `[e0, e00, ej, ej']`. Establish `a1` using `abs_le.1 (hS τ ⟨N - 1, hN1⟩)`. Establish `a2` using `abs_le.1 (hS τ ⟨0, by omega⟩)`. Establish `hPs : 0 ≤ P - psum r τ j` using `by have := h1 τ j hj1 hjN; linarith`.

Establish `hg : G0 ≤ w τ ⟨j - 1, by omega⟩ - w τ ⟨j, hjN⟩`. Rewrite using `[hG0, div_le_iff₀ hq2]`. Combine the linear relations using `[hgap τ]`. Establish `b1 : -2 * S * P ≤ P * (w τ ⟨N - 1, hN1⟩ - w τ ⟨0, by omega⟩)` using `by nlinarith`. Establish `b2 : G0 * (P - psum r τ j) ≤ (w τ ⟨j - 1, by omega⟩ - w τ ⟨j, hjN⟩) * (P - psum r τ j)` using `mul_le_mul_of_nonneg_right hg hPs`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `Finset.sum_le_sum fun τ (_ : τ ∈ (univ : Finset ι)) => hT τ`. Establish `hL : ∑ τ, (-2 * S * P + G0 * (P - psum r τ j)) = (Fintype.card ι : ℝ) * (-2 * S * P + G0 * P) + G0 * (e / 2)`. Rewrite using `[← h3]`. Simplify using `only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hsum` using `[hL]`. Establish `hkey : 0 ≤ G0 * (e / 2) - 2 * f * S * P`. Establish `: G0 * (e / 2) - 2 * f * S * P = (2 * f * S / (q - 2)) * (e - (q - 2) * P)`. Rewrite using `[hG0]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_nonneg (div_nonneg (by positivity) hq2.le) (by linarith)`. Establish `hc : (Fintype.card ι : ℝ) * (S * P) ≤ f * (S * P)` using `mul_le_mul_of_nonneg_right hf (mul_nonneg hS0 hP)`.

Establish `hc2 : 0 ≤ (Fintype.card ι : ℝ) * (G0 * P)` using `mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hG0nn hP)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem chain (j : ℕ) (hj1 : 1 ≤ j) (hjN : j < N) (q f S : ℝ) (hq : 2 < q) (hf : (Fintype.card ι : ℝ) ≤ f)
    (w r : ι → Fin N → ℝ) (hdom : ∀ τ (a b : Fin N), a ≤ b → w τ b ≤ w τ a) (hS : ∀ τ i, |w τ i| ≤ S)
    (hgap : ∀ τ, 4 * f * S ≤ (q - 2) * (w τ ⟨j - 1, by omega⟩ - w τ ⟨j, hjN⟩)) (hD : DegData j q r) :
    0 ≤ ∑ τ, ∑ i, -(w τ i) * r τ i := by
  obtain ⟨P, e, hP, hPe, h1, h2, h3⟩ := hD
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨τ₀⟩⟩
  · simp
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS τ₀ ⟨0, by omega⟩)
  have hq2 : 0 < q - 2 := by linarith
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hf
  set G0 : ℝ := 4 * f * S / (q - 2) with hG0
  have hG0nn : 0 ≤ G0 := div_nonneg (by positivity) hq2.le
  have hT : ∀ τ, -2 * S * P + G0 * (P - psum r τ j) ≤ ∑ i, -(w τ i) * r τ i := fun τ => by
    have ht := term_ge j hj1 hjN (w τ) (r τ) P (hdom τ)
      (fun m a b => (psum_eq r τ b.le).symm.trans_le (h1 τ m a b)) ((psum_eq r τ le_rfl).symm.trans (h2 τ))
    rw [← psum_eq r τ hjN.le] at ht
    have hN1 : N - 1 < N := by omega
    have e0 : ext (w τ) (N - 1) = w τ ⟨N - 1, hN1⟩ := by simp [ext, hN1]
    have e00 : ext (w τ) 0 = w τ ⟨0, by omega⟩ := by simp [ext, show 0 < N by omega]
    have ej : ext (w τ) (j - 1) = w τ ⟨j - 1, by omega⟩ := by simp [ext, show j - 1 < N by omega]
    have ej' : ext (w τ) j = w τ ⟨j, hjN⟩ := by simp [ext, hjN]
    rw [e0, e00, ej, ej'] at ht
    have a1 := abs_le.1 (hS τ ⟨N - 1, hN1⟩)
    have a2 := abs_le.1 (hS τ ⟨0, by omega⟩)
    have hPs : 0 ≤ P - psum r τ j := by have := h1 τ j hj1 hjN; linarith
    have hg : G0 ≤ w τ ⟨j - 1, by omega⟩ - w τ ⟨j, hjN⟩ := by
      rw [hG0, div_le_iff₀ hq2]; linarith [hgap τ]
    have b1 : -2 * S * P ≤ P * (w τ ⟨N - 1, hN1⟩ - w τ ⟨0, by omega⟩) := by nlinarith
    have b2 : G0 * (P - psum r τ j) ≤ (w τ ⟨j - 1, by omega⟩ - w τ ⟨j, hjN⟩) * (P - psum r τ j) :=
      mul_le_mul_of_nonneg_right hg hPs
    linarith
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ (univ : Finset ι)) => hT τ
  have hL : ∑ τ, (-2 * S * P + G0 * (P - psum r τ j)) =
      (Fintype.card ι : ℝ) * (-2 * S * P + G0 * P) + G0 * (e / 2) := by
    rw [← h3]
    simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hL] at hsum
  have hkey : 0 ≤ G0 * (e / 2) - 2 * f * S * P := by
    have : G0 * (e / 2) - 2 * f * S * P = (2 * f * S / (q - 2)) * (e - (q - 2) * P) := by
      rw [hG0]; field_simp; ring
    rw [this]
    exact mul_nonneg (div_nonneg (by positivity) hq2.le) (by linarith)
  have hc : (Fintype.card ι : ℝ) * (S * P) ≤ f * (S * P) := mul_le_mul_of_nonneg_right hf (mul_nonneg hS0 hP)
  have hc2 : 0 ≤ (Fintype.card ι : ℝ) * (G0 * P) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hG0nn hP)
  nlinarith

end GlobalTheory.PowerSumSmul
