import Formalism.BranchSandwichDivisors.StatementR

open Finset

namespace Formalism.BranchingDeterminantCap

/- English proof (translation)
Introduce `Pl _ TT _ hP logT ev aT bT nτ lam1 D0 D1 logc logxi a La L m f k N S η b' CT Cev h0 hc hxi hn hTT hnT hD0 hD1 hb hT0 hT1 hCT hL hLa hl0 hl1 hm1 hmN hk hS hη hb' hcard hev hCev`. Establish `hN1 : 0 ≤ N - 1` using `by linarith`. Establish `hN : 0 ≤ N` using `by linarith`. Establish `hm0 : 0 ≤ m` using `by linarith`. Establish `hmη : 0 ≤ m * η` using `mul_nonneg hm0 hη`.

Establish `hηm : η ≤ m * η` using `by nlinarith`. Establish `hTA : logT ≤ CT * N * La`. Establish `h1 : CT * m * L ≤ CT * m * La` using `mul_le_mul_of_nonneg_left hL (mul_nonneg hCT hm0)`. Establish `h2 : CT * m * La ≤ CT * N * La` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmN hCT) hLa`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hNT : N / 2 * logT ≤ N / 2 * (CT * N * La)` using `mul_le_mul_of_nonneg_left hTA (by linarith)`. Establish `hxi' : ∀ τ, logxi τ ≤ N ^ 2 * La`. Introduce `τ`. Establish `q1 : N * (N - 1) / 2 ≤ N * N / 2` using `by nlinarith`. Establish `q2 : N * (N - 1) / 2 * Real.log (2 * a) ≤ N * N / 2 * (2 * La)` using `mul_le_mul q1 hl1 hl0 (by nlinarith)`.

Use polynomial arithmetic with `[hxi τ]`. Establish `gen : ∀ τ, ∀ B : ℝ, 0 ≤ B → D0 τ ≤ S + m * η + B → D0 τ * logT ≤ (S + m * η + B) * (CT * N * La) ∧ logc τ ≤ N * (4 * S + 4 * (m * η) + 3 * B) * (2 * La)`. Introduce `τ B hB hDB`. Establish `hX : 0 ≤ S + m * η + B` using `by linarith`. Use `⟨(mul_le_mul_of_nonneg_right hDB hT0).trans (mul_le_mul_of_nonneg_left hTA hX), ?_⟩` and prove the remaining obligations.

Establish `hD1' : D1 τ ≤ 3 * (S + m * η + B) + S + η` using `by linarith [hD1 τ]`. Establish `hQ : 0 ≤ 3 * (S + m * η + B) + S + η` using `by linarith`. Establish `q1 : (N - 1) * D1 τ * Real.log (2 * a) ≤ (N - 1) * (3 * (S + m * η + B) + S + η) * Real.log (2 * a)` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1' hN1) hl0`. Establish `q2 : (N - 1) * (3 * (S + m * η + B) + S + η) * Real.log (2 * a) ≤ N * (3 * (S + m * η + B) + S + η) * (2 * La)` using `mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hQ) hl1 hl0 (mul_nonneg hN hQ)`. Establish `q3 : N * (3 * (S + m * η + B) + S + η) * (2 * La) ≤ N * (4 * S + 4 * (m * η) + 3 * B) * (2 * La)` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hN) (by linarith)`.

Combine the linear relations using `[hc τ]`. Establish `key : ∀ τ, -(nτ τ * logT) + (2 * logc τ + logxi τ) ≤ (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) + ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La`. Introduce `τ`. Establish `hD` using `hD0 τ`. Distinguish the cases in `hτ : τ ∈ TT`.

Rewrite `hD`, the goal using `[if_pos hτ]`. Take `⟨e1, e2⟩` from `gen τ b' hb' (by linarith [hb τ hτ])`. Establish `e4 : (N - k) / 2 * logT ≤ N / 2 * logT` using `mul_le_mul_of_nonneg_right (by linarith) hT0`. Rewrite using `[hn τ, hTT τ hτ]`. Combine the linear relations using `[hxi' τ]`.

Rewrite `hD`, the goal using `[if_neg hτ]`. Take `⟨e1, e2⟩` from `gen τ 0 le_rfl (by linarith)`. Establish `e4 : -lam1 τ * logT ≤ N / 2 * logT` using `mul_le_mul_of_nonneg_right (by linarith [hnT τ hτ]) hT0`. Rewrite using `[hn τ]`. Combine the linear relations using `[hxi' τ]`.

Establish `hsum : -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) = ∑ τ, (-(nτ τ * logT) + (2 * logc τ + logxi τ))`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_neg_distrib]`. Establish `hsk` using `Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.univ) => key τ)`. Establish `hsplit : ∑ τ, ((if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) + ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La) = ∑ τ, (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) + (Fintype.card Pl : ℝ) * (((CT + 16) * ((m * η + S) * N) + (CT / …`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Establish `hfilt : Finset.univ.filter (fun τ => τ ∈ TT) = TT`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hite : ∑ τ, (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) = -(∑ t ∈ TT, aT t * logT) + (TT.card : ℝ) * ((CT + 12) * b' * N * La)`. Rewrite using `[← Finset.sum_filter, hfilt, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul]`.

Establish `hf0 : 0 ≤ f` using `le_trans (Nat.cast_nonneg _) hcard`. Establish `hc2 : 0 ≤ ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La`. Establish `: 0 ≤ (CT + 16) * ((m * η + S) * N)` using `mul_nonneg (by linarith) (mul_nonneg (by linarith) hN)`. Establish `: 0 ≤ (CT / 2 + 1) * N ^ 2` using `mul_nonneg (by linarith) (sq_nonneg N)`. Conclude with `mul_nonneg (by linarith) hLa`.

Establish `hcc` using `mul_le_mul_of_nonneg_right hcard hc2`. Establish `hTT0 : (0 : ℝ) ≤ TT.card` using `Nat.cast_nonneg _`. Establish `d1 : 0 ≤ (TT.card : ℝ) * b' * N * La * (4 + Cev)` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hTT0 hb') hN) hLa) (by linarith)`. Establish `d2 : 0 ≤ f * (m * η + S) * N * La * Cev` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 (by linarith)) hN) hLa) hCev`. Establish `d3 : 0 ≤ f * N ^ 2 * La * (15 + CT / 2)` using `mul_nonneg (mul_nonneg (mul_nonneg hf0 (sq_nonneg N)) hLa) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem heightSumBound : BranchSandwichDiii := by
  intro Pl _ TT _ hP logT ev aT bT nτ lam1 D0 D1 logc logxi a La L m f k N S η b' CT Cev
    h0 hc hxi hn hTT hnT hD0 hD1 hb hT0 hT1 hCT hL hLa hl0 hl1 hm1 hmN hk hS hη hb' hcard hev hCev
  have hN1 : 0 ≤ N - 1 := by linarith
  have hN : 0 ≤ N := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hmη : 0 ≤ m * η := mul_nonneg hm0 hη
  have hηm : η ≤ m * η := by nlinarith
  have hTA : logT ≤ CT * N * La := by
    have h1 : CT * m * L ≤ CT * m * La := mul_le_mul_of_nonneg_left hL (mul_nonneg hCT hm0)
    have h2 : CT * m * La ≤ CT * N * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmN hCT) hLa
    linarith
  have hNT : N / 2 * logT ≤ N / 2 * (CT * N * La) := mul_le_mul_of_nonneg_left hTA (by linarith)
  have hxi' : ∀ τ, logxi τ ≤ N ^ 2 * La := by
    intro τ
    have q1 : N * (N - 1) / 2 ≤ N * N / 2 := by nlinarith
    have q2 : N * (N - 1) / 2 * Real.log (2 * a) ≤ N * N / 2 * (2 * La) :=
      mul_le_mul q1 hl1 hl0 (by nlinarith)
    nlinarith [hxi τ]
  have gen : ∀ τ, ∀ B : ℝ, 0 ≤ B → D0 τ ≤ S + m * η + B →
      D0 τ * logT ≤ (S + m * η + B) * (CT * N * La) ∧
        logc τ ≤ N * (4 * S + 4 * (m * η) + 3 * B) * (2 * La) := by
    intro τ B hB hDB
    have hX : 0 ≤ S + m * η + B := by linarith
    refine ⟨(mul_le_mul_of_nonneg_right hDB hT0).trans (mul_le_mul_of_nonneg_left hTA hX), ?_⟩
    have hD1' : D1 τ ≤ 3 * (S + m * η + B) + S + η := by linarith [hD1 τ]
    have hQ : 0 ≤ 3 * (S + m * η + B) + S + η := by linarith
    have q1 : (N - 1) * D1 τ * Real.log (2 * a) ≤
        (N - 1) * (3 * (S + m * η + B) + S + η) * Real.log (2 * a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1' hN1) hl0
    have q2 : (N - 1) * (3 * (S + m * η + B) + S + η) * Real.log (2 * a) ≤
        N * (3 * (S + m * η + B) + S + η) * (2 * La) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hQ) hl1 hl0 (mul_nonneg hN hQ)
    have q3 : N * (3 * (S + m * η + B) + S + η) * (2 * La) ≤
        N * (4 * S + 4 * (m * η) + 3 * B) * (2 * La) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hN) (by linarith)
    linarith [hc τ]
  have key : ∀ τ, -(nτ τ * logT) + (2 * logc τ + logxi τ) ≤
      (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) +
        ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La := by
    intro τ
    have hD := hD0 τ
    by_cases hτ : τ ∈ TT
    · rw [if_pos hτ] at hD ⊢
      obtain ⟨e1, e2⟩ := gen τ b' hb' (by linarith [hb τ hτ])
      have e4 : (N - k) / 2 * logT ≤ N / 2 * logT := mul_le_mul_of_nonneg_right (by linarith) hT0
      rw [hn τ, hTT τ hτ]
      linarith [hxi' τ]
    · rw [if_neg hτ] at hD ⊢
      obtain ⟨e1, e2⟩ := gen τ 0 le_rfl (by linarith)
      have e4 : -lam1 τ * logT ≤ N / 2 * logT :=
        mul_le_mul_of_nonneg_right (by linarith [hnT τ hτ]) hT0
      rw [hn τ]
      linarith [hxi' τ]
  have hsum : -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) =
      ∑ τ, (-(nτ τ * logT) + (2 * logc τ + logxi τ)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hsk := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.univ) => key τ)
  have hsplit : ∑ τ, ((if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) +
        ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La) =
      ∑ τ, (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) +
        (Fintype.card Pl : ℝ) * (((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfilt : Finset.univ.filter (fun τ => τ ∈ TT) = TT := by
    ext x
    simp
  have hite : ∑ τ, (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) =
      -(∑ t ∈ TT, aT t * logT) + (TT.card : ℝ) * ((CT + 12) * b' * N * La) := by
    rw [← Finset.sum_filter, hfilt, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      nsmul_eq_mul]
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hcard
  have hc2 : 0 ≤ ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La := by
    have : 0 ≤ (CT + 16) * ((m * η + S) * N) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hN)
    have : 0 ≤ (CT / 2 + 1) * N ^ 2 := mul_nonneg (by linarith) (sq_nonneg N)
    exact mul_nonneg (by linarith) hLa
  have hcc := mul_le_mul_of_nonneg_right hcard hc2
  have hTT0 : (0 : ℝ) ≤ TT.card := Nat.cast_nonneg _
  have d1 : 0 ≤ (TT.card : ℝ) * b' * N * La * (4 + Cev) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hTT0 hb') hN) hLa) (by linarith)
  have d2 : 0 ≤ f * (m * η + S) * N * La * Cev :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 (by linarith)) hN) hLa) hCev
  have d3 : 0 ≤ f * N ^ 2 * La * (15 + CT / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf0 (sq_nonneg N)) hLa) (by linarith)
  linarith

end Formalism.BranchingDeterminantCap
