import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

/- English proof (translation)
Introduce `W ι _ _ _ w v Y L A C₁ C c φ hC₁ hC hc hφ hL`. Establish `hS0 : 0 ≤ ∑ p, ‖Y p‖ ^ 2` using `Finset.sum_nonneg fun p _ => by positivity`. Take `⟨S, hS⟩ : ∃ S, S = ∑ p, ‖Y p‖ ^ 2` from `⟨_, rfl⟩`. Rewrite `hS0`, the goal using `[← hS]`. Take `⟨D, hD⟩ : ∃ D, D = ‖w‖ ^ 2 + (1 / 4) * S + ‖v‖ ^ 2` from `⟨_, rfl⟩`.

Rewrite using `[← hD]`. Establish `hw2 : 0 ≤ ‖w‖ ^ 2` using `by positivity`. Establish `hv2 : 0 ≤ ‖v‖ ^ 2` using `by positivity`. Establish `hD0 : 0 ≤ D` using `by rw [hD]; positivity`. Establish `hwD : ‖w‖ ^ 2 ≤ D` using `by rw [hD]; linarith`.

Establish `hSD : (1 / 4) * S ≤ D` using `by rw [hD]; linarith`. Establish `hterm : ∀ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))`. Introduce `p`. Establish `hin : |⟪Y p, w⟫_ℝ| ≤ ‖Y p‖ * ‖w‖` using `abs_real_inner_le_norm _ _`. Establish `hmul : |L p * ⟪Y p, w⟫_ℝ| ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))`.

Rewrite using `[abs_mul]`. Establish `h2 : ‖Y p‖ * ‖w‖ ≤ (1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)`. Use polynomial arithmetic with `[sq_nonneg (‖Y p‖ - ‖w‖)]`. Conclude with `mul_le_mul (hL p) (hin.trans h2) (abs_nonneg _) hC₁`. Establish `hle : L p * ⟪Y p, w⟫_ℝ ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))` using `(le_abs_self _).trans hmul`.

Use `mul_le_mul_of_nonneg_left hle (neg_nonneg.2 hc)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : -(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)`. Establish `h1 : ∑ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))` using `Finset.sum_le_sum fun p _ => hterm p`. Establish `h2 : ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) = (-c) * C₁ * ((1 / 2) * (S + (Fintype.card ι : ℝ) * ‖w‖ ^ 2))`.

Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← hS]`. Simplify using `[Finset.card_univ]`. Rewrite `h1` using `[Finset.sum_neg_distrib, h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN0 : (0 : ℝ) ≤ Fintype.card ι` using `Nat.cast_nonneg _`.

Establish `hbr : (1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2 ≤ (1 + (Fintype.card ι : ℝ)) * D`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hwD hN0, mul_nonneg hN0 hw2]`. Establish `hcC : (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2) ≤ (-c) * C * D`. Establish `hnc : 0 ≤ -c` using `neg_nonneg.2 hc`. Combine the equalities or inequalities in the displayed calculation.

Establish `hAv : ⟪A v, w⟫_ℝ ≤ ‖A‖ * ‖v‖ * ‖w‖` using `(real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))`. Establish `hwv : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖` using `real_inner_le_norm _ _`. Establish `hvw : 2 * (‖v‖ * ‖w‖) ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2`. Use polynomial arithmetic with `[sq_nonneg (‖v‖ - ‖w‖)]`. Establish `hvwD : 2 * (‖v‖ * ‖w‖) ≤ D` using `by rw [hD] at *; linarith`.

Establish `hA0 : 0 ≤ ‖A‖` using `norm_nonneg _`. Establish `hbrack : 2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ ≤ (‖A‖ + 1) * D`. Establish `h3 : ‖A‖ * (2 * (‖v‖ * ‖w‖)) ≤ ‖A‖ * D` using `mul_le_mul_of_nonneg_left hvwD hA0`. Use the polynomial consequences of the given equalities and inequalities. Establish `hφ'` using `mul_le_mul_of_nonneg_left hbrack hφ`.

Establish `hrew : (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ = -(-(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ)` using `by ring`. Rewrite using `[hrew]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pointwise_energy_ineq : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  intro W ι _ _ _ w v Y L A C₁ C c φ hC₁ hC hc hφ hL
  have hS0 : 0 ≤ ∑ p, ‖Y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ p, ‖Y p‖ ^ 2 := ⟨_, rfl⟩
  rw [← hS] at hS0 ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ‖w‖ ^ 2 + (1 / 4) * S + ‖v‖ ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hwD : ‖w‖ ^ 2 ≤ D := by rw [hD]; linarith
  have hSD : (1 / 4) * S ≤ D := by rw [hD]; linarith

  have hterm : ∀ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
    intro p
    have hin : |⟪Y p, w⟫_ℝ| ≤ ‖Y p‖ * ‖w‖ := abs_real_inner_le_norm _ _
    have hmul : |L p * ⟪Y p, w⟫_ℝ| ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
      rw [abs_mul]
      have h2 : ‖Y p‖ * ‖w‖ ≤ (1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Y p‖ - ‖w‖)]
      exact mul_le_mul (hL p) (hin.trans h2) (abs_nonneg _) hC₁
    have hle : L p * ⟪Y p, w⟫_ℝ ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      (le_abs_self _).trans hmul
    have := mul_le_mul_of_nonneg_left hle (neg_nonneg.2 hc)
    calc -(c * L p * ⟪Y p, w⟫_ℝ) = (-c) * (L p * ⟪Y p, w⟫_ℝ) := by ring
      _ ≤ (-c) * (C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))) := this
      _ = (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by ring
  have hsum : -(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      ≤ (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2) := by
    have h1 : ∑ p, -(c * L p * ⟪Y p, w⟫_ℝ)
        ≤ ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      Finset.sum_le_sum fun p _ => hterm p
    have h2 : ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))
        = (-c) * C₁ * ((1 / 2) * (S + (Fintype.card ι : ℝ) * ‖w‖ ^ 2)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← hS]
      simp [Finset.card_univ]
    rw [Finset.sum_neg_distrib, h2] at h1
    linarith
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hbr : (1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2
      ≤ (1 + (Fintype.card ι : ℝ)) * D := by
    nlinarith [mul_le_mul_of_nonneg_left hwD hN0, mul_nonneg hN0 hw2]
  have hcC : (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
      ≤ (-c) * C * D := by
    have hnc : 0 ≤ -c := neg_nonneg.2 hc
    calc (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
        ≤ (-c) * C₁ * ((1 + (Fintype.card ι : ℝ)) * D) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hnc hC₁)
      _ = (-c) * (C₁ * (1 + (Fintype.card ι : ℝ))) * D := by ring
      _ ≤ (-c) * C * D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hnc) hD0

  have hAv : ⟪A v, w⟫_ℝ ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))
  have hwv : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
  have hvw : 2 * (‖v‖ * ‖w‖) ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v‖ - ‖w‖)]
  have hvwD : 2 * (‖v‖ * ‖w‖) ≤ D := by rw [hD] at *; linarith
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hbrack : 2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ ≤ (‖A‖ + 1) * D := by
    have h3 : ‖A‖ * (2 * (‖v‖ * ‖w‖)) ≤ ‖A‖ * D := mul_le_mul_of_nonneg_left hvwD hA0
    nlinarith
  have hφ' := mul_le_mul_of_nonneg_left hbrack hφ
  have hrew : (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      = -(-(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ) := by ring
  rw [hrew]
  nlinarith

end GlobalTheory.CompanionTheory.WaveSpd
