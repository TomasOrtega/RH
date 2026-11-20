import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

/- English proof (translation)
Introduce `f N y R2 hf h0 hs`. Establish `hy : ∀ c τ, y c τ ≤ R2` using `fun c τ => le_trans (Finset.single_le_sum (fun i _ => h0 c i) (Finset.mem_univ τ)) (hs c)`. Establish `hP : ∏ τ, ∏ c, y c τ ≤ ∏ _τ : Fin f, ∏ _c : Fin N, R2` using `Finset.prod_le_prod (fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ) (fun τ _ => Finset.prod_le_prod (fun c _ => h0 c τ) (fun c _ => hy c τ))`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hP`. Establish `hP0 : 0 ≤ ∏ τ, ∏ c, y c τ` using `Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem moduli_index_formula : Ms_index := by
  intro f N y R2 hf h0 hs
  have hy : ∀ c τ, y c τ ≤ R2 := fun c τ =>
    le_trans (Finset.single_le_sum (fun i _ => h0 c i) (Finset.mem_univ τ)) (hs c)
  have hP : ∏ τ, ∏ c, y c τ ≤ ∏ _τ : Fin f, ∏ _c : Fin N, R2 :=
    Finset.prod_le_prod (fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ)
      (fun τ _ => Finset.prod_le_prod (fun c _ => h0 c τ) (fun c _ => hy c τ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hP
  have hP0 : 0 ≤ ∏ τ, ∏ c, y c τ := Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ
  calc (∏ τ, ∏ c, y c τ) ^ 2 ≤ ((R2 ^ N) ^ f) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    _ = R2 ^ (2 * f * N) := by rw [← pow_mul, ← pow_mul]; ring_nf

/- English proof (translation)
Introduce `κ lam A bt S hbt hS h0 hl hmid`. Establish `hsucc : ∀ j : Fin (κ + 1), lam j.succ ≤ S`. Introduce `j`. Distinguish the cases in `hj : j.succ = Fin.last (κ + 1)`. Rewrite using `[hj, hl]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hmid j.succ (Fin.succ_ne_zero j) hj).2`. Establish `hsum : ∑ j : Fin (κ + 1), lam j.succ ≤ (κ + 1) * S`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Unfold `wt`. Rewrite using `[Fin.sum_univ_succ, h0]`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `wt plus`. Rewrite using `[Fin.sum_univ_succ, h0, hl]`. Establish `e : ∑ j : Fin (κ + 1), (lam j.succ - -bt) = ∑ j : Fin (κ + 1), lam j.succ + (κ + 1) * bt`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem column_top_entry : LastColumnBound := by
  intro κ lam A bt S hbt hS h0 hl hmid
  have hsucc : ∀ j : Fin (κ + 1), lam j.succ ≤ S := by
    intro j
    by_cases hj : j.succ = Fin.last (κ + 1)
    · rw [hj, hl]; linarith
    · exact (hmid j.succ (Fin.succ_ne_zero j) hj).2
  have hsum : ∑ j : Fin (κ + 1), lam j.succ ≤ (κ + 1) * S := by
    calc ∑ j : Fin (κ + 1), lam j.succ ≤ ∑ _j : Fin (κ + 1), S := Finset.sum_le_sum fun j _ => hsucc j
      _ = (κ + 1) * S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  constructor
  · unfold wt
    rw [Fin.sum_univ_succ, h0]
    nlinarith
  · unfold wt plus
    rw [Fin.sum_univ_succ, h0, hl]
    have e : ∑ j : Fin (κ + 1), (lam j.succ - -bt) = ∑ j : Fin (κ + 1), lam j.succ + (κ + 1) * bt := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    nlinarith

/- English proof (translation)
Introduce `X X' V V' _ _ _ _ K u u' D B hD hB hu hu'`. Establish `hDpos : 0 < D` using `by linarith`. Establish `A1 : ∀ (Y : Type) [Fintype Y] (w : Y → ℝ) (a : Y → ℝ), (∀ y, 1 / D ≤ w y ∧ w y ≤ 1) → (∀ y, 0 ≤ a y) → ∑ y, w y * a y ≤ ∑ y, a y ∧ ∑ y, a y ≤ D * ∑ y, w y * a y`. Introduce `Y _ w a hw ha`. Prove the components needed by the constructor for the conclusion.

Conclude with `Finset.sum_le_sum fun y _ => by`. Use `(hw y).2` as an intermediate fact. Use polynomial arithmetic with `[ha y]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun y _ => by`.

Establish `h1` using `(hw y).1`. Rewrite `h1` using `[div_le_iff₀ hDpos]`. Use polynomial arithmetic with `[ha y]`. Use `⟨fun hK φ => ?_, fun hK φ => ?_⟩` and prove the remaining obligations. Take `⟨h1, _⟩` from `A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)`.

Take `⟨_, h2⟩` from `A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)`. Combine the equalities or inequalities in the displayed calculation. Take `⟨_, h1⟩` from `A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)`. Take `⟨h2, _⟩` from `A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem weight_change_formula : Weight_change := by
  intro X X' V V' _ _ _ _ K u u' D B hD hB hu hu'
  have hDpos : 0 < D := by linarith
  have A1 : ∀ (Y : Type) [Fintype Y] (w : Y → ℝ) (a : Y → ℝ), (∀ y, 1 / D ≤ w y ∧ w y ≤ 1) →
      (∀ y, 0 ≤ a y) → ∑ y, w y * a y ≤ ∑ y, a y ∧ ∑ y, a y ≤ D * ∑ y, w y * a y := by
    intro Y _ w a hw ha
    constructor
    · exact Finset.sum_le_sum fun y _ => by
        have := (hw y).2
        nlinarith [ha y]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => by
        have h1 := (hw y).1
        rw [div_le_iff₀ hDpos] at h1
        nlinarith [ha y]
  refine ⟨fun hK φ => ?_, fun hK φ => ?_⟩
  · obtain ⟨h1, _⟩ := A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)
    obtain ⟨_, h2⟩ := A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)
    calc ∑ x, u' x * ‖K φ x‖ ^ 2 ≤ ∑ x, ‖K φ x‖ ^ 2 := h1
      _ ≤ B * ∑ x, ‖φ x‖ ^ 2 := hK φ
      _ ≤ B * (D * ∑ x, u x * ‖φ x‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hB
      _ = (B * D) * ∑ x, u x * ‖φ x‖ ^ 2 := by ring
  · obtain ⟨_, h1⟩ := A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)
    obtain ⟨h2, _⟩ := A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)
    calc ∑ x, ‖K φ x‖ ^ 2 ≤ D * ∑ x, u' x * ‖K φ x‖ ^ 2 := h1
      _ ≤ D * (B * ∑ x, u x * ‖φ x‖ ^ 2) := mul_le_mul_of_nonneg_left (hK φ) hDpos.le
      _ ≤ D * (B * ∑ x, ‖φ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB) hDpos.le
      _ = (B * D) * ∑ x, ‖φ x‖ ^ 2 := by ring

/- English proof (translation)
Introduce `f g u v hf hv hu`. Establish `hfR : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hfv : 0 < (f : ℝ) / v` using `div_pos (by linarith) hv`. Use `set t := 2 * Real.sqrt u / Real.sqrt (f / v) with ht`. Establish `ht2 : t ^ 2 = 4 * u * v / f`.

Rewrite using `[ht, div_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hfv.le]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `huv : 0 ≤ 4 * u * v` using `by positivity`. Establish `ht2' : t ^ 2 ≤ 4 * u * v`.

Rewrite using `[ht2]`. Conclude with `div_le_self huv hfR`. Establish `key : (1 + t) ^ 2 ≤ 2 * (1 + 4 * u * v)` using `by nlinarith [sq_nonneg (1 - t)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem first_zeta_count : PackingCountBound := by
  intro f g u v hf hv hu
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hfv : 0 < (f : ℝ) / v := div_pos (by linarith) hv
  set t := 2 * Real.sqrt u / Real.sqrt (f / v) with ht
  have ht2 : t ^ 2 = 4 * u * v / f := by
    rw [ht, div_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hfv.le]
    field_simp
    ring
  have huv : 0 ≤ 4 * u * v := by positivity
  have ht2' : t ^ 2 ≤ 4 * u * v := by
    rw [ht2]; exact div_le_self huv hfR
  have key : (1 + t) ^ 2 ≤ 2 * (1 + 4 * u * v) := by nlinarith [sq_nonneg (1 - t)]
  calc (1 + t) ^ (2 * g) = ((1 + t) ^ 2) ^ g := pow_mul _ _ _
    _ ≤ (2 * (1 + 4 * u * v)) ^ g := pow_le_pow_left₀ (sq_nonneg _) key g
    _ = 2 ^ g * (1 + 4 * u * v) ^ g := mul_pow _ _ _

/- English proof (translation)
Introduce `n lam nu`. Unfold `degZ Formalism.LogVandermondeBounds.flipTwoThree.B0`. Rewrite using `[Fin.sum_univ_succ, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem third_zeta_degree_bound : DegreeEqHeadMinusBalance := by
  intro n lam nu
  unfold degZ Formalism.LogVandermondeBounds.flipTwoThree.B0
  rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Introduce `n lam nu X _`. Rewrite using `[← Finset.sum_add_sum_compl X (fun i => min (len lam i) (B0 lam nu))]`. Establish `h1 : ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ X.card * B0 lam nu`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∑ i ∈ Xᶜ, min (len lam i) (B0 lam nu) ≤ ∑ i ∈ Xᶜ, len lam i` using `Finset.sum_le_sum fun i _ => min_le_left _ _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem third_zeta_position_count : CoordinatesBoundedByBalance := by
  intro n lam nu X _
  rw [← Finset.sum_add_sum_compl X (fun i => min (len lam i) (B0 lam nu))]
  have h1 : ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ X.card * B0 lam nu := by
    calc ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ ∑ _i ∈ X, B0 lam nu :=
          Finset.sum_le_sum fun i _ => min_le_right _ _
      _ = X.card * B0 lam nu := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Xᶜ, min (len lam i) (B0 lam nu) ≤ ∑ i ∈ Xᶜ, len lam i :=
    Finset.sum_le_sum fun i _ => min_le_left _ _
  linarith

/- English proof (translation)
Introduce `f k v l1 ln hf hv hl1 hln h hl`. Establish `hfR : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hv2 : 0 < (2 * v) ^ 2` using `by positivity`. Establish `h1 : (ln * l1) ^ 2 ≤ (2 * f * k) ^ 2` using `pow_le_pow_left₀ (mul_nonneg hln hl1) h 2`. Establish `h2 : ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2` using `mul_le_mul_of_nonneg_left hl (sq_nonneg _)`.

Establish `h3 : ln ^ 2 * (f : ℝ) / (2 * v) ^ 2 ≤ 4 * f ^ 2 * k ^ 2`. Rewrite using `[mul_div_assoc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h3` using `[div_le_iff₀ hv2]`. Establish `hf0 : (0 : ℝ) < f` using `by linarith`.

Use `le_of_mul_le_mul_right ?_ hf0` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fifth_zeta_transference : LastMinimumSqBoundOfProductBound := by
  intro f k v l1 ln hf hv hl1 hln h hl
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hv2 : 0 < (2 * v) ^ 2 := by positivity
  have h1 : (ln * l1) ^ 2 ≤ (2 * f * k) ^ 2 := pow_le_pow_left₀ (mul_nonneg hln hl1) h 2
  have h2 : ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2 := mul_le_mul_of_nonneg_left hl (sq_nonneg _)
  have h3 : ln ^ 2 * (f : ℝ) / (2 * v) ^ 2 ≤ 4 * f ^ 2 * k ^ 2 := by
    rw [mul_div_assoc]
    calc ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2 := h2
      _ = (ln * l1) ^ 2 := by ring
      _ ≤ (2 * f * k) ^ 2 := h1
      _ = 4 * f ^ 2 * k ^ 2 := by ring
  rw [div_le_iff₀ hv2] at h3
  have hf0 : (0 : ℝ) < f := by linarith
  refine le_of_mul_le_mul_right ?_ hf0
  calc ln ^ 2 * (f : ℝ) ≤ 4 * f ^ 2 * k ^ 2 * (2 * v) ^ 2 := h3
    _ = 16 * f * (k : ℝ) ^ 2 * v ^ 2 * f := by ring

/- English proof (translation)
Introduce `C₀ L logT logg b' m N hC hL hm hT hg hb`. Establish `hmR : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hL0 : 0 ≤ L` using `by linarith`. Establish `h1 : L ≤ m * L` using `by nlinarith`. Establish `h2 : C₀ * L ≤ C₀ * m * L` using `by nlinarith [mul_nonneg hC hL0]`.

Establish `hs : L + logT + logg ≤ (1 + 2 * C₀) * m * L` using `by nlinarith`. Establish `hmN : 0 ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2` using `by positivity`. Establish `hNL : 0 ≤ (N : ℝ) * L` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem square_moment_from_bound : Sqm_from := by
  intro C₀ L logT logg b' m N hC hL hm hT hg hb
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : 0 ≤ L := by linarith
  have h1 : L ≤ m * L := by nlinarith
  have h2 : C₀ * L ≤ C₀ * m * L := by nlinarith [mul_nonneg hC hL0]
  have hs : L + logT + logg ≤ (1 + 2 * C₀) * m * L := by nlinarith
  have hmN : 0 ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 := by positivity
  have hNL : 0 ≤ (N : ℝ) * L := by positivity
  calc (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * ((1 + 2 * C₀) * m * L) :=
        mul_le_mul_of_nonneg_left hs hmN
    _ = (N * L) * ((1 + 2 * C₀) * (m : ℝ) ^ 3 * N) := by ring
    _ ≤ (N * L) * b' := mul_le_mul_of_nonneg_left hb hNL
    _ = N * b' * L := by ring

end Formalism.HermitianLattices.TraceIntegrality
