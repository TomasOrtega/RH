import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

open Finset in
open scoped InnerProductSpace in
/- English proof (translation)
The claim follows from `|((s.card : ℝ) - (t.card : ℝ)) / 2| ≤ n := by have hs : (s.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin n) have ht : (t.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ t).trans_eq (Fintype.card_fin n) have hs0 : (0 : ℝ) ≤ s.card := …`.
-/
private lemma abs_half_card_sub_le {n : ℕ} (s t : Finset (Fin n)) :
    |((s.card : ℝ) - (t.card : ℝ)) / 2| ≤ n := by
  have hs : (s.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin n)
  have ht : (t.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ t).trans_eq (Fintype.card_fin n)
  have hs0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t.card := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

open Finset in
open scoped InnerProductSpace in
/- English proof (translation)
Simplify using `[LinearMap.sum_apply, inner_sum, Complex.re_sum]`.
-/
private lemma re_inner_double_sum_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M) (w : M) :
    (⟪w, (∑ a, ∑ b, F a b) w⟫_ℂ).re = ∑ a, ∑ b, (⟪w, F a b w⟫_ℂ).re := by
  simp [LinearMap.sum_apply, inner_sum, Complex.re_sum]

open Finset in
open scoped InnerProductSpace in
/- English proof (translation)
Establish `h` using `hE b a w (E b a w)`. Unfold `_root_.Formalism.REAL.sgn at h`. Establish `hn : ‖E b a w‖ ^ 2 = (⟪E b a w, E b a w⟫_ℂ).re`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ)]`. Both sides reduce to the same expression.

Rewrite using `[hn, h, Module.End.mul_apply]`. Distinguish the cases in `hab : ε a = ε b`. Rewrite using `[if_pos hab.symm, if_pos hab]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg (fun h' => hab h'.symm), if_neg hab]`. Simplify using the standard rewrite rules.
-/
private lemma norm_sq_apply_eq_re_inner_of_isUnitary {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : _root_.Formalism.REAL.IsUnitary ε E) (a b : Fin n) (w : M) :
    ‖E b a w‖ ^ 2 = (if ε a = ε b then 2 * (⟪w, (E a b * E b a) w⟫_ℂ).re else 0)
      - (⟪w, (E a b * E b a) w⟫_ℂ).re := by
  have h := hE b a w (E b a w)
  unfold _root_.Formalism.REAL.sgn at h
  have hn : ‖E b a w‖ ^ 2 = (⟪E b a w, E b a w⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
  rw [hn, h, Module.End.mul_apply]
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab]; simp; ring
  · rw [if_neg (fun h' => hab h'.symm), if_neg hab]; simp

open Finset in
open scoped InnerProductSpace in
/- English proof (translation)
Establish `hN1 : (1 : ℝ) ≤ n` using `by linarith`. Establish `hN0 : (0 : ℝ) ≤ n` using `by linarith`. Establish `hJ0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Establish `h7 : ∀ k ≤ 7, (n : ℝ) ^ k ≤ (n : ℝ) ^ 7` using `fun k hk => pow_le_pow_right₀ hN1 hk`. Establish `hn7 : (1 : ℝ) ≤ (n : ℝ) ^ 7` using `one_le_pow₀ hN1`.

Establish `hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2` using `by nlinarith`. Establish `hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2` using `by nlinarith`. Establish `hbv1 : 30 * (n : ℝ) ^ 2 ≤ bv` using `by linarith [h7 2 (by norm_num)]`. Establish `hnb : (n : ℝ) ≤ bv` using `by linarith [h7 1 (by norm_num), pow_one (n : ℝ)]`. Establish `hbv0 : 0 ≤ bv` using `by linarith`.

Establish `hbvone : 1 ≤ bv` using `by linarith`. Establish `hJ5 : (j : ℝ) ≤ 5 * (n : ℝ) ^ 2` using `by linarith`. Establish `hT2 : 0 ≤ ∑ a, T a ^ 2` using `Finset.sum_nonneg fun a _ => sq_nonneg _`. Establish `hA2 : 0 ≤ ∑ a, (μ a + U a) ^ 2` using `Finset.sum_nonneg fun a _ => sq_nonneg _`. Establish `hAbound : ∑ a, (μ a + U a) ^ 2 ≤ (4 * n * bv) ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Establish `h1 : |μ a + U a| ≤ 4 * bv` using `(abs_add_le _ _).trans (by linarith [hμ a, hU a])`. Combine the equalities or inequalities in the displayed calculation. Use `_ = (n : ℝ) * (4 * bv) ^ 2 := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `_ ≤ (4 * n * bv) ^ 2 := by`. Use `mul_le_mul_of_nonneg_right hnsq (sq_nonneg (4 * bv))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : √K ^ 2 ≤ K + ∑ a, T a ^ 2`.

Break down `le_or_gt 0 K with h | h` into its components or cases. Rewrite using `[Real.sq_sqrt h]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.sqrt_eq_zero'.mpr h.le, hK]`. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsqrt : √K ≤ 4 * n * bv`. Combine the equalities or inequalities in the displayed calculation. Establish `hsqrt0 : 0 ≤ √K` using `Real.sqrt_nonneg _`. Establish `hpt : ∀ a, 2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2 ≤ 12 * n * bv + 4 * (n : ℝ) ^ 2`.

Introduce `a`. Establish `e1 : μ a * U a ≤ 3 * bv * n` using `(le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul (hμ a) (hU a) (abs_nonneg _) (by linarith))`. Establish `e2 : μ a * T a ≤ 3 * bv * n` using `(le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul (hμ a) (hT a) (abs_nonneg _) (by linarith))`. Establish `e3 : U a * T a ≤ n * n` using `(le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul (hU a) (hT a) (abs_nonneg _) hN0)`. Establish `e4 : U a ^ 2 ≤ (n : ℝ) ^ 2`.

Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hU a) 2`. Establish `e5 : ρ a ^ 2 ≤ (n : ℝ) ^ 2`. Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hρ a) 2`.

Combine the linear relations using `[sq_nonneg (T a)]`. Establish `hsumid : 2 * K + 2 * ∑ a, T a ^ 2 - c - ∑ a, L a ^ 2 = ∑ a, (2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2)`. Rewrite using `[hK, hc]`. Simplify using `only [hL, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsumle : ∑ a, (2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2) ≤ (n : ℝ) * (12 * n * bv + 4 * (n : ℝ) ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hcross : 16 * n * j * √K ≤ 16 * n * j * (4 * n * bv)` using `mul_le_mul_of_nonneg_left hsqrt (by positivity)`. Establish `hX : 2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j) ≤ (n : ℝ) * (12 * n * bv + 4 * (n : ℝ) ^ 2) + 64 * (n : ℝ) ^ 2 * j * bv + 32 * (n : ℝ) ^ 2 * (j : ℝ) ^ 2 + 8 * bv * j`. Combine the linear relations using `[hsq, hsumid, hsumle, hcross]`.

Establish `b1 : 64 * (n : ℝ) ^ 2 * j * bv ≤ 320 * (n : ℝ) ^ 4 * bv`. Use `mul_le_mul_of_nonneg_left hJ5 (by positivity : (0 : ℝ) ≤ 64 * (n : ℝ) ^ 2 * bv)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b2 : 32 * (n : ℝ) ^ 2 * (j : ℝ) ^ 2 ≤ 800 * (n : ℝ) ^ 6`. Establish `h1 : (j : ℝ) ^ 2 ≤ (5 * (n : ℝ) ^ 2) ^ 2` using `pow_le_pow_left₀ hJ0 hJ5 2`.

Use `mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b3 : 8 * bv * j ≤ 40 * (n : ℝ) ^ 2 * bv`. Use `mul_le_mul_of_nonneg_left hJ5 hbv0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hX' : 2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j) ≤ 52 * (n : ℝ) ^ 2 * bv + 4 * (n : ℝ) ^ 3 + 320 * (n : ℝ) ^ 4 * bv + 800 * (n : ℝ) ^ 6` using `by linarith`. Establish `c1 : (n : ℝ) ^ 3 * bv ≤ (n : ℝ) ^ 7 * bv` using `mul_le_mul_of_nonneg_right (h7 3 (by norm_num)) hbv0`. Establish `c2 : (n : ℝ) ^ 5 * bv ≤ (n : ℝ) ^ 7 * bv` using `mul_le_mul_of_nonneg_right (h7 5 (by norm_num)) hbv0`. Establish `c3 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 7` using `h7 4 (by norm_num)`. Establish `c4 : (n : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 * bv` using `le_mul_of_one_le_right (by positivity) hbvone`.

Establish `c6 : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 7` using `h7 6 (by norm_num)`. Establish `c5 : 10 ^ 6 * (n : ℝ) ^ 7 * bv ≤ bv * bv` using `mul_le_mul_of_nonneg_right hbv hbv0`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma mul_sq_sqrt_sub_le_sq_div_sixteen {n : ℕ} (μ U T ρ L : Fin n → ℝ) (K c bv : ℝ) (j : ℕ)
    (hμ : ∀ a, |μ a| ≤ 3 * bv) (hU : ∀ a, |U a| ≤ n) (hT : ∀ a, |T a| ≤ n)
    (hρ : ∀ a, |ρ a| ≤ n) (hL : ∀ a, L a = μ a + U a - T a)
    (hK : K = ∑ a, (μ a + U a) ^ 2 - ∑ a, T a ^ 2) (hc : c = ∑ a, μ a ^ 2 - ∑ a, ρ a ^ 2)
    (hn : (2 : ℝ) ≤ n) (hbv : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) (hj : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2) :
    (n : ℝ) * (2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j)) ≤ (bv / 16) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hN0 : (0 : ℝ) ≤ n := by linarith
  have hJ0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h7 : ∀ k ≤ 7, (n : ℝ) ^ k ≤ (n : ℝ) ^ 7 := fun k hk => pow_le_pow_right₀ hN1 hk
  have hn7 : (1 : ℝ) ≤ (n : ℝ) ^ 7 := one_le_pow₀ hN1
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hbv1 : 30 * (n : ℝ) ^ 2 ≤ bv := by linarith [h7 2 (by norm_num)]
  have hnb : (n : ℝ) ≤ bv := by linarith [h7 1 (by norm_num), pow_one (n : ℝ)]
  have hbv0 : 0 ≤ bv := by linarith
  have hbvone : 1 ≤ bv := by linarith
  have hJ5 : (j : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by linarith
  have hT2 : 0 ≤ ∑ a, T a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hA2 : 0 ≤ ∑ a, (μ a + U a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hAbound : ∑ a, (μ a + U a) ^ 2 ≤ (4 * n * bv) ^ 2 := by
    calc ∑ a, (μ a + U a) ^ 2 ≤ ∑ _a : Fin n, (4 * bv) ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h1 : |μ a + U a| ≤ 4 * bv :=
            (abs_add_le _ _).trans (by linarith [hμ a, hU a])
          calc (μ a + U a) ^ 2 = |μ a + U a| ^ 2 := (sq_abs _).symm
            _ ≤ (4 * bv) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (n : ℝ) * (4 * bv) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (4 * n * bv) ^ 2 := by
          have := mul_le_mul_of_nonneg_right hnsq (sq_nonneg (4 * bv))
          linarith
  have hsq : √K ^ 2 ≤ K + ∑ a, T a ^ 2 := by
    rcases le_or_gt 0 K with h | h
    · rw [Real.sq_sqrt h]; linarith
    · rw [Real.sqrt_eq_zero'.mpr h.le, hK]; norm_num; linarith
  have hsqrt : √K ≤ 4 * n * bv := by
    calc √K ≤ √((4 * n * bv) ^ 2) := Real.sqrt_le_sqrt (by rw [hK]; linarith)
      _ = 4 * n * bv := Real.sqrt_sq (by positivity)
  have hsqrt0 : 0 ≤ √K := Real.sqrt_nonneg _
  have hpt : ∀ a, 2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2
      ≤ 12 * n * bv + 4 * (n : ℝ) ^ 2 := by
    intro a
    have e1 : μ a * U a ≤ 3 * bv * n := (le_abs_self _).trans
      (by rw [abs_mul]; exact mul_le_mul (hμ a) (hU a) (abs_nonneg _) (by linarith))
    have e2 : μ a * T a ≤ 3 * bv * n := (le_abs_self _).trans
      (by rw [abs_mul]; exact mul_le_mul (hμ a) (hT a) (abs_nonneg _) (by linarith))
    have e3 : U a * T a ≤ n * n := (le_abs_self _).trans
      (by rw [abs_mul]; exact mul_le_mul (hU a) (hT a) (abs_nonneg _) hN0)
    have e4 : U a ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hU a) 2
    have e5 : ρ a ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hρ a) 2
    linarith [sq_nonneg (T a)]
  have hsumid : 2 * K + 2 * ∑ a, T a ^ 2 - c - ∑ a, L a ^ 2
      = ∑ a, (2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2) := by
    rw [hK, hc]
    simp only [hL, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hsumle : ∑ a, (2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2)
      ≤ (n : ℝ) * (12 * n * bv + 4 * (n : ℝ) ^ 2) := by
    calc _ ≤ ∑ _a : Fin n, (12 * n * bv + 4 * (n : ℝ) ^ 2) := Finset.sum_le_sum fun a _ => hpt a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcross : 16 * n * j * √K ≤ 16 * n * j * (4 * n * bv) :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hX : 2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j)
      ≤ (n : ℝ) * (12 * n * bv + 4 * (n : ℝ) ^ 2) + 64 * (n : ℝ) ^ 2 * j * bv
        + 32 * (n : ℝ) ^ 2 * (j : ℝ) ^ 2 + 8 * bv * j := by
    linarith [hsq, hsumid, hsumle, hcross]
  have b1 : 64 * (n : ℝ) ^ 2 * j * bv ≤ 320 * (n : ℝ) ^ 4 * bv := by
    have := mul_le_mul_of_nonneg_left hJ5 (by positivity : (0 : ℝ) ≤ 64 * (n : ℝ) ^ 2 * bv)
    linarith
  have b2 : 32 * (n : ℝ) ^ 2 * (j : ℝ) ^ 2 ≤ 800 * (n : ℝ) ^ 6 := by
    have h1 : (j : ℝ) ^ 2 ≤ (5 * (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hJ0 hJ5 2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2)
    linarith
  have b3 : 8 * bv * j ≤ 40 * (n : ℝ) ^ 2 * bv := by
    have := mul_le_mul_of_nonneg_left hJ5 hbv0
    linarith
  have hX' : 2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j)
      ≤ 52 * (n : ℝ) ^ 2 * bv + 4 * (n : ℝ) ^ 3 + 320 * (n : ℝ) ^ 4 * bv
        + 800 * (n : ℝ) ^ 6 := by linarith
  have c1 : (n : ℝ) ^ 3 * bv ≤ (n : ℝ) ^ 7 * bv :=
    mul_le_mul_of_nonneg_right (h7 3 (by norm_num)) hbv0
  have c2 : (n : ℝ) ^ 5 * bv ≤ (n : ℝ) ^ 7 * bv :=
    mul_le_mul_of_nonneg_right (h7 5 (by norm_num)) hbv0
  have c3 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 7 := h7 4 (by norm_num)
  have c4 : (n : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 * bv := le_mul_of_one_le_right (by positivity) hbvone
  have c6 : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 7 := h7 6 (by norm_num)
  have c5 : 10 ^ 6 * (n : ℝ) ^ 7 * bv ≤ bv * bv := mul_le_mul_of_nonneg_right hbv hbv0
  calc (n : ℝ) * (2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j))
      ≤ (n : ℝ) * (52 * (n : ℝ) ^ 2 * bv + 4 * (n : ℝ) ^ 3 + 320 * (n : ℝ) ^ 4 * bv
        + 800 * (n : ℝ) ^ 6) := mul_le_mul_of_nonneg_left hX' hN0
    _ = 52 * ((n : ℝ) ^ 3 * bv) + 4 * (n : ℝ) ^ 4 + 320 * ((n : ℝ) ^ 5 * bv)
        + 800 * (n : ℝ) ^ 7 := by ring
    _ ≤ (bv / 16) ^ 2 := by linarith

open Finset in
open scoped InnerProductSpace in

/- English proof (translation)
Introduce `M _ _ n ε E μ kk j bv w hmod hshape hj hlev`. Unfold `_root_.BranchingSupport.IsMod at hmod`. Take `⟨-, hE, hcas⟩` from `hmod`. Unfold `_root_.BranchingSupport.Lev _root_.BranchingSupport.CasKLe at hlev`. Take `⟨⟨S, -, -, hwS, hS⟩, hnear⟩` from `hlev`.

Unfold `_root_.BranchingSupport.Shape at hshape`. Take `⟨hkk1, hkkn, -, hlow, hhigh, hbv⟩` from `hshape`. Establish `hn : 2 ≤ n` using `by omega`. Establish `hNR : (2 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hN7 : (1 : ℝ) ≤ (n : ℝ) ^ 7` using `one_le_pow₀ (by linarith)`.

Establish `hbv0 : 0 ≤ bv` using `by linarith`. Establish `hnb : 2 * (n : ℝ) ≤ bv`. Establish `: (n : ℝ) ≤ (n : ℝ) ^ 7`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hμ : ∀ a, |μ a| ≤ 3 * bv`. Introduce `a`. Break down `lt_or_ge ((a : ℕ) + 1) kk with h | h` into its components or cases. Take `⟨-, h1, h2⟩` from `hlow a h`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`.

Take `⟨h1, h2⟩` from `hhigh a h`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Establish `hU : ∀ a, |_root_.Formalism.REAL.rhoN ε a| ≤ n` using `fun a => by`. Unfold `_root_.Formalism.REAL.rhoN`. Conclude with `abs_half_card_sub_le _ _`.

Establish `hT : ∀ a, |_root_.Formalism.REAL.rhoC ε a| ≤ n` using `fun a => by`. Unfold `_root_.Formalism.REAL.rhoC`. Conclude with `abs_half_card_sub_le _ _`. Establish `hρ : ∀ a, |_root_.Formalism.QuantumDeterminants.rhoStd n a| ≤ n`. Introduce `a`.

Unfold `_root_.Formalism.QuantumDeterminants.rhoStd`. Establish `ha : ((a : ℕ) : ℝ) + 1 ≤ n` using `by exact_mod_cast a.isLt`. Establish `ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Establish `hLeq : ∀ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a = μ a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a` using `fun a => by`.

Unfold `_root_.Formalism.QuantumDeterminants.lowK`. Simplify using the standard rewrite rules. Establish `hLb : ∀ a, |_root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ 4 * bv`. Introduce `a`. Establish `h1` using `hμ a`.

Establish `h2` using `hU a`. Establish `h3` using `hT a`. Apply the tactic sequence `rw [hLeq]; rw [abs_le] at h1 h2 h3 ⊢; constructor <;> linarith`. Establish `hm : ∀ ω : Fin n → ℝ, ∑ a, |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ (j : ℝ) → ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j ≤ ∑ a, ω a ^ 2`. Introduce `ω hω`.

Establish `hpt : ∀ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ ω a ^ 2`. Introduce `a`. Establish `h1` using `neg_abs_le (_root_.Formalism.QuantumDeterminants.lowK ε μ a * (ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a))`. Rewrite `h1` using `[abs_mul]`. Establish `h2 : |_root_.Formalism.QuantumDeterminants.lowK ε μ a| * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ 4 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a|` using `mul_le_mul_of_nonneg_right (hLb a) (abs_nonneg _)`.

Combine the linear relations using `[sq_nonneg (ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a)]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left hω hbv0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ∑ a, (_root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a|) := by`.

Rewrite using `[Finset.mul_sum, Finset.sum_sub_distrib]`. Use `_ ≤ ∑ a, ω a ^ 2 := Finset.sum_le_sum fun a _ => hpt a`. Establish `hdiag : (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j) * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2` using `(_root_.GlobalTheory.wtNear_diag_bounds M n ε E (_root_.Formalism.QuantumDeterminants.lowK ε μ) (j : ℝ) w hE hnear).1 _ hm`. Establish `hΩ : (⟪w, _root_.Formalism.REAL.Cas E w⟫_ℂ).re = _root_.BranchingSupport.casG μ * ‖w‖ ^ 2`. Rewrite using `[hcas w, inner_smul_right, inner_self_eq_norm_sq_to_K]`.

Use `norm_cast`. Rewrite using `[Complex.re_ofReal_mul]`. Use `congr 1`. Establish `hKc` using `hS w hwS`. Establish `hsum : ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (⟪w, _root_.Formalism.REAL.CasK ε E w⟫_ℂ).re - (⟪w, _root_.Formalism.REAL.Cas E w⟫_ℂ).re`.

Rewrite using `[Finset.sum_comm]`. Unfold `_root_.Formalism.REAL.CasK _root_.Formalism.REAL.Cas`. Rewrite using `[re_inner_double_sum_apply, re_inner_double_sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_sq_apply_eq_re_inner_of_isUnitary hE a b w]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hoff : ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 = ∑ a, ∑ b, ‖E a b w‖ ^ 2 - ∑ a, ‖E a a w‖ ^ 2`. Rewrite using `[← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_erase_eq_sub (Finset.mem_univ a)`. Establish `hKeq : _root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ) = ∑ a, (μ a + _root_.Formalism.REAL.rhoN ε a) ^ 2 - ∑ a, _root_.Formalism.REAL.rhoC ε a ^ 2`. Unfold `_root_.Formalism.REAL.ckv _root_.Formalism.REAL.nsq _root_.Formalism.REAL.dot _root_.Formalism.QuantumDeterminants.lowK`. Simplify using `only [Pi.add_apply, Pi.sub_apply, sub_add_cancel, sq]`. Establish `hceq : _root_.BranchingSupport.casG μ = ∑ a, μ a ^ 2 - ∑ a, _root_.Formalism.QuantumDeterminants.rhoStd n a ^ 2`.

Unfold `_root_.BranchingSupport.casG`. Both sides reduce to the same expression. Establish `hj' : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2` using `by exact_mod_cast hj`. Establish `hnum` using `mul_sq_sqrt_sub_le_sq_div_sixteen μ (_root_.Formalism.REAL.rhoN ε) (_root_.Formalism.REAL.rhoC ε) (fun a => _root_.Formalism.QuantumDeterminants.rhoStd n a) (_root_.Formalism.QuantumDeterminants.lowK ε μ) (_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ …`. Establish `hw2 : 0 ≤ ‖w‖ ^ 2` using `by positivity`.

Establish `hoff_le : ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2 - _root_.BranchingSupport.casG μ - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2`. Rewrite using `[hoff, hsum, hΩ]`. Combine the linear relations using `[hKc, hdiag]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hnum hw2`.
-/
theorem _root_.GlobalTheory.lev_offDiag_normSq_le : ∀ (M : Type) [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), _root_.BranchingSupport.IsMod ε E μ →
    _root_.BranchingSupport.Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 →
    _root_.BranchingSupport.Lev ε E μ j w →
    (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv w hmod hshape hj hlev
  unfold _root_.BranchingSupport.IsMod at hmod
  obtain ⟨-, hE, hcas⟩ := hmod
  unfold _root_.BranchingSupport.Lev _root_.BranchingSupport.CasKLe at hlev
  obtain ⟨⟨S, -, -, hwS, hS⟩, hnear⟩ := hlev
  unfold _root_.BranchingSupport.Shape at hshape
  obtain ⟨hkk1, hkkn, -, hlow, hhigh, hbv⟩ := hshape
  have hn : 2 ≤ n := by omega
  have hNR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN7 : (1 : ℝ) ≤ (n : ℝ) ^ 7 := one_le_pow₀ (by linarith)
  have hbv0 : 0 ≤ bv := by linarith
  have hnb : 2 * (n : ℝ) ≤ bv := by
    have : (n : ℝ) ≤ (n : ℝ) ^ 7 := by
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hμ : ∀ a, |μ a| ≤ 3 * bv := by
    intro a
    rcases lt_or_ge ((a : ℕ) + 1) kk with h | h
    · obtain ⟨-, h1, h2⟩ := hlow a h
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hhigh a h
      rw [abs_le]; constructor <;> linarith
  have hU : ∀ a, |_root_.Formalism.REAL.rhoN ε a| ≤ n := fun a => by
    unfold _root_.Formalism.REAL.rhoN; exact abs_half_card_sub_le _ _
  have hT : ∀ a, |_root_.Formalism.REAL.rhoC ε a| ≤ n := fun a => by
    unfold _root_.Formalism.REAL.rhoC; exact abs_half_card_sub_le _ _
  have hρ : ∀ a, |_root_.Formalism.QuantumDeterminants.rhoStd n a| ≤ n := by
    intro a
    unfold _root_.Formalism.QuantumDeterminants.rhoStd
    have ha : ((a : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast a.isLt
    have ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  have hLeq : ∀ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a = μ a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := fun a => by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  have hLb : ∀ a, |_root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ 4 * bv := by
    intro a
    have h1 := hμ a; have h2 := hU a; have h3 := hT a
    rw [hLeq]; rw [abs_le] at h1 h2 h3 ⊢; constructor <;> linarith
  have hm : ∀ ω : Fin n → ℝ, ∑ a, |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ (j : ℝ) →
      ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j ≤ ∑ a, ω a ^ 2 := by
    intro ω hω
    have hpt : ∀ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ ω a ^ 2 := by
      intro a
      have h1 := neg_abs_le (_root_.Formalism.QuantumDeterminants.lowK ε μ a * (ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a))
      rw [abs_mul] at h1
      have h2 : |_root_.Formalism.QuantumDeterminants.lowK ε μ a| * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ 4 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| :=
        mul_le_mul_of_nonneg_right (hLb a) (abs_nonneg _)
      linarith [sq_nonneg (ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a)]
    calc ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j
        ≤ ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * ∑ a, |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| := by
          have := mul_le_mul_of_nonneg_left hω hbv0
          linarith
      _ = ∑ a, (_root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a|) := by
          rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ a, ω a ^ 2 := Finset.sum_le_sum fun a _ => hpt a
  have hdiag : (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j) * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2 :=
    (_root_.GlobalTheory.wtNear_diag_bounds M n ε E (_root_.Formalism.QuantumDeterminants.lowK ε μ) (j : ℝ) w hE hnear).1 _ hm
  have hΩ : (⟪w, _root_.Formalism.REAL.Cas E w⟫_ℂ).re = _root_.BranchingSupport.casG μ * ‖w‖ ^ 2 := by
    rw [hcas w, inner_smul_right, inner_self_eq_norm_sq_to_K]
    norm_cast
    rw [Complex.re_ofReal_mul]
    congr 1
  have hKc := hS w hwS
  have hsum : ∑ a, ∑ b, ‖E a b w‖ ^ 2
      = 2 * (⟪w, _root_.Formalism.REAL.CasK ε E w⟫_ℂ).re - (⟪w, _root_.Formalism.REAL.Cas E w⟫_ℂ).re := by
    rw [Finset.sum_comm]
    unfold _root_.Formalism.REAL.CasK _root_.Formalism.REAL.Cas
    rw [re_inner_double_sum_apply, re_inner_double_sum_apply, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [norm_sq_apply_eq_re_inner_of_isUnitary hE a b w]
    split_ifs <;> simp
  have hoff : ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2
      = ∑ a, ∑ b, ‖E a b w‖ ^ 2 - ∑ a, ‖E a a w‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_erase_eq_sub (Finset.mem_univ a)
  have hKeq : _root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)
      = ∑ a, (μ a + _root_.Formalism.REAL.rhoN ε a) ^ 2 - ∑ a, _root_.Formalism.REAL.rhoC ε a ^ 2 := by
    unfold _root_.Formalism.REAL.ckv _root_.Formalism.REAL.nsq _root_.Formalism.REAL.dot _root_.Formalism.QuantumDeterminants.lowK
    simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel, sq]
  have hceq : _root_.BranchingSupport.casG μ = ∑ a, μ a ^ 2 - ∑ a, _root_.Formalism.QuantumDeterminants.rhoStd n a ^ 2 := by
    unfold _root_.BranchingSupport.casG; rfl
  have hj' : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  have hnum := mul_sq_sqrt_sub_le_sq_div_sixteen μ (_root_.Formalism.REAL.rhoN ε) (_root_.Formalism.REAL.rhoC ε) (fun a => _root_.Formalism.QuantumDeterminants.rhoStd n a)
    (_root_.Formalism.QuantumDeterminants.lowK ε μ) (_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) (_root_.BranchingSupport.casG μ) bv j hμ hU hT hρ
    hLeq hKeq hceq hNR hbv hj'
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hoff_le : ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2
      ≤ (2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2 - _root_.BranchingSupport.casG μ
        - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2 := by
    rw [hoff, hsum, hΩ]
    linarith [hKc, hdiag]
  calc (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2
      ≤ (n : ℝ) * ((2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2
        - _root_.BranchingSupport.casG μ - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hoff_le (Nat.cast_nonneg n)
    _ = (n : ℝ) * (2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2
        - _root_.BranchingSupport.casG μ - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2 := by
        ring
    _ ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hnum hw2

end GlobalTheory
