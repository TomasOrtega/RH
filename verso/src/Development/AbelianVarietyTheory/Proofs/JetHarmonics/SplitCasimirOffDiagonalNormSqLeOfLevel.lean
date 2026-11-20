import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLe

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ‖∑ c ∈ s, v c‖ ≤ ∑ c ∈ s, ‖v c‖` using `norm_sum_le _ _`. Establish `h2 : (∑ c ∈ s, ‖v c‖) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2` using `sq_sum_le_card_mul_sum_sq`. Establish `h3 : (s.card : ℝ) ≤ n`. Use `card_le_univ s` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`.

Conclude with `this` after adjusting the coercions. Establish `h4 : 0 ≤ ∑ c ∈ s, ‖v c‖ ^ 2` using `sum_nonneg fun _ _ => sq_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sum_sq_le_fin_mul {M : Type} [NormedAddCommGroup M] {n : ℕ} (s : Finset (Fin n)) (v : Fin n → M) :
    ‖∑ c ∈ s, v c‖ ^ 2 ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have h1 : ‖∑ c ∈ s, v c‖ ≤ ∑ c ∈ s, ‖v c‖ := norm_sum_le _ _
  have h2 : (∑ c ∈ s, ‖v c‖) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (s.card : ℝ) ≤ n := by
    have := card_le_univ s
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h4 : 0 ≤ ∑ c ∈ s, ‖v c‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ c ∈ s, v c‖ ^ 2 ≤ (∑ c ∈ s, ‖v c‖) ^ 2 := by gcongr
    _ ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := h2
    _ ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h4

/- English proof (translation)
Introduce `M _ _ n ε E μ kk j bv x hmod hsh hj hlev`. Establish `step1 : ∀ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2` using `fun b => norm_sum_sq_le_fin_mul _ _`. Establish `swap : ∑ b, ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 = ∑ c, ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2` using `Finset.sum_comm' (fun b c => by`. Simplify using `only [mem_univ, mem_erase, true_and, and_true]`. Conclude with `ne_comm)`.

Establish `step2 : ∀ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖x c‖ ^ 2`. Introduce `c`. Use `le_trans ?_ (lev_offDiag_normSq_le M n ε E μ kk j bv (x c) hmod hsh hj (hlev c))` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `sum_le_sum fun b hb => ?_` and prove the remaining obligations. Establish `hcb : c ∈ univ.erase b` using `mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 h.symm, mem_univ _⟩`. Conclude with `single_le_sum (f := fun b' => ‖E b b' (x c)‖ ^ 2) (fun _ _ => sq_nonneg _) hcb`. Use `_ ≤ ∑ b, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_sum, swap, mul_sum]`. Use `_ ≤ ∑ c, (bv / 16) ^ 2 * ‖x c‖ ^ 2 := sum_le_sum fun c _ => step2 c`. Use `_ = (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by rw [mul_sum]`.
-/
theorem offDiagPart_sq_le_of_lev : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M),
    IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) →
      ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hsh hj hlev

  have step1 : ∀ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤
      (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 :=
    fun b => norm_sum_sq_le_fin_mul _ _
  have swap : ∑ b, ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 =
      ∑ c, ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 :=
    Finset.sum_comm' (fun b c => by
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ne_comm)
  have step2 : ∀ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 ≤
      (bv / 16) ^ 2 * ‖x c‖ ^ 2 := by
    intro c
    refine le_trans ?_ (lev_offDiag_normSq_le M n ε E μ kk j bv (x c) hmod hsh hj (hlev c))
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    calc ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2
        ≤ ∑ b ∈ univ.erase c, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 := by
          refine sum_le_sum fun b hb => ?_
          have hcb : c ∈ univ.erase b :=
            mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 h.symm, mem_univ _⟩
          exact single_le_sum (f := fun b' => ‖E b b' (x c)‖ ^ 2) (fun _ _ => sq_nonneg _) hcb
      _ ≤ ∑ b, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2
      ≤ ∑ b, (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 := sum_le_sum fun b _ => step1 b
    _ = ∑ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 := by
      rw [← mul_sum, swap, mul_sum]
    _ ≤ ∑ c, (bv / 16) ^ 2 * ‖x c‖ ^ 2 := sum_le_sum fun c _ => step2 c
    _ = (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by rw [mul_sum]

end GlobalTheory
