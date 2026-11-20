import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ ι _ b i`. Establish `hB1 : 1 ≤ 1 + ∑ c, ‖b c‖`. Establish `: 0 ≤ ∑ c, ‖b c‖` using `Finset.sum_nonneg (fun c _ => norm_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨(1 + ∑ c, ‖b c‖) ^ i, by positivity, fun x => ?_⟩` and prove the remaining obligations.

Establish `hS : 0 ≤ ∑ c, |b.coord c x| ^ i` using `Finset.sum_nonneg (fun c _ => by positivity)`. Establish `hx : ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖` using `by conv_lhs => rw [← b.sum_repr x]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs, Module.Basis.coord_apply]`.

Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Establish `h0 : ‖x‖ = 0`. Establish `: ∑ c, |b.coord c x| * ‖b c‖ = 0` using `by simp`. Combine the linear relations using `[norm_nonneg x]`. Rewrite using `[h0]`.

Establish `hp : 1 ≤ (1 + ∑ c, ‖b c‖) ^ i` using `one_le_pow₀ hB1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨c0, -, hc0⟩` from `Finset.exists_max_image Finset.univ (fun c => |b.coord c x|) Finset.univ_nonempty`. Establish `h1 : ‖x‖ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : |b.coord c0 x| ^ i ≤ ∑ c, |b.coord c x| ^ i` using `Finset.single_le_sum (f := fun c => |b.coord c x| ^ i) (fun c _ => by positivity) (Finset.mem_univ c0)`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_pow_le_const_mul_one_add_sum_abs_coord_pow :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  intro E _ _ ι _ b i
  have hB1 : 1 ≤ 1 + ∑ c, ‖b c‖ := by
    have : 0 ≤ ∑ c, ‖b c‖ := Finset.sum_nonneg (fun c _ => norm_nonneg _)
    linarith
  refine ⟨(1 + ∑ c, ‖b c‖) ^ i, by positivity, fun x => ?_⟩
  have hS : 0 ≤ ∑ c, |b.coord c x| ^ i := Finset.sum_nonneg (fun c _ => by positivity)
  have hx : ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := by
    conv_lhs => rw [← b.sum_repr x]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, Module.Basis.coord_apply]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ‖x‖ = 0 := by
      have : ∑ c, |b.coord c x| * ‖b c‖ = 0 := by simp
      linarith [norm_nonneg x]
    rw [h0]
    have hp : 1 ≤ (1 + ∑ c, ‖b c‖) ^ i := one_le_pow₀ hB1
    calc (0:ℝ) ^ i ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by nlinarith
  · obtain ⟨c0, -, hc0⟩ := Finset.exists_max_image Finset.univ (fun c => |b.coord c x|)
      Finset.univ_nonempty
    have h1 : ‖x‖ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) := by
      calc ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := hx
        _ ≤ ∑ c, |b.coord c0 x| * ‖b c‖ := Finset.sum_le_sum (fun c _ =>
            mul_le_mul_of_nonneg_right (hc0 c (Finset.mem_univ _)) (norm_nonneg _))
        _ = |b.coord c0 x| * ∑ c, ‖b c‖ := by rw [Finset.mul_sum]
        _ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |b.coord c0 x| ^ i ≤ ∑ c, |b.coord c x| ^ i :=
      Finset.single_le_sum (f := fun c => |b.coord c x| ^ i) (fun c _ => by positivity)
        (Finset.mem_univ c0)
    calc ‖x‖ ^ i ≤ (|b.coord c0 x| * (1 + ∑ c, ‖b c‖)) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) h1 i
      _ = (1 + ∑ c, ‖b c‖) ^ i * |b.coord c0 x| ^ i := by rw [mul_pow, mul_comm]
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

end GlobalTheory
