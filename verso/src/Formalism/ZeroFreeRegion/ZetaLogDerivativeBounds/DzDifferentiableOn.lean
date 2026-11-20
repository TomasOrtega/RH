import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

def dz (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (1 - s) -
    (s - 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)

def Dz (s : ℂ) : ℂ := ∑' n, dz s n

/- English proof (authored)
Write the power-difference term as s − 1 times the associated integral on the interval beginning at n + 1. Take norms and apply the integral bound at that positive endpoint.
-/
lemma norm_dz_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [dz, d_eq ha s, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_eint_le ha hs) (norm_nonneg _)

/- English proof (authored)
The power series over the positive integers converges for exponent below minus one. Reindex it by n + 1, which is exactly the shifted sequence in the claim.
-/
lemma summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa [Nat.cast_add, Nat.cast_one] using h

/- English proof (authored)
The power-difference bound dominates each term norm by a constant times the power of n + 1 with exponent −Re(s) − 1. The exponent is below −1, so comparison with the summable shifted powers proves the assertion.
-/
lemma summable_norm_dz {s : ℂ} (hs : 0 < s.re) : Summable (fun n => ‖dz s n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_dz_le hs n)
    ((summable_shift (by linarith : -s.re - 1 < -1)).mul_left _)

/- English proof (authored)
Around any point with positive real part, restrict to the unit disk and require the real part to exceed half that of the center. Every power-difference term is holomorphic there. The norms of s and s − 1 are uniformly bounded on this neighborhood, and the exponent in the term bound is at most minus one minus half the center’s real part. The resulting numerical majorant is summable. Thus the series converges uniformly on the neighborhood and its sum is holomorphic there.
-/
lemma Dz_differentiableOn : DifferentiableOn ℂ Dz {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  let U : Set ℂ := {s | s0.re / 2 < s.re} ∩ Metric.ball s0 1
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith, Metric.mem_ball_self one_pos⟩
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s => dz s n) U := by
    intro n
    apply Differentiable.differentiableOn
    intro s
    have h1 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
    have h2 : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1 + 1) ≠ 0)
    unfold dz
    refine ((DifferentiableAt.sub ?_ ?_).sub ((differentiableAt_id.sub_const 1).mul ?_))
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h1)
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h2)
    · exact differentiableAt_id.neg.const_cpow (Or.inl h2)
  have hbound : ∀ n : ℕ, ∀ s ∈ U,
      ‖dz s n‖ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by
    intro n s hs
    have hre : s0.re / 2 < s.re := hs.1
    have hd : ‖s - s0‖ < 1 := by
      have := hs.2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hpos : 0 < s.re := by linarith
    have hsR : ‖s‖ ≤ ‖s0‖ + 1 := by
      have := norm_sub_norm_le s s0
      linarith
    have hs1 : ‖s - 1‖ ≤ ‖s0‖ + 1 + 1 := by
      have := norm_sub_le s 1
      rw [norm_one] at this
      linarith
    have hp : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by linarith)
    calc ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := norm_dz_le hpos n
      _ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by gcongr
  have hsum : Summable (fun n : ℕ =>
      (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1)) :=
    (summable_shift (by linarith)).mul_left _
  have hD : DifferentiableOn ℂ (fun s => ∑' n, dz s n) U :=
    differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

end ComplexPowerDifferenceIntegral

end Formalism.ZF
