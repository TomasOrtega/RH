import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Establish `hp : (0 : ℝ) < n` using `by exact_mod_cast (zero_lt_one.trans hn)`. Establish `e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n`. Rewrite using `[Real.rpow_sub_one hp.ne' x]`. Clear the denominators using the available nonvanishing facts. Establish `hq : 0 < (n : ℝ) ^ (x - 1)` using `Real.rpow_pos_of_pos hp _`.

Establish `hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1)`. Rewrite using `[Real.rpow_def_of_pos hp]`. Use `Real.add_one_le_exp (Real.log n * (x - 1))` as an intermediate fact. Use polynomial arithmetic with `[this]`. Establish `hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) = ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n)`.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hrw]`. Use `mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)` and prove the remaining obligations.
-/
theorem sub_one_mul_log_div_rpow_le (n : ℕ) (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [Real.rpow_sub_one hp.ne' x]; field_simp
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hp _
  have hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hp]
    have := Real.add_one_le_exp (Real.log n * (x - 1))
    nlinarith [this]
  have hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) =
      ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n) := by
    rw [e]; field_simp
  rw [hrw]
  refine mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)

/- English proof (translation)
Introduce `M hM hs`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Establish `hD` using `Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg`. Unfold `Formalism.HF.LogDensity at hD`. Use `set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS`.

Establish `h0 : Tendsto (fun x : ℝ => ∑' n : ℕ, (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1) (𝓝 (∑' _ : ℕ, (0 : ℝ)))`. Use `tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hn : n ∈ S`. Simplify using `only [Set.indicator_of_mem hn]`. Establish `hp : (0 : ℝ) < n` using `by exact_mod_cast hn.1.pos`.

Establish `hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x)`. Use `(continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)` and prove the remaining obligations. Conclude with `continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')`. Introduce `x`. Conclude with `(Real.rpow_pos_of_pos hp x).ne'`.

Use `(hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))` as an intermediate fact. Simplify using `using this`. Simplify using `only [Set.indicator_of_notMem hn, mul_zero]`. Conclude with `tendsto_const_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with x hx n`.

Establish `hx : (1 : ℝ) < x` using `hx`. Distinguish the cases in `hn : n ∈ S`. Establish `hc : n.Prime ∧ (n : ZMod M) = -1` using `hn`. Simplify using `only [Set.indicator_of_mem hn, if_pos hc]`. Establish `hlog : 0 ≤ Real.log n` using `Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)`.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]`. Conclude with `sub_one_mul_log_div_rpow_le n hc.1.one_lt hx`. Establish `hc : ¬ (n.Prime ∧ (n : ZMod M) = -1)` using `hn`. Simplify using `only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]`. Simplify using `only [tsum_zero, tsum_mul_left] at h0`.

Establish `hu` using `tendsto_nhds_unique hD h0`. Establish `ht : (0 : ℝ) < M.totient` using `by exact_mod_cast Nat.totient_pos.2 hM`. Rewrite `hu` using `[one_div]`. Conclude with `(inv_pos.2 ht).ne' hu`.
-/
theorem not_summable_one_div_primes_eq_neg_one :
    ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ =>
      if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  intro M hM hs
  haveI : NeZero M := ⟨hM.ne'⟩
  have hD := Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg
  unfold Formalism.HF.LogDensity at hD
  set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS
  have h0 : Tendsto (fun x : ℝ => ∑' n : ℕ,
      (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · by_cases hn : n ∈ S
      · simp only [Set.indicator_of_mem hn]
        have hp : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
        have hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x) := by
          refine (continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)
          · exact continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')
          · intro x; exact (Real.rpow_pos_of_pos hp x).ne'
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · simp only [Set.indicator_of_notMem hn, mul_zero]
        exact tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      have hx : (1 : ℝ) < x := hx
      by_cases hn : n ∈ S
      · have hc : n.Prime ∧ (n : ZMod M) = -1 := hn
        simp only [Set.indicator_of_mem hn, if_pos hc]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
          (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]
        exact sub_one_mul_log_div_rpow_le n hc.1.one_lt hx
      · have hc : ¬ (n.Prime ∧ (n : ZMod M) = -1) := hn
        simp only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]
  simp only [tsum_zero, tsum_mul_left] at h0
  have hu := tendsto_nhds_unique hD h0
  have ht : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 hM
  rw [one_div] at hu
  exact (inv_pos.2 ht).ne' hu

end GlobalTheory
