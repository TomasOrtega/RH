import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
