import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonnegAtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

/- English proof (translation)
Introduce `d p c hc hdom hev`. Assume the negation of the conclusion as `h0`. Use `push Not at h0`. Take `⟨N, hN⟩` from `eventually_atTop.1 hev`. Set `S : Set ℝ` to `{t | 0 ≤ t ∧ p.eval t ≤ 0}`.

Establish `h0S : (0 : ℝ) ∈ S` using `⟨le_rfl, h0.le⟩`. Establish `hbdd : BddAbove S` using `⟨N, fun t ht => by`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `absurd ht.2 (not_le.2 (hN t hlt.le))⟩`.

Establish `hclosed : IsClosed S` using `(isClosed_le continuous_const continuous_id).inter (isClosed_le p.continuous continuous_const)`. Establish `ht0S : sSup S ∈ S` using `hclosed.csSup_mem ⟨0, h0S⟩ hbdd`. Take `⟨ht0nn, hpt0⟩` from `ht0S`. Establish `hpos : ∀ t, sSup S < t → 0 < p.eval t`. Introduce `t ht`.

Assume the negation of the conclusion as `hle`. Use `push Not at hle`. Conclude with `absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)`. Establish `hlim : c * (sSup S) ^ d ≤ p.eval (sSup S)`. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Establish `hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d` using `p.continuous.sub (continuous_const.mul (continuous_pow d))`. Establish `hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0` using `hcont.continuousAt.eventually (gt_mem_nhds (by linarith))`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff.1 hev'`. Take `⟨q, hq1, hq2⟩` from `exists_rat_btwn (show sSup S < sSup S + ε by linarith)`.

Establish `hqpos : (0 : ℝ) < q` using `lt_of_le_of_lt ht0nn hq1`. Establish `hd : dist (q : ℝ) (sSup S) < ε`. Rewrite using `[Real.dist_eq, abs_lt]`. Apply the tactic sequence `constructor <;> linarith`. Establish `h1` using `hball hd`.

Establish `h2` using `hdom q (by exact_mod_cast hqpos) (hpos q hq1)`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `ht0nn.lt_or_eq with htpos | htz` into its components or cases. Establish `: 0 < c * (sSup S) ^ d` using `mul_pos hc (pow_pos htpos d)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hp0 : 0 ≤ p.eval (sSup S)` using `le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim`. Rewrite `hp0` using `[← htz]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PolyNonnegAtZero.proof : PolyNonnegAtZero.Statement := by
  intro d p c hc hdom hev
  by_contra h0
  push Not at h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set ℝ := {t | 0 ≤ t ∧ p.eval t ≤ 0}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, h0.le⟩
  have hbdd : BddAbove S := ⟨N, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (hN t hlt.le))⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le p.continuous continuous_const)
  have ht0S : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
  obtain ⟨ht0nn, hpt0⟩ := ht0S
  have hpos : ∀ t, sSup S < t → 0 < p.eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)
  have hlim : c * (sSup S) ^ d ≤ p.eval (sSup S) := by
    by_contra hlt
    push Not at hlt
    have hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d :=
      p.continuous.sub (continuous_const.mul (continuous_pow d))
    have hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup S < sSup S + ε by linarith)
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt ht0nn hq1
    have hd : dist (q : ℝ) (sSup S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hball hd
    have h2 := hdom q (by exact_mod_cast hqpos) (hpos q hq1)
    linarith
  rcases ht0nn.lt_or_eq with htpos | htz
  · have : 0 < c * (sSup S) ^ d := mul_pos hc (pow_pos htpos d)
    linarith
  · have hp0 : 0 ≤ p.eval (sSup S) := le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim
    rw [← htz] at hp0
    linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
