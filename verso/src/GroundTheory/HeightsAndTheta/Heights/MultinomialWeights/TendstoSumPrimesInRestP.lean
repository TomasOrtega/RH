import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset Filter Topology

/- English proof (translation)
Use `set g : ℕ → ℝ := fun p => rest₂ d S.vol p (S.frob p) Q with hg`. Establish `hs : Summable (fun p : primesAbove S B0 => g p)` using `summable_abs_iff.1 h`. Establish `hi : Summable ((primesAbove S B0).indicator g)` using `summable_subtype_iff_indicator.1 hs`. Establish `ht : restTot S B0 Q = ∑' p, (primesAbove S B0).indicator g p`. Rewrite using `[restTot]`.

Conclude with `_root_.tsum_subtype (primesAbove S B0) g`. Rewrite using `[ht]`. Use `(hi.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr ?_` and prove the remaining obligations. Introduce `B`. Establish `hset : primesIn S B0 B = (range (B + 1)).filter (fun p => p ∈ primesAbove S B0)`.

Use extensionality with `p`. Rewrite using `[primesIn, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]`. Establish `hm : p ∈ primesAbove S B0 ↔ p.Prime ∧ ¬ p ∣ S.level ∧ B0 < p` using `Iff.rfl`. Rewrite using `[hm]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨h1, h2⟩, h3, h4⟩`. Conclude with `⟨by omega, h3, h4, h1⟩`. Introduce and unpack `⟨h1, h3, h4, h5⟩`. Conclude with `⟨⟨h5, by omega⟩, h3, h4⟩`. Rewrite using `[Function.comp_apply, hset, Finset.sum_filter]`.

Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[Set.indicator_apply]`.
-/
theorem tendsto_sum_primesIn_restP {d : IndexData} (S : EndSystem d) (B0 : ℕ)
    (Q : ℕ → Fin d.f → XPoly d)
    (h : Summable (fun p : primesAbove S B0 => |rest₂ d S.vol p (S.frob p) Q|)) :
    Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) atTop
      (𝓝 (restTot S B0 Q)) := by
  set g : ℕ → ℝ := fun p => rest₂ d S.vol p (S.frob p) Q with hg
  have hs : Summable (fun p : primesAbove S B0 => g p) := summable_abs_iff.1 h
  have hi : Summable ((primesAbove S B0).indicator g) := summable_subtype_iff_indicator.1 hs
  have ht : restTot S B0 Q = ∑' p, (primesAbove S B0).indicator g p := by
    rw [restTot]
    exact _root_.tsum_subtype (primesAbove S B0) g
  rw [ht]
  refine (hi.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr ?_
  intro B
  classical
  have hset : primesIn S B0 B = (range (B + 1)).filter (fun p => p ∈ primesAbove S B0) := by
    ext p
    rw [primesIn, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    have hm : p ∈ primesAbove S B0 ↔ p.Prime ∧ ¬ p ∣ S.level ∧ B0 < p := Iff.rfl
    rw [hm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by omega, h3, h4, h1⟩
    · rintro ⟨h1, h3, h4, h5⟩
      exact ⟨⟨h5, by omega⟩, h3, h4⟩
  rw [Function.comp_apply, hset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Set.indicator_apply]

/- English proof (translation)
Introduce `d S hin B0 A0 b0 hA hb F Q hQ`. Take `⟨B1, hB1⟩` from `h82 d S hin B0`. Take `⟨C, hC⟩` from `hB1 F Q hQ`. Establish `hrest` using `tendsto_sum_primesIn_restP S B0 Q (hsum d S B0 F Q hQ.2.2)`. Use `set L : ℕ → ℝ := fun B => S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) - bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q with hLdef`.

Establish `hL : Tendsto L atTop (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) + restTot S B0 Q))` using `((((tendsto_const_nhds (x := S.hh F)).sub (hA.mul_const _)).sub (hb.mul_const _)).const_mul S.vol).add hrest`. Establish `hlog : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0)`. Establish `h` using `((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop).const_mul C`. Simplify `h` using `[Function.comp_def, mul_div_assoc]`. Establish `hdiff : Tendsto (fun B => S.PP B0 F - L B) atTop (𝓝 0)`.

Use `squeeze_zero_norm' ?_ hlog` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop B0, eventually_ge_atTop B1] with B hB0 hB1'`. Rewrite using `[Real.norm_eq_abs]`. Conclude with `hC B hB0 hB1'`. Establish `hsum'` using `hL.add hdiff`.

Rewrite `hsum'` using `[add_zero]`. Establish `hconst : Tendsto (fun _ : ℕ => S.PP B0 F) atTop (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) + restTot S B0 Q))` using `hsum'.congr (fun B => by ring)`. Conclude with `tendsto_nhds_unique tendsto_const_nhds hconst`.
-/
theorem HeightTauIdentity.proof (h82 : HeightSumIdentity.Statement) (hsum : RestSummable.Statement) :
    HeightTauIdentity.Statement := by
  intro d S hin B0 A0 b0 hA hb F Q hQ
  obtain ⟨B1, hB1⟩ := h82 d S hin B0
  obtain ⟨C, hC⟩ := hB1 F Q hQ
  have hrest := tendsto_sum_primesIn_restP S B0 Q (hsum d S B0 F Q hQ.2.2)
  set L : ℕ → ℝ := fun B => S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
      bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q with hLdef
  have hL : Tendsto L atTop (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) +
      restTot S B0 Q)) :=
    ((((tendsto_const_nhds (x := S.hh F)).sub (hA.mul_const _)).sub
      (hb.mul_const _)).const_mul S.vol).add hrest
  have hlog : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).const_mul C
    simpa [Function.comp_def, mul_div_assoc] using h
  have hdiff : Tendsto (fun B => S.PP B0 F - L B) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_gt_atTop B0, eventually_ge_atTop B1] with B hB0 hB1'
    rw [Real.norm_eq_abs]
    exact hC B hB0 hB1'
  have hsum' := hL.add hdiff
  rw [add_zero] at hsum'
  have hconst : Tendsto (fun _ : ℕ => S.PP B0 F) atTop
      (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) + restTot S B0 Q)) :=
    hsum'.congr (fun B => by ring)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end GroundTheory.Heights₂.Heights.TheoremB
