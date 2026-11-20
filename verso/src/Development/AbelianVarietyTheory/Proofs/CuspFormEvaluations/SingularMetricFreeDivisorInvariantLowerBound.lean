import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FreeDivMetric

open GlobalTheory.Up GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

open Classical in

noncomputable def Wfree (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ)

/- English proof (translation)
Unfold `Wfree`. Rewrite using `[if_pos hx]`.
-/
theorem Wfree_of_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X G x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wfree
  rw [if_pos hx]

/- English proof (translation)
Unfold `Wfree`. Rewrite using `[if_neg hx]`.
-/
theorem Wfree_of_notMem {x : Frame X.Ψ r} (hx : x ∉ X.dom) : Wfree Xa Fl G n x = 0 := by
  unfold Wfree
  rw [if_neg hx]

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Conclude with `Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩`.
-/
private lemma sum_norm_sq_pos_of_exists_ne_zero {N : ℕ} {a : Fin N → ℂ} (h : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩

/- English proof (translation)
Establish `hA : 0 < ∑ k, ‖Xa.w k x‖ ^ 2` using `sum_norm_sq_pos_of_exists_ne_zero (Xa.w_nz x hx)`. Establish `hB : 0 < ∑ k, ‖Fl.s k x‖ ^ 2` using `sum_norm_sq_pos_of_exists_ne_zero hs`. Establish `key : Real.exp (-(phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))) = Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))`. Rewrite using `[Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Wfree_of_mem Xa Fl G n hx, key, ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hA.le _)), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hB]`.
-/
theorem Wfree_eq_exp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-(phla X G x +
      (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)))) := by
  have hA : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero (Xa.w_nz x hx)
  have hB : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero hs
  have key : Real.exp (-(phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))) =
      Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hA.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hB]

/- English proof (translation)
Establish `hc : 0 < Real.exp (-phla X Xa.L x)` using `Real.exp_pos _`. Establish `hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _`. Establish `hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _`. Establish `key : Real.exp (-phla X G x) = Real.exp (-phla X (G + n • Xa.L) x) * Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) * Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2))`. Rewrite using `[GlobalTheory.Up.phla_add_nsmul hx, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Wfree_of_mem Xa Fl G n hx, hw, hs, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul hc.le, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_rp …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wfree_eq_pnorm {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have hc : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have key : Real.exp (-phla X G x) = Real.exp (-phla X (G + n • Xa.L) x) *
      Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) * Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, hw, hs, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul hc.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_rpow_of_pos hc, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hc.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/- English proof (translation)
The claim follows from `h.1.1`.
-/
private lemma isBddSec_of_mem_SSgt {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ} (h : P ∈ X.SSgt la c) :
    X.IsBddSec la P := h.1.1

/- English proof (translation)
Establish `hw : ∀ k, ContinuousOn (Xa.w k) X.dom` using `fun k => (isBddSec_of_mem_SSgt (Xa.w_van k)).1.1.continuousOn`. Establish `hs : ∀ k, ContinuousOn (Fl.s k) X.dom` using `fun k => (isBddSec_of_mem_SSgt (Fl.s_van k)).1.1.continuousOn`. Establish `ha : ContinuousOn (fun x => Real.exp (-phla X G x)) X.dom` using `Real.continuous_exp.comp_continuousOn (IW.phla_contOn X G).neg`. Establish `hA : ContinuousOn (fun x => ∑ k, ‖Xa.w k x‖ ^ 2) X.dom` using `continuousOn_finset_sum _ fun k _ => ((hw k).norm).pow 2`. Establish `hB : ContinuousOn (fun x => ∑ k, ‖Fl.s k x‖ ^ 2) X.dom` using `continuousOn_finset_sum _ fun k _ => ((hs k).norm).pow 2`.

Establish `e : Wfree Xa Fl G n = fun x => X.dom.indicator (fun x => ENNReal.ofReal (Real.exp (-phla X G x))) x * X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) x ^ (-(1 / 2 : ℝ)) * X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) x ^ (-((n : ℝ) - 1 / 2))`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ X.dom`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]`. Conclude with `Wfree_of_mem Xa Fl G n hx`.

Rewrite using `[Set.indicator_of_notMem hx, zero_mul, zero_mul]`. Conclude with `Wfree_of_notMem Xa Fl G n hx`. Rewrite using `[e]`. Conclude with `((GlobalTheory.Up.DivMetricPf.measurable_cut ha).mul ((GlobalTheory.Up.DivMetricPf.measurable_cut hA).pow_const _)).mul ((GlobalTheory.Up.DivMetricPf.measurable_cut hB).pow_const _)`.
-/
theorem measurable_Wfree : Measurable (Wfree Xa Fl G n) := by
  have hw : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (isBddSec_of_mem_SSgt (Xa.w_van k)).1.1.continuousOn
  have hs : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (isBddSec_of_mem_SSgt (Fl.s_van k)).1.1.continuousOn
  have ha : ContinuousOn (fun x => Real.exp (-phla X G x)) X.dom :=
    Real.continuous_exp.comp_continuousOn (IW.phla_contOn X G).neg
  have hA : ContinuousOn (fun x => ∑ k, ‖Xa.w k x‖ ^ 2) X.dom :=
    continuousOn_finset_sum _ fun k _ => ((hw k).norm).pow 2
  have hB : ContinuousOn (fun x => ∑ k, ‖Fl.s k x‖ ^ 2) X.dom :=
    continuousOn_finset_sum _ fun k _ => ((hs k).norm).pow 2
  have e : Wfree Xa Fl G n = fun x =>
      X.dom.indicator (fun x => ENNReal.ofReal (Real.exp (-phla X G x))) x *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) x ^ (-(1 / 2 : ℝ)) *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) x ^ (-((n : ℝ) - 1 / 2)) := by
    funext x
    by_cases hx : x ∈ X.dom
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact Wfree_of_mem Xa Fl G n hx
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul]
      exact Wfree_of_notMem Xa Fl G n hx
  rw [e]
  exact ((GlobalTheory.Up.DivMetricPf.measurable_cut ha).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hA).pow_const _)).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hB).pow_const _)

/- English proof (translation)
Establish `hxb : rmul x b ∈ X.dom` using `OntoS.dom_rmul X hx hb`. Establish `hw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x` using `fun k => GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hx hb`. Establish `hs : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x` using `fun k => GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hx hb`. Establish `h1` using `GlobalTheory.Up.DivMetricPf.exp_neg_phla hxb (G + n • Xa.L)`. Establish `h2` using `GlobalTheory.Up.DivMetricPf.exp_neg_phla hx (G + n • Xa.L)`.

Establish `h3` using `hN r X (G + n • Xa.L) x hx b hb`. Establish `hn0 : X.nfac (G + n • Xa.L) (rmul x b) ≠ 0`. Introduce `h`. Establish `hp` using `Real.exp_pos (-phla X (G + n • Xa.L) (rmul x b))`. Rewrite `hp` using `[h1, h]`.

Evaluate the numerical expressions using `at hp`. Establish `hc : ‖bchar (G + n • Xa.L) b‖ ≠ 0`. Introduce `h`. Rewrite `h3` using `[h, inv_zero, zero_mul]`. Conclude with `hn0 h3`.

Establish `hc2 : 0 < ‖bchar (G + n • Xa.L) b‖ ^ 2` using `by positivity`. Establish `hph : Real.exp (-phla X (G + n • Xa.L) (rmul x b)) = Real.exp (-phla X (G + n • Xa.L) x) / ‖bchar (G + n • Xa.L) b‖ ^ 2`. Rewrite using `[h1, h2, h3]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Wfree_eq_pnorm Xa Fl G n hxb, Wfree_eq_pnorm Xa Fl G n hx]`.

Simplify using `only [hw, hs]`. Rewrite using `[hph, ENNReal.ofReal_div_of_pos hc2]`. Simplify using `only [div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wfree_rmul (hN : NfacRmulStatement (E := E)) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    Wfree Xa Fl G n (rmul x b) =
      Wfree Xa Fl G n x / ENNReal.ofReal (‖bchar (G + n • Xa.L) b‖ ^ 2) := by
  have hxb : rmul x b ∈ X.dom := OntoS.dom_rmul X hx hb
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hx hb
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hx hb
  have h1 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hxb (G + n • Xa.L)
  have h2 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hx (G + n • Xa.L)
  have h3 := hN r X (G + n • Xa.L) x hx b hb
  have hn0 : X.nfac (G + n • Xa.L) (rmul x b) ≠ 0 := by
    intro h
    have hp := Real.exp_pos (-phla X (G + n • Xa.L) (rmul x b))
    rw [h1, h] at hp
    norm_num at hp
  have hc : ‖bchar (G + n • Xa.L) b‖ ≠ 0 := by
    intro h
    rw [h, inv_zero, zero_mul] at h3
    exact hn0 h3
  have hc2 : 0 < ‖bchar (G + n • Xa.L) b‖ ^ 2 := by positivity
  have hph : Real.exp (-phla X (G + n • Xa.L) (rmul x b)) =
      Real.exp (-phla X (G + n • Xa.L) x) / ‖bchar (G + n • Xa.L) b‖ ^ 2 := by
    rw [h1, h2, h3]
    field_simp
  rw [Wfree_eq_pnorm Xa Fl G n hxb, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs]
  rw [hph, ENNReal.ofReal_div_of_pos hc2]
  simp only [div_eq_mul_inv]
  ring

/- English proof (translation)
Establish `hxg : lact γ x ∈ X.dom` using `OntoS.dom_lact X hγ hx`. Establish `hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x` using `fun k => GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hγ hx`. Establish `hs : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x` using `fun k => GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hγ hx`. Establish `hph : Real.exp (-phla X (G + n • Xa.L) (lact γ x)) = Real.exp (-phla X (G + n • Xa.L) x)`. Rewrite using `[GlobalTheory.Up.DivMetricPf.exp_neg_phla hxg, GlobalTheory.Up.DivMetricPf.exp_neg_phla hx, hN r X _ γ hγ x hx]`.

Rewrite using `[Wfree_eq_pnorm Xa Fl G n hxg, Wfree_eq_pnorm Xa Fl G n hx]`. Simplify using `only [hw, hs, hph]`.
-/
theorem Wfree_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wfree Xa Fl G n (lact γ x) = Wfree Xa Fl G n x := by
  have hxg : lact γ x ∈ X.dom := OntoS.dom_lact X hγ hx
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hγ hx
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hγ hx
  have hph : Real.exp (-phla X (G + n • Xa.L) (lact γ x)) = Real.exp (-phla X (G + n • Xa.L) x) := by
    rw [GlobalTheory.Up.DivMetricPf.exp_neg_phla hxg, GlobalTheory.Up.DivMetricPf.exp_neg_phla hx, hN r X _ γ hγ x hx]
  rw [Wfree_eq_pnorm Xa Fl G n hxg, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs, hph]

/- English proof (translation)
Take `⟨C, hC, hCw⟩` from `GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Xa.w_van k)`. Take `⟨D, hD, hDs⟩` from `GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Fl.s_van k)`. Establish `ht : (0 : ℝ) ≤ (n : ℝ) - 1 / 2`. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)), mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hD _), fun x hx => ?_⟩` and prove the remaining obligations. Establish `e1` using `GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hC (hCw x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2)`. Establish `e2` using `GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hD (hDs x hx) ht`. Rewrite using `[Wfree_eq_pnorm Xa Fl G n hx]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hC.le _))]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by gcongr`.
-/
theorem Wfree_lower (hn : 1 ≤ n) : WLower X (G + n • Xa.L) (Wfree Xa Fl G n) := by
  obtain ⟨C, hC, hCw⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Xa.w_van k)
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Fl.s_van k)
  have ht : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)),
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hD _), fun x hx => ?_⟩
  have e1 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hC (hCw x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e2 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hD (hDs x hx) ht
  rw [Wfree_eq_pnorm Xa Fl G n hx]
  calc ENNReal.ofReal (C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)) * Real.exp (-phla X (G + n • Xa.L) x))
      = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) * ENNReal.ofReal (C ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (D ^ (-((n : ℝ) - 1 / 2))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hC.le _))]
        congr 1
        ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `E _ _ _ r X Xa Fl G n hn`. Establish `hR` using `GlobalTheory.NormFactor.nfacRmul_holds (E := E)`. Establish `hL` using `GlobalTheory.NormFactor.nfacLact_holds (E := E)`. Conclude with `⟨⟨measurable_Wfree Xa Fl G n, fun x hx b hb => Wfree_rmul Xa Fl G n hR hx hb, fun γ hγ x hx => Wfree_lact Xa Fl G n hL hγ hx⟩, Wfree_lower Xa Fl G n hn, fun x hx hs => Wfree_eq_exp Xa Fl G n hx hs⟩`.
-/
theorem freeDivMetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → IsMetricW X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ WLower X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) x = ENNReal.ofReal (Real.exp (-(fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) x)) := by
  intro E _ _ _ r X Xa Fl G n hn
  have hR := GlobalTheory.NormFactor.nfacRmul_holds (E := E)
  have hL := GlobalTheory.NormFactor.nfacLact_holds (E := E)
  exact ⟨⟨measurable_Wfree Xa Fl G n, fun x hx b hb => Wfree_rmul Xa Fl G n hR hx hb,
    fun γ hγ x hx => Wfree_lact Xa Fl G n hL hγ hx⟩, Wfree_lower Xa Fl G n hn,
    fun x hx hs => Wfree_eq_exp Xa Fl G n hx hs⟩

end GlobalTheory.FreeDivMetric
