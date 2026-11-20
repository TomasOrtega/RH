import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenyP

noncomputable section
open Filter Topology

namespace GlobalTheory.HalfPeriodProduct

open Formalism.L2.Th1.F

def ind (L : PeriodPair) (x : ℂ) : ℤ := by classical exact if x ∈ L.lattice then 1 else 0

/- English proof (translation)
Establish `: -x ∈ L.lattice ↔ x ∈ L.lattice` using `neg_mem_iff`. Unfold `ind`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma ind_neg (L : PeriodPair) (x : ℂ) : ind L (-x) = ind L x := by
  have : -x ∈ L.lattice ↔ x ∈ L.lattice := neg_mem_iff
  unfold ind
  split_ifs <;> simp_all

/- English proof (translation)
Establish `: x ∈ L.lattice ↔ y ∈ L.lattice`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Simplify using `using L.lattice.sub_mem hx h`. Introduce `hy`.

Simplify using `using L.lattice.add_mem h hy`. Unfold `ind`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma ind_congr (L : PeriodPair) {x y : ℂ} (h : x - y ∈ L.lattice) : ind L x = ind L y := by
  have : x ∈ L.lattice ↔ y ∈ L.lattice := by
    constructor
    · intro hx; simpa using L.lattice.sub_mem hx h
    · intro hy; simpa using L.lattice.add_mem h hy
  unfold ind
  split_ifs <;> simp_all

/- English proof (translation)
Establish `h` using `sigmaOrder L 1 b z₀ one_ne_zero`. Simplify using `only [one_mul] at h`. Rewrite using `[h]`. Unfold `ind`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma order_sigma (L : PeriodPair) (b z₀ : ℂ) :
    meromorphicOrderAt (fun z => wSigma L (z + b)) z₀ = ((ind L (z₀ + b) : ℤ) : WithTop ℤ) := by
  have h := sigmaOrder L 1 b z₀ one_ne_zero
  simp only [one_mul] at h
  rw [h]
  unfold ind
  split_ifs <;> simp_all

/- English proof (translation)
The claim follows from `((sigmaEntire L).comp (differentiable_id.add_const b)).analyticAt z₀`.
-/
lemma analyticAt_sigma (L : PeriodPair) (b z₀ : ℂ) : AnalyticAt ℂ (fun z => wSigma L (z + b)) z₀ :=
  ((sigmaEntire L).comp (differentiable_id.add_const b)).analyticAt z₀

/- English proof (translation)
Establish `hσa : wSigma L a ≠ 0` using `fun h => ha ((sigmaZero L a).1 h)`. Use `set c : ℂ := -((wSigma L a) ^ 2)⁻¹ with hc_def`. Establish `hc : c ≠ 0` using `by simp [c, hσa]`. Establish `heq : (fun z => L.weierstrassP z - L.weierstrassP a) =ᶠ[𝓝[≠] z₀] ((fun _ => c) * (fun z => wSigma L (z + a)) * (fun z => wSigma L (z + -a)) * ((fun z => wSigma L (z + 0)) ^ 2)⁻¹)` using `by filter_upwards [IsogenyPAux.eventually_notMem L 1 z₀ one_ne_zero] with z hz`. Rewrite `hz` using `[one_mul]`.

Establish `hσz : wSigma L z ≠ 0` using `fun h => hz ((sigmaZero L z).1 h)`. Establish `h` using `sigmaAdd L z a hz ha`. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, add_zero, ← sub_eq_add_neg, c]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.

Establish `m : ∀ b, MeromorphicAt (fun z => wSigma L (z + b)) z₀` using `fun b => (analyticAt_sigma L b z₀).meromorphicAt`. Establish `hm : MeromorphicAt ((fun _ => c) * (fun z => wSigma L (z + a)) * (fun z => wSigma L (z + -a)) * ((fun z => wSigma L (z + 0)) ^ 2)⁻¹) z₀` using `(((MeromorphicAt.const c z₀).mul (m a)).mul (m (-a))).mul ((m 0).pow 2).inv`. Use `⟨hm.congr heq.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[meromorphicOrderAt_congr heq, meromorphicOrderAt_mul (((MeromorphicAt.const c z₀).mul (m a)).mul (m (-a))) ((m 0).pow 2).inv, meromorphicOrderAt_mul ((MeromorphicAt.const c z₀).mul (m a)) (m (-a)), meromorphicOrderAt_mul (MeromorphicAt.const c z₀) (m a), meromorphicOrderAt_inv, …`. Rewrite using `[show ((2 : ℕ) : WithTop ℤ) * ((ind L (z₀ + 0) : ℤ) : WithTop ℤ) = ((2 * ind L (z₀ + 0) : ℤ) : WithTop ℤ) by norm_cast, zero_add, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]`.

Use `congr 1`.
-/
lemma order_sub (L : PeriodPair) {a : ℂ} (ha : a ∉ L.lattice) (z₀ : ℂ) :
    MeromorphicAt (fun z => L.weierstrassP z - L.weierstrassP a) z₀ ∧
    meromorphicOrderAt (fun z => L.weierstrassP z - L.weierstrassP a) z₀
      = ((ind L (z₀ + a) + ind L (z₀ + -a) - 2 * ind L (z₀ + 0) : ℤ) : WithTop ℤ) := by
  classical
  have hσa : wSigma L a ≠ 0 := fun h => ha ((sigmaZero L a).1 h)
  set c : ℂ := -((wSigma L a) ^ 2)⁻¹ with hc_def
  have hc : c ≠ 0 := by simp [c, hσa]
  have heq : (fun z => L.weierstrassP z - L.weierstrassP a) =ᶠ[𝓝[≠] z₀]
      ((fun _ => c) * (fun z => wSigma L (z + a)) * (fun z => wSigma L (z + -a))
        * ((fun z => wSigma L (z + 0)) ^ 2)⁻¹) := by
    filter_upwards [IsogenyPAux.eventually_notMem L 1 z₀ one_ne_zero] with z hz
    rw [one_mul] at hz
    have hσz : wSigma L z ≠ 0 := fun h => hz ((sigmaZero L z).1 h)
    have h := sigmaAdd L z a hz ha
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, add_zero, ← sub_eq_add_neg, c]
    field_simp
    linear_combination h
  have m : ∀ b, MeromorphicAt (fun z => wSigma L (z + b)) z₀ := fun b => (analyticAt_sigma L b z₀).meromorphicAt
  have hm : MeromorphicAt ((fun _ => c) * (fun z => wSigma L (z + a)) * (fun z => wSigma L (z + -a))
        * ((fun z => wSigma L (z + 0)) ^ 2)⁻¹) z₀ :=
    (((MeromorphicAt.const c z₀).mul (m a)).mul (m (-a))).mul ((m 0).pow 2).inv
  refine ⟨hm.congr heq.symm, ?_⟩
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul (((MeromorphicAt.const c z₀).mul (m a)).mul (m (-a)))
    ((m 0).pow 2).inv, meromorphicOrderAt_mul ((MeromorphicAt.const c z₀).mul (m a)) (m (-a)),
    meromorphicOrderAt_mul (MeromorphicAt.const c z₀) (m a), meromorphicOrderAt_inv,
    meromorphicOrderAt_pow (m 0), meromorphicOrderAt_const, if_neg hc, order_sigma, order_sigma, order_sigma]
  rw [show ((2 : ℕ) : WithTop ℤ) * ((ind L (z₀ + 0) : ℤ) : WithTop ℤ) = ((2 * ind L (z₀ + 0) : ℤ) : WithTop ℤ) by
    norm_cast, zero_add, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  congr 1

/- English proof (translation)
Establish `hsub : ∀ t ∈ T, x + -t ∈ L.lattice → x ∈ L'.lattice` using `fun t ht h => by`. Simplify using `using L'.lattice.add_mem (hLL h) (hT1 t ht).1`. Distinguish the cases in `hx : x ∈ L'.lattice`. Establish `e1 : ind L' x = 1` using `by unfold ind; simp [hx]`. Rewrite using `[e1]`.

Distinguish the cases in `hxL : x ∈ L.lattice`. Establish `e2 : ind L x = 1` using `by unfold ind; simp [hxL]`. Establish `e3 : ∀ t ∈ T, ind L (x + -t) = 0` using `fun t ht => by`. Establish `: x + -t ∉ L.lattice` using `fun h => (hT1 t ht).2 (by simpa using L.lattice.sub_mem hxL h)`. Unfold `ind`.

Simplify using `[this]`. Rewrite using `[e2, Finset.sum_eq_zero e3]`. Simplify using the standard rewrite rules. Establish `e2 : ind L x = 0` using `by unfold ind; simp [hxL]`. Take `⟨t₀, ht₀, hxt⟩` from `(hT3 x hx).resolve_left hxL`.

Establish `e3 : ind L (x + -t₀) = 1` using `by unfold ind; simp [← sub_eq_add_neg, hxt]`. Rewrite using `[e2, Finset.sum_eq_single t₀ (fun t ht hne => ?_) (fun h => absurd ht₀ h), e3]`. Simplify using the standard rewrite rules. Establish `: x + -t ∉ L.lattice` using `fun h => hne (hT2 t ht t₀ ht₀ (by`. Use `L.lattice.sub_mem hxt h` as an intermediate fact.

Rewrite `this` using `[← sub_eq_add_neg]`. Simplify using `using this))`. Unfold `ind`. Simplify using `[this]`. Establish `e1 : ind L' x = 0` using `by unfold ind; simp [hx]`.

Establish `hxL : x ∉ L.lattice` using `fun h => hx (hLL h)`. Establish `e2 : ind L x = 0` using `by unfold ind; simp [hxL]`. Establish `e3 : ∀ t ∈ T, ind L (x + -t) = 0` using `fun t ht => by`. Establish `: x + -t ∉ L.lattice` using `fun h => hx (hsub t ht h)`. Unfold `ind`.

Simplify using `[this]`. Rewrite using `[e1, e2, Finset.sum_eq_zero e3]`. Simplify using the standard rewrite rules.
-/
lemma ind_count (L L' : PeriodPair) (T : Finset ℂ) (hLL : L.lattice ≤ L'.lattice)
    (hT1 : ∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ L.lattice)
    (hT2 : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L.lattice → t = t')
    (hT3 : ∀ x ∈ L'.lattice, x ∈ L.lattice ∨ ∃ t ∈ T, x - t ∈ L.lattice) (x : ℂ) :
    ind L' x = ind L x + ∑ t ∈ T, ind L (x + -t) := by
  classical
  have hsub : ∀ t ∈ T, x + -t ∈ L.lattice → x ∈ L'.lattice := fun t ht h => by
    simpa using L'.lattice.add_mem (hLL h) (hT1 t ht).1
  by_cases hx : x ∈ L'.lattice
  · have e1 : ind L' x = 1 := by unfold ind; simp [hx]
    rw [e1]
    by_cases hxL : x ∈ L.lattice
    · have e2 : ind L x = 1 := by unfold ind; simp [hxL]
      have e3 : ∀ t ∈ T, ind L (x + -t) = 0 := fun t ht => by
        have : x + -t ∉ L.lattice := fun h => (hT1 t ht).2 (by simpa using L.lattice.sub_mem hxL h)
        unfold ind; simp [this]
      rw [e2, Finset.sum_eq_zero e3]; simp
    · have e2 : ind L x = 0 := by unfold ind; simp [hxL]
      obtain ⟨t₀, ht₀, hxt⟩ := (hT3 x hx).resolve_left hxL
      have e3 : ind L (x + -t₀) = 1 := by unfold ind; simp [← sub_eq_add_neg, hxt]
      rw [e2, Finset.sum_eq_single t₀ (fun t ht hne => ?_) (fun h => absurd ht₀ h), e3]
      · simp
      · have : x + -t ∉ L.lattice := fun h => hne (hT2 t ht t₀ ht₀ (by
          have := L.lattice.sub_mem hxt h
          rw [← sub_eq_add_neg] at this
          simpa using this))
        unfold ind; simp [this]
  · have e1 : ind L' x = 0 := by unfold ind; simp [hx]
    have hxL : x ∉ L.lattice := fun h => hx (hLL h)
    have e2 : ind L x = 0 := by unfold ind; simp [hxL]
    have e3 : ∀ t ∈ T, ind L (x + -t) = 0 := fun t ht => by
      have : x + -t ∉ L.lattice := fun h => hx (hsub t ht h)
      unfold ind; simp [this]
    rw [e1, e2, Finset.sum_eq_zero e3]; simp

/- English proof (translation)
Establish `hE : ContinuousAt (M.weierstrassPExcept 0) 0` using `(M.analyticAt_weierstrassPExcept 0).continuousAt`. Establish `h1 : Tendsto (fun z : ℂ => z ^ 2 * (M.weierstrassPExcept 0 z - c) + 1) (𝓝[≠] 0) (𝓝 (0 ^ 2 * (M.weierstrassPExcept 0 0 - c) + 1))`. Use `(((continuous_pow 2).continuousAt.tendsto.mul (hE.tendsto.sub tendsto_const_nhds)).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds` and prove the remaining obligations. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add] at h1`. Use `h1.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with z hz`. Establish `hz' : z ≠ 0` using `hz`. Rewrite using `[IsogenyPAux.P_local M 0 M.lattice.zero_mem z, sub_zero]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma tendsto_sq_mul (M : PeriodPair) (c : ℂ) :
    Tendsto (fun z => z ^ 2 * (M.weierstrassP z - c)) (𝓝[≠] 0) (𝓝 1) := by
  have hE : ContinuousAt (M.weierstrassPExcept 0) 0 := (M.analyticAt_weierstrassPExcept 0).continuousAt
  have h1 : Tendsto (fun z : ℂ => z ^ 2 * (M.weierstrassPExcept 0 z - c) + 1) (𝓝[≠] 0)
      (𝓝 (0 ^ 2 * (M.weierstrassPExcept 0 0 - c) + 1)) := by
    refine (((continuous_pow 2).continuousAt.tendsto.mul (hE.tendsto.sub tendsto_const_nhds)).add
      tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := hz
  rw [IsogenyPAux.P_local M 0 M.lattice.zero_mem z, sub_zero]
  field_simp
  ring

/- English proof (translation)
Establish `hwL : w ∉ L.lattice` using `fun h => hw (hLL h)`. Establish `htL : ∀ t ∈ T, t ∉ L.lattice` using `fun t ht => (hT1 t ht).2`. Establish `hwt : ∀ t ∈ T, w + t ∉ L.lattice` using `fun t ht h => hw (by`. Simplify using `using L'.lattice.sub_mem (hLL h) (hT1 t ht).1)`. Use `set A : ℂ → ℂ := fun z => (L'.weierstrassP z - L'.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t) with hA`.

Use `set B : ℂ → ℂ := fun z => (L.weierstrassP z - L.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t)) with hB`. Establish `mprod : ∀ (f : ℂ → ℂ → ℂ) z₀, (∀ t ∈ T, MeromorphicAt (f t) z₀) → MeromorphicAt (fun z => ∏ t ∈ T, f t z) z₀` using `fun f z₀ h => by`. Use `MeromorphicAt.prod (s := T) h` as an intermediate fact. Rewrite `this` using `[Finset.prod_fn]`. Then use the resulting hypothesis. Establish `mA : ∀ z₀, MeromorphicAt A z₀` using `fun z₀ => (order_sub L' hw z₀).1.mul (mprod _ z₀ fun t ht => (order_sub L (htL t ht) z₀).1)`.

Establish `mB : ∀ z₀, MeromorphicAt B z₀` using `fun z₀ => (order_sub L hwL z₀).1.mul (mprod _ z₀ fun t ht => (order_sub L (hwt t ht) z₀).1)`. Establish `oA : ∀ z₀, meromorphicOrderAt A z₀ = ((ind L' (z₀ + w) + ind L' (z₀ + -w) - 2 * ind L' (z₀ + 0) + ∑ t ∈ T, (ind L (z₀ + t) + ind L (z₀ + -t) - 2 * ind L (z₀ + 0)) : ℤ) : WithTop ℤ)`. Introduce `z₀`. Rewrite using `[show A = (fun z => L'.weierstrassP z - L'.weierstrassP w) * (fun z => ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t)) from rfl]`. Rewrite using `[meromorphicOrderAt_mul (order_sub L' hw z₀).1 (mprod _ z₀ fun t ht => (order_sub L (htL t ht) z₀).1), meromorphicOrderAt_fun_prod (fun t ht => (order_sub L (htL t ht) z₀).1), (order_sub L' hw z₀).2, Finset.sum_congr rfl (fun t ht => (order_sub L (htL t ht) z₀).2), ← WithTop.coe_ …`.

Establish `oB : ∀ z₀, meromorphicOrderAt B z₀ = ((ind L (z₀ + w) + ind L (z₀ + -w) - 2 * ind L (z₀ + 0) + ∑ t ∈ T, (ind L (z₀ + (w + t)) + ind L (z₀ + -(w + t)) - 2 * ind L (z₀ + 0)) : ℤ) : WithTop ℤ)`. Introduce `z₀`. Rewrite using `[show B = (fun z => L.weierstrassP z - L.weierstrassP w) * (fun z => ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t))) from rfl]`. Rewrite using `[meromorphicOrderAt_mul (order_sub L hwL z₀).1 (mprod _ z₀ fun t ht => (order_sub L (hwt t ht) z₀).1), meromorphicOrderAt_fun_prod (fun t ht => (order_sub L (hwt t ht) z₀).1), (order_sub L hwL z₀).2, Finset.sum_congr rfl (fun t ht => (order_sub L (hwt t ht) z₀).2), ← WithTop.coe_ …`. Establish `cnt` using `ind_count L L' T hLL hT1 hT2 hT3`.

Establish `oAB : ∀ z₀, meromorphicOrderAt A z₀ = meromorphicOrderAt B z₀`. Introduce `z₀`. Rewrite using `[oA, oB]`. Use `congr 1`. Establish `h1` using `cnt (z₀ + w)`.

Establish `h2 : ind L' (z₀ + -w) = ind L (z₀ + -w) + ∑ t ∈ T, ind L (z₀ + -w + t)`. Rewrite using `[← ind_neg L' (z₀ + -w), cnt (-(z₀ + -w)), ind_neg]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← ind_neg L (z₀ + -w + t)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `cnt (z₀ + 0)`. Establish `h3' : ind L' (z₀ + 0) = ind L (z₀ + 0) + ∑ t ∈ T, ind L (z₀ + t)`. Rewrite using `[← ind_neg L' (z₀ + 0), cnt (-(z₀ + 0)), ind_neg]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← ind_neg L (z₀ + t)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4 : ∑ t ∈ T, ind L (z₀ + w + -t) = ∑ t ∈ T, ind L (z₀ + -(w + t))` using `Finset.sum_congr rfl fun t _ => ind_congr L (by`. Establish `e : z₀ + w + -t - (z₀ + -(w + t)) = 2 * w` using `by ring`. Rewrite using `[e]`. Conclude with `hw2)`. Establish `h5 : ∑ t ∈ T, ind L (z₀ + -w + t) = ∑ t ∈ T, ind L (z₀ + (w + t))` using `Finset.sum_congr rfl fun t _ => ind_congr L (by`.

Establish `e : z₀ + -w + t - (z₀ + (w + t)) = -(2 * w)` using `by ring`. Rewrite using `[e]`. Conclude with `L.lattice.neg_mem hw2)`. Establish `h6 : ∑ t ∈ T, ind L (z₀ + 0 + -t) = ∑ t ∈ T, ind L (z₀ + -t)` using `Finset.sum_congr rfl fun t _ => by rw [add_zero]`. Rewrite `h1` using `[h4]`.

Rewrite `h2` using `[h5]`. Rewrite `h3` using `[h6]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Take the linear combination `h1 + h2 - h3 - h3'`. Use `set F : ℂ → ℂ := fun z => A z / B z with hF`.

Establish `hper : IsPeriodic L F`. Introduce `ω hω x`. Simplify using `only [hF, hA, hB]`. Rewrite using `[L.weierstrassP_add_coe x ⟨ω, hω⟩, L'.weierstrassP_add_coe x ⟨ω, hLL hω⟩]`. Establish `mF : ∀ z₀, MeromorphicAt F z₀` using `fun z₀ => (mA z₀).div (mB z₀)`.

Establish `oF : ∀ z₀, 0 ≤ meromorphicOrderAt F z₀`. Introduce `z₀`. Rewrite using `[show F = A / B from rfl, meromorphicOrderAt_div (mA z₀) (mB z₀), oAB, oB, sub_eq_add_neg, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, add_neg_cancel]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `ellipticNoPole L F mF hper oF`.

Establish `cP : ∀ (M : PeriodPair) x, x ∉ M.lattice → ContinuousAt M.weierstrassP x` using `fun M x hx => (M.analyticOnNhd_weierstrassP x hx).continuousAt`. Establish `cont : ∀ x, x ∉ L'.lattice → B x ≠ 0 → ContinuousAt F x`. Introduce `x hx hBx`. Establish `hxL : x ∉ L.lattice` using `fun h => hx (hLL h)`. Establish `cA : ContinuousAt A x` using `((cP L' x hx).sub continuousAt_const).mul (tendsto_finsetProd T fun t _ => (cP L x hxL).sub continuousAt_const)`.

Establish `cB : ContinuousAt B x` using `((cP L x hxL).sub continuousAt_const).mul (tendsto_finsetProd T fun t _ => (cP L x hxL).sub continuousAt_const)`. Conclude with `cA.div cB hBx`. Use `set m : ℕ := 2 * (T.card + 1)`. Establish `eA : ∀ x, x ^ m * A x = (x ^ 2 * (L'.weierstrassP x - L'.weierstrassP w)) * ∏ t ∈ T, (x ^ 2 * (L.weierstrassP x - L.weierstrassP t))`. Introduce `x`.

Simplify using `only [hA, m, Finset.prod_mul_distrib, Finset.prod_const]`. Expand and normalize the polynomial expressions, which then agree. Establish `eB : ∀ x, x ^ m * B x = (x ^ 2 * (L.weierstrassP x - L.weierstrassP w)) * ∏ t ∈ T, (x ^ 2 * (L.weierstrassP x - L.weierstrassP (w + t)))`. Introduce `x`. Simplify using `only [hB, m, Finset.prod_mul_distrib, Finset.prod_const]`.

Expand and normalize the polynomial expressions, which then agree. Establish `tA : Tendsto (fun x => x ^ m * A x) (𝓝[≠] 0) (𝓝 1)`. Use `(tendsto_sq_mul L' (L'.weierstrassP w)).mul (tendsto_finsetProd T fun t _ => tendsto_sq_mul L (L.weierstrassP t))` as an intermediate fact. Simplify using `only [Finset.prod_const_one, mul_one] at this`. Conclude with `this.congr fun x => (eA x).symm`.

Establish `tB : Tendsto (fun x => x ^ m * B x) (𝓝[≠] 0) (𝓝 1)`. Use `(tendsto_sq_mul L (L.weierstrassP w)).mul (tendsto_finsetProd T fun t _ => tendsto_sq_mul L (L.weierstrassP (w + t)))` as an intermediate fact. Simplify using `only [Finset.prod_const_one, mul_one] at this`. Conclude with `this.congr fun x => (eB x).symm`. Establish `evB : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ^ m * B x ≠ 0` using `tB.eventually_ne one_ne_zero`.

Establish `tF : Tendsto F (𝓝[≠] 0) (𝓝 1)`. Use `tA.div tB one_ne_zero` as an intermediate fact. Rewrite `this` using `[div_one]`. Use `this.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`.

Establish `hx' : x ^ m ≠ 0` using `pow_ne_zero _ hx`. Use `show x ^ m * A x / (x ^ m * B x) = A x / B x`. Rewrite using `[mul_div_mul_left _ _ hx']`. Establish `tF' : Tendsto F (𝓝[≠] 0) (𝓝 c)`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [evB, IsogenyPAux.eventually_notMem L' 1 0 one_ne_zero] with x hx1 hx2`. Rewrite `hx2` using `[one_mul]`. Conclude with `(hc x (cont x hx2 (right_ne_zero_of_mul hx1))).symm`. Establish `hc1 : c = 1` using `tendsto_nhds_unique tF' tF`. Distinguish the cases in `hBz : B z = 0`.

Establish `hzL : z ∉ L.lattice` using `fun h => hz (hLL h)`. Establish `key : ∀ a, a ∉ L.lattice → a - w ∈ L'.lattice → L.weierstrassP z = L.weierstrassP a → L'.weierstrassP z = L'.weierstrassP w`. Introduce `a ha haw he`. Break down `(pInjective L z a hzL ha).1 he with h | h` into its components or cases. Establish `h' : z - w ∈ L'.lattice`.

Use `L'.lattice.add_mem (hLL h) haw` as an intermediate fact. Rewrite `this` using `[show z - a + (a - w) = z - w by ring]`. Then use the resulting hypothesis. Use `L'.weierstrassP_add_coe w ⟨z - w, h'⟩` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Establish `h' : z + w ∈ L'.lattice`. Use `L'.lattice.sub_mem (hLL h) haw` as an intermediate fact. Rewrite `this` using `[show z + a - (a - w) = z + w by ring]`. Then use the resulting hypothesis. Use `L'.weierstrassP_add_coe (-w) ⟨z + w, h'⟩` as an intermediate fact. Simplify using `only at this`.

Rewrite `this` using `[show -w + (z + w) = z by ring, L'.weierstrassP_neg]`. Conclude with `this`. Establish `hAz : A z = 0`. Simplify using `only [hB, mul_eq_zero, Finset.prod_eq_zero_iff, sub_eq_zero] at hBz`. Simplify using `only [hA]`.

Break down `hBz with h | ⟨t, ht, h⟩` into its components or cases. Rewrite using `[key w hwL (by simp) h, sub_self, zero_mul]`. Rewrite using `[key (w + t) (hwt t ht) (by simpa using (hT1 t ht).1) h, sub_self, zero_mul]`. Conclude with `hAz.trans hBz.symm`. Use `hc z (cont z hz hBz)` as an intermediate fact.

Rewrite `this` using `[hc1]`. Conclude with `(div_eq_one_iff_eq hBz).1 this`.
-/
theorem wp_half_period_prod (L L' : PeriodPair) (T : Finset ℂ) (w : ℂ) (hLL : L.lattice ≤ L'.lattice)
    (hT1 : ∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ L.lattice)
    (hT2 : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L.lattice → t = t')
    (hT3 : ∀ x ∈ L'.lattice, x ∈ L.lattice ∨ ∃ t ∈ T, x - t ∈ L.lattice)
    (hw2 : 2 * w ∈ L.lattice) (hw : w ∉ L'.lattice) (z : ℂ) (hz : z ∉ L'.lattice) :
    (L'.weierstrassP z - L'.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t) =
      (L.weierstrassP z - L.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t)) := by
  classical
  have hwL : w ∉ L.lattice := fun h => hw (hLL h)
  have htL : ∀ t ∈ T, t ∉ L.lattice := fun t ht => (hT1 t ht).2
  have hwt : ∀ t ∈ T, w + t ∉ L.lattice := fun t ht h => hw (by
    simpa using L'.lattice.sub_mem (hLL h) (hT1 t ht).1)
  set A : ℂ → ℂ := fun z => (L'.weierstrassP z - L'.weierstrassP w) *
    ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t) with hA
  set B : ℂ → ℂ := fun z => (L.weierstrassP z - L.weierstrassP w) *
    ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t)) with hB

  have mprod : ∀ (f : ℂ → ℂ → ℂ) z₀, (∀ t ∈ T, MeromorphicAt (f t) z₀) →
      MeromorphicAt (fun z => ∏ t ∈ T, f t z) z₀ := fun f z₀ h => by
    have := MeromorphicAt.prod (s := T) h
    rwa [Finset.prod_fn] at this
  have mA : ∀ z₀, MeromorphicAt A z₀ := fun z₀ =>
    (order_sub L' hw z₀).1.mul (mprod _ z₀ fun t ht => (order_sub L (htL t ht) z₀).1)
  have mB : ∀ z₀, MeromorphicAt B z₀ := fun z₀ =>
    (order_sub L hwL z₀).1.mul (mprod _ z₀ fun t ht => (order_sub L (hwt t ht) z₀).1)
  have oA : ∀ z₀, meromorphicOrderAt A z₀ = ((ind L' (z₀ + w) + ind L' (z₀ + -w) - 2 * ind L' (z₀ + 0)
      + ∑ t ∈ T, (ind L (z₀ + t) + ind L (z₀ + -t) - 2 * ind L (z₀ + 0)) : ℤ) : WithTop ℤ) := by
    intro z₀
    rw [show A = (fun z => L'.weierstrassP z - L'.weierstrassP w) *
      (fun z => ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t)) from rfl]
    rw [meromorphicOrderAt_mul (order_sub L' hw z₀).1 (mprod _ z₀ fun t ht => (order_sub L (htL t ht) z₀).1),
      meromorphicOrderAt_fun_prod (fun t ht => (order_sub L (htL t ht) z₀).1), (order_sub L' hw z₀).2,
      Finset.sum_congr rfl (fun t ht => (order_sub L (htL t ht) z₀).2), ← WithTop.coe_sum, ← WithTop.coe_add]
  have oB : ∀ z₀, meromorphicOrderAt B z₀ = ((ind L (z₀ + w) + ind L (z₀ + -w) - 2 * ind L (z₀ + 0)
      + ∑ t ∈ T, (ind L (z₀ + (w + t)) + ind L (z₀ + -(w + t)) - 2 * ind L (z₀ + 0)) : ℤ) : WithTop ℤ) := by
    intro z₀
    rw [show B = (fun z => L.weierstrassP z - L.weierstrassP w) *
      (fun z => ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t))) from rfl]
    rw [meromorphicOrderAt_mul (order_sub L hwL z₀).1 (mprod _ z₀ fun t ht => (order_sub L (hwt t ht) z₀).1),
      meromorphicOrderAt_fun_prod (fun t ht => (order_sub L (hwt t ht) z₀).1), (order_sub L hwL z₀).2,
      Finset.sum_congr rfl (fun t ht => (order_sub L (hwt t ht) z₀).2), ← WithTop.coe_sum, ← WithTop.coe_add]
  have cnt := ind_count L L' T hLL hT1 hT2 hT3
  have oAB : ∀ z₀, meromorphicOrderAt A z₀ = meromorphicOrderAt B z₀ := by
    intro z₀
    rw [oA, oB]
    congr 1
    have h1 := cnt (z₀ + w)
    have h2 : ind L' (z₀ + -w) = ind L (z₀ + -w) + ∑ t ∈ T, ind L (z₀ + -w + t) := by
      rw [← ind_neg L' (z₀ + -w), cnt (-(z₀ + -w)), ind_neg]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← ind_neg L (z₀ + -w + t)]; congr 1; ring
    have h3 := cnt (z₀ + 0)
    have h3' : ind L' (z₀ + 0) = ind L (z₀ + 0) + ∑ t ∈ T, ind L (z₀ + t) := by
      rw [← ind_neg L' (z₀ + 0), cnt (-(z₀ + 0)), ind_neg]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← ind_neg L (z₀ + t)]; congr 1; ring
    have h4 : ∑ t ∈ T, ind L (z₀ + w + -t) = ∑ t ∈ T, ind L (z₀ + -(w + t)) :=
      Finset.sum_congr rfl fun t _ => ind_congr L (by
        have e : z₀ + w + -t - (z₀ + -(w + t)) = 2 * w := by ring
        rw [e]; exact hw2)
    have h5 : ∑ t ∈ T, ind L (z₀ + -w + t) = ∑ t ∈ T, ind L (z₀ + (w + t)) :=
      Finset.sum_congr rfl fun t _ => ind_congr L (by
        have e : z₀ + -w + t - (z₀ + (w + t)) = -(2 * w) := by ring
        rw [e]; exact L.lattice.neg_mem hw2)
    have h6 : ∑ t ∈ T, ind L (z₀ + 0 + -t) = ∑ t ∈ T, ind L (z₀ + -t) :=
      Finset.sum_congr rfl fun t _ => by rw [add_zero]
    rw [h4] at h1
    rw [h5] at h2
    rw [h6] at h3
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination h1 + h2 - h3 - h3'

  set F : ℂ → ℂ := fun z => A z / B z with hF
  have hper : IsPeriodic L F := by
    intro ω hω x
    simp only [hF, hA, hB]
    rw [L.weierstrassP_add_coe x ⟨ω, hω⟩, L'.weierstrassP_add_coe x ⟨ω, hLL hω⟩]
  have mF : ∀ z₀, MeromorphicAt F z₀ := fun z₀ => (mA z₀).div (mB z₀)
  have oF : ∀ z₀, 0 ≤ meromorphicOrderAt F z₀ := by
    intro z₀
    rw [show F = A / B from rfl, meromorphicOrderAt_div (mA z₀) (mB z₀), oAB, oB, sub_eq_add_neg,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, add_neg_cancel]
    simp
  obtain ⟨c, hc⟩ := ellipticNoPole L F mF hper oF

  have cP : ∀ (M : PeriodPair) x, x ∉ M.lattice → ContinuousAt M.weierstrassP x :=
    fun M x hx => (M.analyticOnNhd_weierstrassP x hx).continuousAt
  have cont : ∀ x, x ∉ L'.lattice → B x ≠ 0 → ContinuousAt F x := by
    intro x hx hBx
    have hxL : x ∉ L.lattice := fun h => hx (hLL h)
    have cA : ContinuousAt A x := ((cP L' x hx).sub continuousAt_const).mul
      (tendsto_finsetProd T fun t _ => (cP L x hxL).sub continuousAt_const)
    have cB : ContinuousAt B x := ((cP L x hxL).sub continuousAt_const).mul
      (tendsto_finsetProd T fun t _ => (cP L x hxL).sub continuousAt_const)
    exact cA.div cB hBx

  set m : ℕ := 2 * (T.card + 1)
  have eA : ∀ x, x ^ m * A x = (x ^ 2 * (L'.weierstrassP x - L'.weierstrassP w)) *
      ∏ t ∈ T, (x ^ 2 * (L.weierstrassP x - L.weierstrassP t)) := by
    intro x; simp only [hA, m, Finset.prod_mul_distrib, Finset.prod_const]; ring
  have eB : ∀ x, x ^ m * B x = (x ^ 2 * (L.weierstrassP x - L.weierstrassP w)) *
      ∏ t ∈ T, (x ^ 2 * (L.weierstrassP x - L.weierstrassP (w + t))) := by
    intro x; simp only [hB, m, Finset.prod_mul_distrib, Finset.prod_const]; ring
  have tA : Tendsto (fun x => x ^ m * A x) (𝓝[≠] 0) (𝓝 1) := by
    have := (tendsto_sq_mul L' (L'.weierstrassP w)).mul
      (tendsto_finsetProd T fun t _ => tendsto_sq_mul L (L.weierstrassP t))
    simp only [Finset.prod_const_one, mul_one] at this
    exact this.congr fun x => (eA x).symm
  have tB : Tendsto (fun x => x ^ m * B x) (𝓝[≠] 0) (𝓝 1) := by
    have := (tendsto_sq_mul L (L.weierstrassP w)).mul
      (tendsto_finsetProd T fun t _ => tendsto_sq_mul L (L.weierstrassP (w + t)))
    simp only [Finset.prod_const_one, mul_one] at this
    exact this.congr fun x => (eB x).symm
  have evB : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ^ m * B x ≠ 0 := tB.eventually_ne one_ne_zero
  have tF : Tendsto F (𝓝[≠] 0) (𝓝 1) := by
    have := tA.div tB one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x ^ m ≠ 0 := pow_ne_zero _ hx
    show x ^ m * A x / (x ^ m * B x) = A x / B x
    rw [mul_div_mul_left _ _ hx']
  have tF' : Tendsto F (𝓝[≠] 0) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [evB, IsogenyPAux.eventually_notMem L' 1 0 one_ne_zero] with x hx1 hx2
    rw [one_mul] at hx2
    exact (hc x (cont x hx2 (right_ne_zero_of_mul hx1))).symm
  have hc1 : c = 1 := tendsto_nhds_unique tF' tF

  by_cases hBz : B z = 0
  ·
    have hzL : z ∉ L.lattice := fun h => hz (hLL h)
    have key : ∀ a, a ∉ L.lattice → a - w ∈ L'.lattice → L.weierstrassP z = L.weierstrassP a →
        L'.weierstrassP z = L'.weierstrassP w := by
      intro a ha haw he
      rcases (pInjective L z a hzL ha).1 he with h | h
      · have h' : z - w ∈ L'.lattice := by
          have := L'.lattice.add_mem (hLL h) haw
          rwa [show z - a + (a - w) = z - w by ring] at this
        have := L'.weierstrassP_add_coe w ⟨z - w, h'⟩
        simp only at this
        rwa [add_sub_cancel] at this
      · have h' : z + w ∈ L'.lattice := by
          have := L'.lattice.sub_mem (hLL h) haw
          rwa [show z + a - (a - w) = z + w by ring] at this
        have := L'.weierstrassP_add_coe (-w) ⟨z + w, h'⟩
        simp only at this
        rw [show -w + (z + w) = z by ring, L'.weierstrassP_neg] at this
        exact this
    have hAz : A z = 0 := by
      simp only [hB, mul_eq_zero, Finset.prod_eq_zero_iff, sub_eq_zero] at hBz
      simp only [hA]
      rcases hBz with h | ⟨t, ht, h⟩
      · rw [key w hwL (by simp) h, sub_self, zero_mul]
      · rw [key (w + t) (hwt t ht) (by simpa using (hT1 t ht).1) h, sub_self, zero_mul]
    exact hAz.trans hBz.symm
  · have := hc z (cont z hz hBz)
    rw [hc1] at this
    exact (div_eq_one_iff_eq hBz).1 this

end GlobalTheory.HalfPeriodProduct
