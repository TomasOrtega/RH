import Mathlib
import GroundTheory.GlobalFields.TateThesis.Nonvanishing
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

open NumberField IsDedekindDomain Complex Topology Filter Set

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def primeSum (s : ℝ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), χ.coeffTerm (s : ℂ) v.asIdeal

def primeLogSum (s : ℝ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), -Complex.log (1 - χ.coeffTerm (s : ℂ) v.asIdeal)

/- English proof (translation)
Use `(χ.norm_coeffTerm_le _).trans ?_` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal`. Conclude with `(one_lt_absNorm_asIdeal v).le` after adjusting the coercions. Rewrite using `[ofReal_re]`. Use `inv_anti₀ (by positivity) ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_coeffTerm_asIdeal_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖χ.coeffTerm (s : ℂ) v.asIdeal‖ ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  refine (χ.norm_coeffTerm_le _).trans ?_
  have h1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
    exact_mod_cast (one_lt_absNorm_asIdeal v).le
  rw [ofReal_re]
  refine inv_anti₀ (by positivity) ?_
  calc (Ideal.absNorm v.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) :=
        (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1 hs

/- English proof (translation)
Use `(χ.norm_coeffTerm_asIdeal_le hs v).trans ?_` and prove the remaining obligations. Establish `h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal` using `by exact_mod_cast one_lt_absNorm_asIdeal v`. Rewrite using `[one_div]`. Conclude with `inv_anti₀ two_pos h2`.
-/
theorem norm_coeffTerm_asIdeal_le_half {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖χ.coeffTerm (s : ℂ) v.asIdeal‖ ≤ 1 / 2 := by
  refine (χ.norm_coeffTerm_asIdeal_le hs v).trans ?_
  have h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast one_lt_absNorm_asIdeal v
  rw [one_div]
  exact inv_anti₀ two_pos h2

/- English proof (translation)
The claim follows from `(χ.summable_norm_coeffTerm (by simpa using hs)).comp_injective fun _ _ h ↦ HeightOneSpectrum.ext h`.
-/
theorem summable_norm_coeffTerm_asIdeal {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) ↦ ‖χ.coeffTerm (s : ℂ) v.asIdeal‖ :=
  (χ.summable_norm_coeffTerm (by simpa using hs)).comp_injective fun _ _ h ↦ HeightOneSpectrum.ext h

/- English proof (translation)
Establish `hs' : 1 < (s : ℂ).re` using `by simpa using hs`. Use `set x : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ χ.coeffTerm (s : ℂ) v.asIdeal with hx`. Establish `hlt : ∀ v, ‖x v‖ < 1` using `fun v ↦ (χ.norm_coeffTerm_asIdeal_le_half hs.le v).trans_lt (by norm_num)`. Establish `hne : ∀ v, 1 - x v ≠ 0`. Introduce `v h`.

Establish `h1 : x v = 1` using `(sub_eq_zero.1 h).symm`. Establish `h2` using `hlt v`. Rewrite `h2` using `[h1, norm_one]`. Conclude with `lt_irrefl _ h2`. Establish `hxs : Summable x` using `Summable.of_norm (χ.summable_norm_coeffTerm_asIdeal hs)`.

Establish `hlog : Summable fun v ↦ Complex.log (1 - x v)` using `(Complex.summable_log_one_add_of_summable hxs.neg).congr fun v ↦ by rw [sub_eq_add_neg]`. Establish `hP : HasProd (fun v ↦ 1 - x v) (Complex.exp (∑' v, Complex.log (1 - x v)))` using `Complex.hasProd_of_hasSum_log hne hlog.hasSum`. Establish `hL : HasProd (fun v ↦ (1 - x v)⁻¹) (χ.LFunction s)`. Rewrite using `[χ.LFunction_eq_tsum_coeffTerm hs']`. Conclude with `hasProd_euler _ (χ.summable_norm_coeffTerm hs') (χ.coeffTerm_bot _)`.

Establish `h1` using `hL.mul hP`. Establish `h2 : (fun v ↦ (1 - x v)⁻¹ * (1 - x v)) = fun _ ↦ (1 : ℂ)`. Use function extensionality and compare the values at `fun v ↦ inv_mul_cancel₀ (hne v)`. Rewrite `h1` using `[h2]`. Establish `h3` using `h1.unique hasProd_one`.

Rewrite using `[primeLogSum, tsum_neg, Complex.exp_neg]`. Conclude with `inv_eq_of_mul_eq_one_left h3`.
-/
theorem exp_primeLogSum {s : ℝ} (hs : 1 < s) : Complex.exp (χ.primeLogSum s) = χ.LFunction s := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  set x : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ χ.coeffTerm (s : ℂ) v.asIdeal with hx
  have hlt : ∀ v, ‖x v‖ < 1 := fun v ↦
    (χ.norm_coeffTerm_asIdeal_le_half hs.le v).trans_lt (by norm_num)
  have hne : ∀ v, 1 - x v ≠ 0 := by
    intro v h
    have h1 : x v = 1 := (sub_eq_zero.1 h).symm
    have h2 := hlt v
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hxs : Summable x := Summable.of_norm (χ.summable_norm_coeffTerm_asIdeal hs)
  have hlog : Summable fun v ↦ Complex.log (1 - x v) :=
    (Complex.summable_log_one_add_of_summable hxs.neg).congr fun v ↦ by rw [sub_eq_add_neg]
  have hP : HasProd (fun v ↦ 1 - x v) (Complex.exp (∑' v, Complex.log (1 - x v))) :=
    Complex.hasProd_of_hasSum_log hne hlog.hasSum
  have hL : HasProd (fun v ↦ (1 - x v)⁻¹) (χ.LFunction s) := by
    rw [χ.LFunction_eq_tsum_coeffTerm hs']
    exact hasProd_euler _ (χ.summable_norm_coeffTerm hs') (χ.coeffTerm_bot _)
  have h1 := hL.mul hP
  have h2 : (fun v ↦ (1 - x v)⁻¹ * (1 - x v)) = fun _ ↦ (1 : ℂ) :=
    funext fun v ↦ inv_mul_cancel₀ (hne v)
  rw [h2] at h1
  have h3 := h1.unique hasProd_one
  rw [primeLogSum, tsum_neg, Complex.exp_neg]
  exact inv_eq_of_mul_eq_one_left h3

/- English proof (translation)
Introduce `s₀ hs₀`. Establish `hs₀' : (1 : ℝ) < s₀` using `hs₀`. Establish `hσ1 : 1 < (1 + s₀) / 2` using `by linarith`. Establish `hσs : (1 + s₀) / 2 < s₀` using `by linarith`. Establish `hc : ContinuousOn χ.primeLogSum (Ioi ((1 + s₀) / 2))`.

Use `continuousOn_tsum (u := fun v : HeightOneSpectrum (𝓞 K) ↦ 3 / 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ ((1 + s₀) / 2))⁻¹) (fun v ↦ ?_) ?_ (fun v s hs ↦ ?_)` and prove the remaining obligations. Establish `hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0`. Conclude with `(one_pos.trans (one_lt_absNorm_asIdeal v)).ne'` after adjusting the coercions. Introduce `s hs`. Establish `hs1 : (1 : ℝ) ≤ s`.

Establish `: (1 + s₀) / 2 < s` using `hs`. Combine the linear equalities and inequalities to obtain the conclusion. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Establish `hcp : ContinuousAt (fun t : ℝ ↦ (Ideal.absNorm v.asIdeal : ℂ) ^ (t : ℂ)) s` using `(continuous_ofReal.const_cpow (Or.inl hN)).continuousAt`. Establish `hden : (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ) ≠ 0` using `fun h ↦ hN ((cpow_eq_zero_iff _ _).1 h).1`.

Establish `hterm : ContinuousAt (fun t : ℝ ↦ χ.coeffTerm (t : ℂ) v.asIdeal) s`. Simplify using `only [coeffTerm_apply]`. Conclude with `continuousAt_const.div hcp hden`. Use `(ContinuousAt.clog (continuousAt_const.sub hterm) ?_).neg` and prove the remaining obligations. Establish `hm` using `mem_slitPlane_of_norm_lt_one (z := -χ.coeffTerm (s : ℂ) v.asIdeal) (by rw [norm_neg]; exact (χ.norm_coeffTerm_asIdeal_le_half hs1 v).trans_lt (by norm_num))`.

Rewrite `hm` using `[← sub_eq_add_neg]`. Then use the resulting hypothesis. Conclude with `((summable_absNorm_rpow_inv hσ1).comp_injective fun _ _ h ↦ HeightOneSpectrum.ext h).mul_left _`. Establish `hs' : (1 + s₀) / 2 < s` using `hs`. Establish `hs1 : (1 : ℝ) ≤ s` using `by linarith`. Establish `h1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal`.

Conclude with `(one_lt_absNorm_asIdeal v).le` after adjusting the coercions. Rewrite using `[norm_neg, sub_eq_add_neg]`. Use `(norm_log_one_add_half_le_self (by rw [norm_neg]; exact χ.norm_coeffTerm_asIdeal_le_half hs1 v)).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`. Use `mul_le_mul_of_nonneg_left ((χ.norm_coeffTerm_le _).trans ?_) (by norm_num)` and prove the remaining obligations.

Rewrite using `[ofReal_re]`. Conclude with `inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hs'.le)`. Conclude with `(hc.continuousAt (Ioi_mem_nhds hσs)).continuousWithinAt`.
-/
theorem continuousOn_primeLogSum : ContinuousOn χ.primeLogSum (Ioi 1) := by
  intro s₀ hs₀
  have hs₀' : (1 : ℝ) < s₀ := hs₀
  have hσ1 : 1 < (1 + s₀) / 2 := by linarith
  have hσs : (1 + s₀) / 2 < s₀ := by linarith
  have hc : ContinuousOn χ.primeLogSum (Ioi ((1 + s₀) / 2)) := by
    refine continuousOn_tsum
      (u := fun v : HeightOneSpectrum (𝓞 K) ↦
        3 / 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ ((1 + s₀) / 2))⁻¹) (fun v ↦ ?_) ?_
      (fun v s hs ↦ ?_)
    · have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        exact_mod_cast (one_pos.trans (one_lt_absNorm_asIdeal v)).ne'
      intro s hs
      have hs1 : (1 : ℝ) ≤ s := by
        have : (1 + s₀) / 2 < s := hs
        linarith
      refine ContinuousAt.continuousWithinAt ?_
      have hcp : ContinuousAt (fun t : ℝ ↦ (Ideal.absNorm v.asIdeal : ℂ) ^ (t : ℂ)) s :=
        (continuous_ofReal.const_cpow (Or.inl hN)).continuousAt
      have hden : (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ) ≠ 0 := fun h ↦
        hN ((cpow_eq_zero_iff _ _).1 h).1
      have hterm : ContinuousAt (fun t : ℝ ↦ χ.coeffTerm (t : ℂ) v.asIdeal) s := by
        simp only [coeffTerm_apply]
        exact continuousAt_const.div hcp hden
      refine (ContinuousAt.clog (continuousAt_const.sub hterm) ?_).neg
      have hm := mem_slitPlane_of_norm_lt_one (z := -χ.coeffTerm (s : ℂ) v.asIdeal)
        (by rw [norm_neg]; exact (χ.norm_coeffTerm_asIdeal_le_half hs1 v).trans_lt (by norm_num))
      rwa [← sub_eq_add_neg] at hm
    · exact ((summable_absNorm_rpow_inv hσ1).comp_injective
        fun _ _ h ↦ HeightOneSpectrum.ext h).mul_left _
    · have hs' : (1 + s₀) / 2 < s := hs
      have hs1 : (1 : ℝ) ≤ s := by linarith
      have h1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
        exact_mod_cast (one_lt_absNorm_asIdeal v).le
      rw [norm_neg, sub_eq_add_neg]
      refine (norm_log_one_add_half_le_self
        (by rw [norm_neg]; exact χ.norm_coeffTerm_asIdeal_le_half hs1 v)).trans ?_
      rw [norm_neg]
      refine mul_le_mul_of_nonneg_left ((χ.norm_coeffTerm_le _).trans ?_) (by norm_num)
      rw [ofReal_re]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hs'.le)
  exact (hc.continuousAt (Ioi_mem_nhds hσs)).continuousWithinAt

/- English proof (translation)
Establish `hw1 : Tendsto (fun s : ℝ ↦ χ.LFunction s / L₁) (𝓝[>] 1) (𝓝 1)`. Use `hL.div_const L₁` as an intermediate fact. Rewrite `this` using `[div_self hL₁]`. Then use the resulting hypothesis. Establish `hball : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), χ.LFunction s / L₁ ∈ Metric.ball (1 : ℂ) 1` using `hw1 (Metric.ball_mem_nhds _ one_pos)`. Take `⟨u, hu1, hu⟩` from `mem_nhdsGT_iff_exists_Ioo_subset.1 hball`.

Establish `hu1' : (1 : ℝ) < u` using `hu1`. Establish `hslit : ∀ s ∈ Ioo (1 : ℝ) u, χ.LFunction s / L₁ ∈ slitPlane` using `fun s hs ↦ by`. Establish `h : χ.LFunction s / L₁ ∈ Metric.ball (1 : ℂ) 1` using `hu hs`. Rewrite `h` using `[Metric.mem_ball, dist_eq_norm]`. Use `mem_slitPlane_of_norm_lt_one h` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hLc : ∀ s ∈ Ioo (1 : ℝ) u, ContinuousAt (fun s : ℝ ↦ χ.LFunction s) s` using `fun s hs ↦ by`. Establish `hs' : 1 < ((s : ℝ) : ℂ).re` using `by simpa using hs.1`. Establish `hd` using `(χ.differentiableOn_LFunction _ hs').differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hs')`. Conclude with `hd.continuousAt.comp continuous_ofReal.continuousAt`.

Establish `hs₀ : (1 + u) / 2 ∈ Ioo (1 : ℝ) u` using `⟨by linarith, by linarith⟩`. Use `set s₀ := (1 + u) / 2`. Use `set c := χ.primeLogSum s₀ - Complex.log (χ.LFunction s₀ / L₁) with hc`. Establish `heq : EqOn χ.primeLogSum (fun s : ℝ ↦ Complex.log (χ.LFunction s / L₁) + c) (Ioo 1 u)`. Use `isCoveringMap_exp.eqOn_of_comp_eqOn isPreconnected_Ioo (χ.continuousOn_primeLogSum.mono fun s hs ↦ hs.1) (fun s hs ↦ ((ContinuousAt.clog ((hLc s hs).div_const L₁) (hslit s hs)).add continuousAt_const).continuousWithinAt) (fun s hs ↦ ?_) hs₀ (by rw [hc]; ring)` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Function.comp_apply]`. Rewrite using `[Complex.exp_add, Complex.exp_log (slitPlane_ne_zero (hslit s hs)), hc, Complex.exp_sub, Complex.exp_log (slitPlane_ne_zero (hslit s₀ hs₀)), χ.exp_primeLogSum hs.1, χ.exp_primeLogSum hs₀.1]`. Establish `h0 : χ.LFunction s₀ ≠ 0` using `χ.LFunction_ne_zero (by simpa using hs₀.1)`. Clear the denominators using the available nonvanishing facts.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hlim : Tendsto (fun s : ℝ ↦ Complex.log (χ.LFunction s / L₁) + c) (𝓝[>] 1) (𝓝 (Complex.log 1 + c))` using `((continuousAt_clog (by simp)).tendsto.comp hw1).add tendsto_const_nhds`. Rewrite `hlim` using `[Complex.log_one, zero_add]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsGT hu1'] with s hs using (heq hs).symm`.
-/
theorem exists_tendsto_primeLogSum {L₁ : ℂ} (hL₁ : L₁ ≠ 0)
    (hL : Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 L₁)) :
    ∃ c : ℂ, Tendsto χ.primeLogSum (𝓝[>] 1) (𝓝 c) := by
  have hw1 : Tendsto (fun s : ℝ ↦ χ.LFunction s / L₁) (𝓝[>] 1) (𝓝 1) := by
    have := hL.div_const L₁
    rwa [div_self hL₁] at this
  have hball : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), χ.LFunction s / L₁ ∈ Metric.ball (1 : ℂ) 1 :=
    hw1 (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hball
  have hu1' : (1 : ℝ) < u := hu1
  have hslit : ∀ s ∈ Ioo (1 : ℝ) u, χ.LFunction s / L₁ ∈ slitPlane := fun s hs ↦ by
    have h : χ.LFunction s / L₁ ∈ Metric.ball (1 : ℂ) 1 := hu hs
    rw [Metric.mem_ball, dist_eq_norm] at h
    have := mem_slitPlane_of_norm_lt_one h
    rwa [add_sub_cancel] at this
  have hLc : ∀ s ∈ Ioo (1 : ℝ) u, ContinuousAt (fun s : ℝ ↦ χ.LFunction s) s := fun s hs ↦ by
    have hs' : 1 < ((s : ℝ) : ℂ).re := by simpa using hs.1
    have hd := (χ.differentiableOn_LFunction _ hs').differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hs')
    exact hd.continuousAt.comp continuous_ofReal.continuousAt
  have hs₀ : (1 + u) / 2 ∈ Ioo (1 : ℝ) u := ⟨by linarith, by linarith⟩
  set s₀ := (1 + u) / 2
  set c := χ.primeLogSum s₀ - Complex.log (χ.LFunction s₀ / L₁) with hc
  have heq : EqOn χ.primeLogSum (fun s : ℝ ↦ Complex.log (χ.LFunction s / L₁) + c) (Ioo 1 u) := by
    refine isCoveringMap_exp.eqOn_of_comp_eqOn isPreconnected_Ioo
      (χ.continuousOn_primeLogSum.mono fun s hs ↦ hs.1)
      (fun s hs ↦ ((ContinuousAt.clog ((hLc s hs).div_const L₁) (hslit s hs)).add
        continuousAt_const).continuousWithinAt) (fun s hs ↦ ?_) hs₀ (by rw [hc]; ring)
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [Complex.exp_add, Complex.exp_log (slitPlane_ne_zero (hslit s hs)), hc, Complex.exp_sub,
      Complex.exp_log (slitPlane_ne_zero (hslit s₀ hs₀)), χ.exp_primeLogSum hs.1,
      χ.exp_primeLogSum hs₀.1]
    have h0 : χ.LFunction s₀ ≠ 0 := χ.LFunction_ne_zero (by simpa using hs₀.1)
    field_simp
  refine ⟨c, ?_⟩
  have hlim : Tendsto (fun s : ℝ ↦ Complex.log (χ.LFunction s / L₁) + c) (𝓝[>] 1)
      (𝓝 (Complex.log 1 + c)) :=
    ((continuousAt_clog (by simp)).tendsto.comp hw1).add tendsto_const_nhds
  rw [Complex.log_one, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hu1'] with s hs using (heq hs).symm

/- English proof (translation)
Take `⟨c, hc⟩` from `χ.exists_tendsto_primeLogSum hL₁ hL`. Establish `hB : Summable fun v : HeightOneSpectrum (𝓞 K) ↦ ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹` using `(summable_absNorm_rpow_inv (K := K) one_lt_two).comp_injective fun _ _ h ↦ HeightOneSpectrum.ext h`. Use `set B := ∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹`. Establish `hnear : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖χ.primeLogSum s‖ ≤ ‖c‖ + 1` using `by filter_upwards [hc.norm.eventually (gt_mem_nhds (lt_add_one ‖c‖))] with s hs using hs.le`. Use `isBoundedUnder_of_eventually_le (a := ‖c‖ + 1 + B) ?_` and prove the remaining obligations.

Use `filter_upwards [hnear, self_mem_nhdsWithin] with s hs hs1`. Establish `hs1' : (1 : ℝ) < s` using `hs1`. Establish `hdiff : ‖χ.primeLogSum s - χ.primeSum s‖ ≤ B`. Establish `hP : Summable fun v : HeightOneSpectrum (𝓞 K) ↦ χ.coeffTerm (s : ℂ) v.asIdeal` using `Summable.of_norm (χ.summable_norm_coeffTerm_asIdeal hs1')`. Establish `hF : Summable fun v : HeightOneSpectrum (𝓞 K) ↦ -Complex.log (1 - χ.coeffTerm (s : ℂ) v.asIdeal)`.

Use `Summable.of_norm_bounded ((χ.summable_norm_coeffTerm_asIdeal hs1').mul_left (3 / 2)) fun v ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_neg, sub_eq_add_neg]`. Use `(norm_log_one_add_half_le_self (by rw [norm_neg]; exact χ.norm_coeffTerm_asIdeal_le_half hs1'.le v)).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`. Rewrite using `[primeLogSum, primeSum, ← hF.tsum_sub hP]`.

Use `tsum_of_norm_bounded hB.hasSum fun v ↦ ?_` and prove the remaining obligations. Use `set a := χ.coeffTerm (s : ℂ) v.asIdeal`. Establish `ha` using `χ.norm_coeffTerm_asIdeal_le_half hs1'.le v`. Establish `ha'` using `χ.norm_coeffTerm_asIdeal_le hs1'.le v`. Establish `e : -Complex.log (1 - a) - a = -(Complex.log (1 + -a) - -a)`.

Rewrite using `[sub_eq_add_neg 1 a]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_neg]`. Use `(norm_log_one_add_sub_self_le (by rw [norm_neg]; linarith)).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`.

Establish `ht0 : 0 ≤ ‖a‖` using `norm_nonneg _`. Establish `hinv : (1 - ‖a‖)⁻¹ ≤ 2`. Rewrite using `[inv_le_comm₀ (by linarith) two_pos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN0 : (0 : ℝ) < Ideal.absNorm v.asIdeal`.

Conclude with `one_pos.trans (one_lt_absNorm_asIdeal v)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_sub_cancel]`. Use `_ ≤ ‖χ.primeLogSum s‖ + ‖χ.primeLogSum s - χ.primeSum s‖ := norm_sub_le _ _`.

Use `_ ≤ ‖c‖ + 1 + B := add_le_add hs hdiff`.
-/
theorem isBoundedUnder_norm_primeSum {L₁ : ℂ} (hL₁ : L₁ ≠ 0)
    (hL : Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 L₁)) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s ↦ ‖χ.primeSum s‖ := by
  obtain ⟨c, hc⟩ := χ.exists_tendsto_primeLogSum hL₁ hL
  have hB : Summable fun v : HeightOneSpectrum (𝓞 K) ↦
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹ :=
    (summable_absNorm_rpow_inv (K := K) one_lt_two).comp_injective
      fun _ _ h ↦ HeightOneSpectrum.ext h
  set B := ∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹
  have hnear : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖χ.primeLogSum s‖ ≤ ‖c‖ + 1 := by
    filter_upwards [hc.norm.eventually (gt_mem_nhds (lt_add_one ‖c‖))] with s hs using hs.le
  refine isBoundedUnder_of_eventually_le (a := ‖c‖ + 1 + B) ?_
  filter_upwards [hnear, self_mem_nhdsWithin] with s hs hs1
  have hs1' : (1 : ℝ) < s := hs1
  have hdiff : ‖χ.primeLogSum s - χ.primeSum s‖ ≤ B := by
    have hP : Summable fun v : HeightOneSpectrum (𝓞 K) ↦ χ.coeffTerm (s : ℂ) v.asIdeal :=
      Summable.of_norm (χ.summable_norm_coeffTerm_asIdeal hs1')
    have hF : Summable fun v : HeightOneSpectrum (𝓞 K) ↦
        -Complex.log (1 - χ.coeffTerm (s : ℂ) v.asIdeal) := by
      refine Summable.of_norm_bounded ((χ.summable_norm_coeffTerm_asIdeal hs1').mul_left (3 / 2))
        fun v ↦ ?_
      rw [norm_neg, sub_eq_add_neg]
      refine (norm_log_one_add_half_le_self
        (by rw [norm_neg]; exact χ.norm_coeffTerm_asIdeal_le_half hs1'.le v)).trans ?_
      rw [norm_neg]
    rw [primeLogSum, primeSum, ← hF.tsum_sub hP]
    refine tsum_of_norm_bounded hB.hasSum fun v ↦ ?_
    set a := χ.coeffTerm (s : ℂ) v.asIdeal
    have ha := χ.norm_coeffTerm_asIdeal_le_half hs1'.le v
    have ha' := χ.norm_coeffTerm_asIdeal_le hs1'.le v
    have e : -Complex.log (1 - a) - a = -(Complex.log (1 + -a) - -a) := by
      rw [sub_eq_add_neg 1 a]
      ring
    rw [e, norm_neg]
    refine (norm_log_one_add_sub_self_le (by rw [norm_neg]; linarith)).trans ?_
    rw [norm_neg]
    have ht0 : 0 ≤ ‖a‖ := norm_nonneg _
    have hinv : (1 - ‖a‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]
      linarith
    have hN0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
      exact_mod_cast one_pos.trans (one_lt_absNorm_asIdeal v)
    calc ‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2 ≤ ‖a‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖a‖ ^ 2 := by ring
      _ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ 2 := by gcongr
      _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_two, inv_pow]
  calc ‖χ.primeSum s‖ = ‖χ.primeLogSum s - (χ.primeLogSum s - χ.primeSum s)‖ := by
        rw [sub_sub_cancel]
    _ ≤ ‖χ.primeLogSum s‖ + ‖χ.primeLogSum s - χ.primeSum s‖ := norm_sub_le _ _
    _ ≤ ‖c‖ + 1 + B := add_le_add hs hdiff

/- English proof (translation)
Introduce and unpack `⟨τ, hτ⟩`. Establish `h0 : τ * n = 0`. Use `eq_zero_of_forall_ideleModule_cpow_eq_one (K := K) fun x ↦ ?_` and prove the remaining obligations. Establish `h1 : (((χ ^ n).toIdele x : Circle) : ℂ) = 1`. Rewrite using `[hχn, toIdele_apply]`.

Both sides reduce to the same expression. Rewrite `h1` using `[pow_toIdele, Circle.coe_pow, hτ x, ← cpow_nat_mul]`. Rewrite using `[← h1]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `hτ0 : τ = 0`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (by exact_mod_cast h) hn`. Apply `hχ` to reduce the goal to its premises.

Use extensionality with `c`. Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective K c`. Establish `h` using `hτ x`. Rewrite `h` using `[hτ0, ofReal_zero, zero_mul, cpow_zero, toIdele_apply]`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem not_exists_cpow_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (hχn : χ ^ n = 1) (hχ : χ ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  rintro ⟨τ, hτ⟩
  have h0 : τ * n = 0 := by
    refine eq_zero_of_forall_ideleModule_cpow_eq_one (K := K) fun x ↦ ?_
    have h1 : (((χ ^ n).toIdele x : Circle) : ℂ) = 1 := by
      rw [hχn, toIdele_apply]
      rfl
    rw [pow_toIdele, Circle.coe_pow, hτ x, ← cpow_nat_mul] at h1
    rw [← h1]
    push_cast
    ring_nf
  have hτ0 : τ = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hn
  apply hχ
  ext c
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have h := hτ x
  rw [hτ0, ofReal_zero, zero_mul, cpow_zero, toIdele_apply] at h
  rw [h]
  rfl

/- English proof (translation)
Take `⟨G, hG, hGL⟩` from `χ.exists_LFunction_continuation hχ`. Use `⟨G 1, χ.continuation_ne_zero_of_one_le_re hχ hG hGL (by simp), ?_⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ))`. Use `(continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 1))` as an intermediate fact. Rewrite `this` using `[ofReal_one]`. Then use the resulting hypothesis.

Use `((hG 1).continuousAt.tendsto.comp h1).congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Conclude with `hGL s (by simpa using hs)`.
-/
theorem exists_tendsto_LFunction_of_not_exists
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∃ L₁ : ℂ, L₁ ≠ 0 ∧ Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 L₁) := by
  obtain ⟨G, hG, hGL⟩ := χ.exists_LFunction_continuation hχ
  refine ⟨G 1, χ.continuation_ne_zero_of_one_le_re hχ hG hGL (by simp), ?_⟩
  have h1 : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    rwa [ofReal_one] at this
  refine ((hG 1).continuousAt.tendsto.comp h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hGL s (by simpa using hs)

/- English proof (translation)
Take `⟨L₁, hL₁, hL⟩` from `χ.exists_tendsto_LFunction_of_not_exists (χ.not_exists_cpow_of_pow_eq_one hn hχn hχ)`. Conclude with `χ.isBoundedUnder_norm_primeSum hL₁ hL`.
-/
theorem isBoundedUnder_norm_primeSum_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (hχn : χ ^ n = 1)
    (hχ : χ ≠ 1) : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s ↦ ‖χ.primeSum s‖ := by
  obtain ⟨L₁, hL₁, hL⟩ :=
    χ.exists_tendsto_LFunction_of_not_exists (χ.not_exists_cpow_of_pow_eq_one hn hχn hχ)
  exact χ.isBoundedUnder_norm_primeSum hL₁ hL

end HeckeCharacter

end

end GroundTheory.Global
