import ReciprocityTheory.L2DbarEstimates.LeviForms.FixedB
import ReciprocityTheory.L2DbarEstimates.LeviForms.FixedC

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

/- English proof (translation)
Unfold `ev`. Check the signs of the components of the expression.
-/
theorem fx_ev_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev; positivity

/- English proof (translation)
Unfold `wgt lw`. Rewrite using `[Real.rpow_def_of_pos h, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fx_exp_neg_wgt {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ)
    (δ : ℝ) (x : M) (h : 0 < ev n g ph r x + δ ^ 2) :
    Real.exp (-wgt n g ph ph2 r j δ x) =
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * (ev n g ph r x + δ ^ 2) ^ (-(n : ℝ)) := by
  unfold wgt lw
  rw [Real.rpow_def_of_pos h, ← Real.exp_add]
  congr 1; ring

/- English proof (translation)
Establish `ht : 0 < ev n g ph r x` using `lt_of_lt_of_le (by positivity) hx`. Rewrite using `[fx_exp_neg_wgt n g ph ph2 r j δ x (by positivity)]`. Use `mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow_of_nonpos ht (by nlinarith [sq_nonneg δ]) (neg_nonpos.mpr (Nat.cast_nonneg n))`.
-/
theorem fx_exp_neg_wgt_le_shell {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ)
    (j : ℕ) (ε δ : ℝ) (hε : 0 < ε) (x : M) (hx : ε ^ 2 / 2 ≤ ev n g ph r x) :
    Real.exp (-wgt n g ph ph2 r j δ x) ≤
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ)) := by
  have ht : 0 < ev n g ph r x := lt_of_lt_of_le (by positivity) hx
  rw [fx_exp_neg_wgt n g ph ph2 r j δ x (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Real.rpow_le_rpow_of_nonpos ht (by nlinarith [sq_nonneg δ])
    (neg_nonpos.mpr (Nat.cast_nonneg n))

/- English proof (translation)
Take `⟨h1, ⟨Ct, hCt⟩, -, -⟩` from `hB g ph ph2 r j ε ε hr hε hbound`. Use `⟨(Real.exp Ct + 1) ^ 2 + Real.exp Ct, by positivity, fun x => ?_⟩` and prove the remaining obligations. Take `⟨hx1, hη1, -, -⟩` from `h1 x`. Establish `hlog : Real.log (eta n g ph r ε x) ≤ Ct`. Use `hCt x` as an intermediate fact.

Unfold `twist at this`. Rewrite `this` using `[abs_neg]`. Conclude with `(le_abs_self _).trans this`. Establish `hηle : eta n g ph r ε x ≤ Real.exp Ct` using `(Real.log_le_iff_le_exp (by linarith)).mp hlog`. Establish `hxη : xx n g ph r ε x ≤ eta n g ph r ε x`.

Unfold `eta`. Use `Real.log_nonneg hx1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Establish `h2 : xx n g ph r ε x + 1 ≤ Real.exp Ct + 1` using `by linarith`.

Establish `h3 : 0 ≤ xx n g ph r ε x + 1` using `by linarith`. Use polynomial arithmetic with `[mul_le_mul h2 h2 h3 (by positivity)]`.
-/
theorem fx_denom_bounds {M : Type*} (n : ℕ) (hB : BasicStatement n M) (g : Fin n → M → ℂ)
    (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (hbound : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) :
    ∃ Dm > 0, ∀ x, 0 < (xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x ∧
      (xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x ≤ Dm := by
  obtain ⟨h1, ⟨Ct, hCt⟩, -, -⟩ := hB g ph ph2 r j ε ε hr hε hbound
  refine ⟨(Real.exp Ct + 1) ^ 2 + Real.exp Ct, by positivity, fun x => ?_⟩
  obtain ⟨hx1, hη1, -, -⟩ := h1 x
  have hlog : Real.log (eta n g ph r ε x) ≤ Ct := by
    have := hCt x
    unfold twist at this
    rw [abs_neg] at this
    exact (le_abs_self _).trans this
  have hηle : eta n g ph r ε x ≤ Real.exp Ct :=
    (Real.log_le_iff_le_exp (by linarith)).mp hlog
  have hxη : xx n g ph r ε x ≤ eta n g ph r ε x := by
    unfold eta
    have := Real.log_nonneg hx1
    linarith
  refine ⟨by positivity, ?_⟩
  have h2 : xx n g ph r ε x + 1 ≤ Real.exp Ct + 1 := by linarith
  have h3 : 0 ≤ xx n g ph r ε x + 1 := by linarith
  nlinarith [mul_le_mul h2 h2 h3 (by positivity)]

/- English proof (translation)
Introduce `X g ph ph2 r j c W m χ ε hn hg hph hlph hph2 hlph2 hr hj hbound hS hJ hL hχ hε hε50 hm`. Establish `hz` using `X.isLocalHomeomorph`. Establish `hre : ∀ f : M → ℝ, SmoothR n X.z f → Continuous f` using `fun f hf => (Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hf)).congr fun x => by simp`. Establish `hphc` using `hre ph hph`. Establish `hph2c` using `hre ph2 hph2`.

Establish `hevc` using `fx_continuous_ev n X.z hz g hg ph hph r`. Establish `hJc` using `fx_continuous_jac n X.z hz g hg`. Establish `hψ₀s : SmoothR n X.z (fun x => ph2 x + ((n : ℝ) + j) * ph x)` using `SmoothR.add n X.z _ _ hph2 (SmoothR.mul n X.z _ _ (smoothR_const n X.z _) hph)`. Establish `hψ₀c : Continuous (fun x => ph2 x + ((n : ℝ) + j) * ph x)` using `hph2c.add (continuous_const.mul hphc)`. Establish `hF0m : Measurable (cutExt n X.z g ph r c W χ ε)` using `fx_measurable_cutExt n X.z hz g hg ph hph r c W m χ hχ ε hS hL`.

Establish `hshm : MeasurableSet (shell n g ph r ε)` using `((isClosed_le continuous_const hevc).inter (isClosed_le hevc continuous_const)).measurableSet`. Use `vol_isFiniteMeasureOnCompacts n X.z hz` as an intermediate fact. Establish `hKc : IsCompact (⋃ q ∈ zeroSet n g, closure (W q))` using `hS.isCompact_biUnion fun q hq => (hL.2 q hq).2.2.1`. Use `set s0 : ℝ := ∑ q ∈ hS.toFinset, ‖c q‖ with hs0`. Establish `hgt_le : ∀ x, ‖gt n X.z g c W x‖ ≤ s0 * ‖jac n X.z g x‖` using `fun x => by`.

Rewrite using `[hs0, Finset.sum_mul]`. Conclude with `fx_norm_gt_le n X.z g c W hS x`. Use `set G := ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z with hG`. Establish `hGfin : G < ⊤`. Rewrite using `[hG, ← lintegral_indicator hshm]`.

Use `fx_lintegral_lt_top_of_le_indicator _ _ hKc (fun x => (s0 * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * (ε ^ 2 / 2) ^ (-(n : ℝ))) (by fun_prop) _ fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hxs : x ∈ shell n g ph r ε`. Rewrite using `[indicator_of_mem hxs]`. Distinguish the cases in `hxK : x ∈ ⋃ q ∈ zeroSet n g, closure (W q)`. Rewrite using `[indicator_of_mem hxK]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h1 : ‖gt n X.z g c W x‖ ^ 2 ≤ (s0 * ‖jac n X.z g x‖) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) (hgt_le x) 2`. Establish `h2 : ev n g ph r x ^ (-(n : ℝ)) ≤ (ε ^ 2 / 2) ^ (-(n : ℝ))` using `Real.rpow_le_rpow_of_nonpos (by positivity) hxs.1 (neg_nonpos.mpr (Nat.cast_nonneg n))`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h2 (Real.rpow_nonneg (fx_ev_nonneg n g ph r x) _) (by positivity)`. Rewrite using `[fx_gt_eq_zero n X.z g c W hS x hxK]`.

Simplify using the standard rewrite rules. Rewrite using `[indicator_of_notMem hxs]`. Conclude with `bot_le`. Establish `hF0fin : otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) < ⊤`. Unfold `otNorm`.

Use `fx_lintegral_lt_top_of_le_indicator _ _ hKc (fun x => (s0 * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)) (by fun_prop) _ fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hxK : x ∈ ⋃ q ∈ zeroSet n g, closure (W q)`. Rewrite using `[indicator_of_mem hxK]`. Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (norm_nonneg _) ((fx_norm_cutExt_le n X.z g ph r c W χ hχ ε x).trans (hgt_le x)) 2`.

Establish `: cutExt n X.z g ph r c W χ ε x = 0`. Unfold `cutExt`. Rewrite using `[fx_gt_eq_zero n X.z g c W hS x hxK, mul_zero]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Use `set κ' : ℝ := 2 * Real.exp 1 * (1 + ε ^ 2) ^ n with hκ'`. Establish `hκ'pos : 0 < κ'` using `by positivity`. Use `set δ : ℕ → ℝ := fun k => ε / ((k : ℝ) + 2) with hδ`. Establish `hδpos : ∀ k, 0 < δ k` using `fun k => by simp only [hδ]; positivity`. Establish `hδle : ∀ k, δ k ≤ ε` using `fun k => by`.

Simplify using `only [hδ]`. Conclude with `div_le_self hε.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)`. Establish `hδlim : Tendsto δ atTop (𝓝 0)` using `tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)`. Establish `hApp` using `fun k => hA X g ph ph2 r j c W m χ ε (δ k) hg hph hlph hph2 hlph2 hr hj hbound hS hJ hL hχ hε hε50 hm (hδpos k) (hδle k)`. Use `choose Fk hFk hFkb using hApp`.

Establish `hFkm : ∀ k, Measurable (Fk k)` using `fun k => (Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hFk k))).measurable`. Establish `hshell : ∀ k, ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j (δ k) x)) ∂vol n X.z ≤ G`. Introduce `k`. Use `setLIntegral_mono' hshm fun x hx => ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (fx_exp_neg_wgt_le_shell n g ph ph2 r j ε (δ k) hε x hx.1) (sq_nonneg _)`. Establish `hdiff : ∀ k, otNorm n X.z ph ph2 j (fun x => cutExt n X.z g ph r c W χ ε x - Fk k x) ≤ ENNReal.ofReal (κ' * 72) * G`. Introduce `k`. Establish `h4` using `(hB g ph ph2 r j ε (δ k) hr hε hbound).2.2.2 hn (hδpos k) (hδle k)`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul hκ'pos.le]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = ENNReal.ofReal κ' * ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j (δ k) x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.

Use `_ ≤ ENNReal.ofReal κ' * (72 * G) := by gcongr`. Conclude with `(hFkb k).trans (by gcongr; exact hshell k)`. Use `_ = ENNReal.ofReal (κ' * 72) * G := by`. Rewrite using `[ENNReal.ofReal_mul hκ'pos.le, ENNReal.ofReal_ofNat, mul_assoc]`. Use `set B := ((ENNReal.ofReal (κ' * 72) * G) ^ (1 / 2 : ℝ) + otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) with hBdef`.

Establish `hBfin : B ≠ ⊤`. Use `ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin.ne)`. Conclude with `ENNReal.rpow_ne_top_of_nonneg (by norm_num) hF0fin.ne`. Use `set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x)))) with hμ`.

Establish `hot : ∀ f : M → ℂ, otNorm n X.z ph ph2 j f = eLpNorm f 2 μ ^ (2 : ℝ)` using `fun f => by`. Rewrite using `[fx_otNorm_eq_wint, fx_wint_eq_withDensity n X.z _ hψ₀c.measurable f, fx_lintegral_enorm_sq_eq]`. Establish `hsq : ∀ f : M → ℂ, eLpNorm f 2 μ = otNorm n X.z ph ph2 j f ^ (1 / 2 : ℝ)` using `fun f => by`. Rewrite using `[hot, ← ENNReal.rpow_mul]`. Evaluate the numerical expressions.

Establish `hFkB : ∀ k, otNorm n X.z ph ph2 j (Fk k) ≤ B`. Introduce `k`. Establish `htri : eLpNorm (Fk k) 2 μ ≤ eLpNorm (cutExt n X.z g ph r c W χ ε) 2 μ + eLpNorm (cutExt n X.z g ph r c W χ ε - Fk k) 2 μ`. Use `eLpNorm_sub_le (p := 2) (μ := μ) hF0m.aestronglyMeasurable (hF0m.sub (hFkm k)).aestronglyMeasurable one_le_two` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[hot, hBdef]`. Use `ENNReal.rpow_le_rpow ?_ (by norm_num)` and prove the remaining obligations. Rewrite `htri` using `[hsq (cutExt n X.z g ph r c W χ ε), hsq (cutExt n X.z g ph r c W χ ε - Fk k)]`.

Use `htri.trans ?_` and prove the remaining obligations. Rewrite using `[add_comm]`. Use `gcongr`. Conclude with `hdiff k`. Establish `hevm : Measurable (ev n g ph r)` using `hevc.measurable`.

Establish `hlwm : ∀ t, Measurable (lw n g ph r t)` using `fun t => by`. Unfold `lw`. Conclude with `(hevm.add_const _).log`. Establish `hxxm : Measurable (xx n g ph r ε)`. Unfold `xx`.

Conclude with `measurable_const.sub (hlwm ε)`. Establish `hetam : Measurable (eta n g ph r ε)`. Unfold `eta`. Conclude with `hxxm.add hxxm.log`. Establish `hwm : ∀ k, Measurable fun x => Real.exp (-wgt n g ph ph2 r j (δ k) x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x)` using `fun k => by`.

Establish `: Measurable (wgt n g ph ph2 r j (δ k))`. Unfold `wgt`. Conclude with `(hph2c.measurable.add (measurable_const.mul hphc.measurable)).add (measurable_const.mul (hlwm (δ k)))`. Conclude with `(Real.measurable_exp.comp this.neg).div (((hxxm.add_const 1).pow_const 2).add hetam)`. Take `⟨Dm, hDm, hD⟩` from `fx_denom_bounds n hB g ph ph2 r j ε hr hε hbound`.

Establish `hlim : ∀ p ∈ zeroSet n g, Tendsto (fun k => Fk k p) atTop (𝓝 (c p * jac n X.z g p))`. Introduce `p hp`. Take `⟨e, he, hpe, ρ, hρ, C1, hC1, A, hball, hbb⟩` from `fx_exists_ball_bounds n X.z hz g hg ph ph2 hph hph2 r hr j ε hε p hp (W p) (hL.2 p hp).1 (hL.2 p hp).2.1`. Establish `hF0p : cutExt n X.z g ph r c W χ ε p = c p * jac n X.z g p` using `fx_cutExt_eq_of_mem n X.z g ph r c W m χ hχ ε hε hS hL p hp p (hL.2 p hp).2.1 (by rw [fx_ev_eq_zero n g ph r p hp]; positivity)`. Establish `hδ2 : Tendsto (fun k => δ k ^ 2) atTop (𝓝[>] 0)`.

Use `tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩` and prove the remaining obligations. Simplify using `using hδlim.pow 2`. Conclude with `pow_pos (hδpos k) 2`. Establish `key` using `fx_tendsto_zero_of_weighted n hn hV X.z hz e he p hpe ρ hρ hball (Real.exp (-A) / Dm) C1 (72 * G.toReal) (by positivity) hC1 (fun k => δ k ^ 2) hδ2 (fun k x => cutExt n X.z g ph r c W χ ε x - Fk k x) (fun k x => Real.exp (-wgt n g ph ph2 r j (δ k) x) / ((xx n g ph r ε x + 1) ^ 2 …`. Use `key.const_sub (c p * jac n X.z g p)` as an intermediate fact.

Simplify `this` using `[hF0p]`. Introduce `k`. Establish `h1 : DifferentiableOn ℂ (fun y => c p * jac n X.z g (e.symm y) - Fk k (e.symm y)) (ball (X.z p) ρ)` using `(((fx_differentiableOn_jac_chart n X.z g hg e he).mono hball).const_mul (c p)).sub ((hFk k e he).mono hball)`. Use `h1.congr fun y hy => ?_` and prove the remaining obligations. Take `⟨hU, hev, -, -⟩` from `hbb y hy`.

Use `show cutExt n X.z g ph r c W χ ε (e.symm y) - Fk k (e.symm y) = _`. Rewrite using `[fx_cutExt_eq_of_mem n X.z g ph r c W m χ hχ ε hε hS hL p hp _ hU hev]`. Introduce `k y hy`. Take `⟨-, -, hevC, hψA⟩` from `hbb y hy`. Establish `hDx` using `hD (e.symm y)`.

Establish `hpos : 0 < ev n g ph r (e.symm y) + δ k ^ 2`. Use `fx_ev_nonneg n g ph r (e.symm y)` as an intermediate fact. Use `hδpos k` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[fx_exp_neg_wgt n g ph ph2 r j (δ k) _ hpos]`.

Establish `h1 : (C1 * ‖y - X.z p‖ ^ 2 + δ k ^ 2) ^ (-(n : ℝ)) ≤ (ev n g ph r (e.symm y) + δ k ^ 2) ^ (-(n : ℝ))` using `Real.rpow_le_rpow_of_nonpos hpos (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg n))`. Establish `h2 : Real.exp (-A) ≤ Real.exp (-ph2 (e.symm y) - ((n : ℝ) + j) * ph (e.symm y))` using `Real.exp_le_exp.mpr (by linarith)`. Establish `hR : 0 ≤ (C1 * ‖y - X.z p‖ ^ 2 + δ k ^ 2) ^ (-(n : ℝ))` using `Real.rpow_nonneg (by positivity) _`. Rewrite using `[div_mul_eq_mul_div, div_le_div_iff₀ hDm hDx.1]`. Conclude with `mul_le_mul (mul_le_mul h2 h1 hR (Real.exp_pos _).le) hDx.2 hDx.1.le (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hpos.le _))`.

Introduce `k`. Use `(hFkb k).trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hGfin.ne, ENNReal.ofReal_ofNat]`. Use `gcongr`. Conclude with `hshell k`.

Take `⟨Fl, hFl, hFlp, hFlB⟩` from `fx_exists_holo_limit n X _ hψ₀s hC hE hCVX (zeroSet n g) hS (fun p => c p * jac n X.z g p) B.toReal ENNReal.toReal_nonneg Fk hFk (fun k => by rw [← fx_otNorm_eq_wint, ENNReal.ofReal_toReal hBfin]; exact hFkB k) hlim`. Use `⟨Fl, hFl, hFlp, ?_⟩` and prove the remaining obligations. Rewrite using `[fx_otNorm_eq_wint]`. Conclude with `hFlB.trans (ENNReal.ofReal_toReal hBfin).le`.
-/
theorem fixed (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hA : ApplyStatement n M) (hB : BasicStatement n M) (hV : VanishStatement n)
    (hC : HoloClosedNeed n M) (hE : EvalNeed n M) (hCVX : CVXNeed.{u}) : FixedStatement n M := by
  intro X g ph ph2 r j c W m χ ε hn hg hph hlph hph2 hlph2 hr hj hbound hS hJ hL hχ hε hε50 hm
  have hz := X.isLocalHomeomorph
  have hre : ∀ f : M → ℝ, SmoothR n X.z f → Continuous f := fun f hf =>
    (Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hf)).congr fun x => by simp
  have hphc := hre ph hph
  have hph2c := hre ph2 hph2
  have hevc := fx_continuous_ev n X.z hz g hg ph hph r
  have hJc := fx_continuous_jac n X.z hz g hg
  have hψ₀s : SmoothR n X.z (fun x => ph2 x + ((n : ℝ) + j) * ph x) :=
    SmoothR.add n X.z _ _ hph2 (SmoothR.mul n X.z _ _ (smoothR_const n X.z _) hph)
  have hψ₀c : Continuous (fun x => ph2 x + ((n : ℝ) + j) * ph x) :=
    hph2c.add (continuous_const.mul hphc)
  have hF0m : Measurable (cutExt n X.z g ph r c W χ ε) :=
    fx_measurable_cutExt n X.z hz g hg ph hph r c W m χ hχ ε hS hL
  have hshm : MeasurableSet (shell n g ph r ε) :=
    ((isClosed_le continuous_const hevc).inter (isClosed_le hevc continuous_const)).measurableSet
  have := vol_isFiniteMeasureOnCompacts n X.z hz
  have hKc : IsCompact (⋃ q ∈ zeroSet n g, closure (W q)) :=
    hS.isCompact_biUnion fun q hq => (hL.2 q hq).2.2.1
  set s0 : ℝ := ∑ q ∈ hS.toFinset, ‖c q‖ with hs0
  have hgt_le : ∀ x, ‖gt n X.z g c W x‖ ≤ s0 * ‖jac n X.z g x‖ := fun x => by
    rw [hs0, Finset.sum_mul]; exact fx_norm_gt_le n X.z g c W hS x
  set G := ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z with hG
  have hGfin : G < ⊤ := by
    rw [hG, ← lintegral_indicator hshm]
    refine fx_lintegral_lt_top_of_le_indicator _ _ hKc
      (fun x => (s0 * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) *
        (ε ^ 2 / 2) ^ (-(n : ℝ))) (by fun_prop) _ fun x => ?_
    by_cases hxs : x ∈ shell n g ph r ε
    · rw [indicator_of_mem hxs]
      by_cases hxK : x ∈ ⋃ q ∈ zeroSet n g, closure (W q)
      · rw [indicator_of_mem hxK]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ‖gt n X.z g c W x‖ ^ 2 ≤ (s0 * ‖jac n X.z g x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hgt_le x) 2
        have h2 : ev n g ph r x ^ (-(n : ℝ)) ≤ (ε ^ 2 / 2) ^ (-(n : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hxs.1 (neg_nonpos.mpr (Nat.cast_nonneg n))
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h2
          (Real.rpow_nonneg (fx_ev_nonneg n g ph r x) _) (by positivity)
      · rw [fx_gt_eq_zero n X.z g c W hS x hxK]; simp
    · rw [indicator_of_notMem hxs]; exact bot_le
  have hF0fin : otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) < ⊤ := by
    unfold otNorm
    refine fx_lintegral_lt_top_of_le_indicator _ _ hKc
      (fun x => (s0 * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x))
      (by fun_prop) _ fun x => ?_
    by_cases hxK : x ∈ ⋃ q ∈ zeroSet n g, closure (W q)
    · rw [indicator_of_mem hxK]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((fx_norm_cutExt_le n X.z g ph r c W χ hχ ε x).trans (hgt_le x)) 2
    · have : cutExt n X.z g ph r c W χ ε x = 0 := by
        unfold cutExt; rw [fx_gt_eq_zero n X.z g c W hS x hxK, mul_zero]
      rw [this]; simp
  set κ' : ℝ := 2 * Real.exp 1 * (1 + ε ^ 2) ^ n with hκ'
  have hκ'pos : 0 < κ' := by positivity
  set δ : ℕ → ℝ := fun k => ε / ((k : ℝ) + 2) with hδ
  have hδpos : ∀ k, 0 < δ k := fun k => by simp only [hδ]; positivity
  have hδle : ∀ k, δ k ≤ ε := fun k => by
    simp only [hδ]
    exact div_le_self hε.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hApp := fun k => hA X g ph ph2 r j c W m χ ε (δ k) hg hph hlph hph2 hlph2 hr hj hbound hS
    hJ hL hχ hε hε50 hm (hδpos k) (hδle k)
  choose Fk hFk hFkb using hApp
  have hFkm : ∀ k, Measurable (Fk k) := fun k =>
    (Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hFk k))).measurable
  have hshell : ∀ k, ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
      Real.exp (-wgt n g ph ph2 r j (δ k) x)) ∂vol n X.z ≤ G := by
    intro k
    refine setLIntegral_mono' hshm fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (fx_exp_neg_wgt_le_shell n g ph ph2 r j ε (δ k) hε x hx.1)
      (sq_nonneg _)
  have hdiff : ∀ k, otNorm n X.z ph ph2 j (fun x => cutExt n X.z g ph r c W χ ε x - Fk k x) ≤
      ENNReal.ofReal (κ' * 72) * G := by
    intro k
    have h4 := (hB g ph ph2 r j ε (δ k) hr hε hbound).2.2.2 hn (hδpos k) (hδle k)
    calc otNorm n X.z ph ph2 j (fun x => cutExt n X.z g ph r c W χ ε x - Fk k x)
        ≤ ∫⁻ x, ENNReal.ofReal κ' * ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 *
            (Real.exp (-wgt n g ph ph2 r j (δ k) x) /
              ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul hκ'pos.le]
          refine ENNReal.ofReal_le_ofReal ?_
          calc _ ≤ ‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 *
                (κ' * (Real.exp (-wgt n g ph ph2 r j (δ k) x) /
                  ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) :=
                mul_le_mul_of_nonneg_left (h4 x) (sq_nonneg _)
            _ = _ := by ring
      _ = ENNReal.ofReal κ' * ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - Fk k x‖ ^ 2 *
            (Real.exp (-wgt n g ph ph2 r j (δ k) x) /
              ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal κ' * (72 * G) := by
          gcongr
          exact (hFkb k).trans (by gcongr; exact hshell k)
      _ = ENNReal.ofReal (κ' * 72) * G := by
          rw [ENNReal.ofReal_mul hκ'pos.le, ENNReal.ofReal_ofNat, mul_assoc]
  set B := ((ENNReal.ofReal (κ' * 72) * G) ^ (1 / 2 : ℝ) +
    otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) with hBdef
  have hBfin : B ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin.ne)
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hF0fin.ne
  set μ : Measure M := (vol n X.z).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x)))) with hμ
  have hot : ∀ f : M → ℂ, otNorm n X.z ph ph2 j f = eLpNorm f 2 μ ^ (2 : ℝ) := fun f => by
    rw [fx_otNorm_eq_wint, fx_wint_eq_withDensity n X.z _ hψ₀c.measurable f, fx_lintegral_enorm_sq_eq]
  have hsq : ∀ f : M → ℂ, eLpNorm f 2 μ = otNorm n X.z ph ph2 j f ^ (1 / 2 : ℝ) := fun f => by
    rw [hot, ← ENNReal.rpow_mul]; norm_num
  have hFkB : ∀ k, otNorm n X.z ph ph2 j (Fk k) ≤ B := by
    intro k
    have htri : eLpNorm (Fk k) 2 μ ≤ eLpNorm (cutExt n X.z g ph r c W χ ε) 2 μ +
        eLpNorm (cutExt n X.z g ph r c W χ ε - Fk k) 2 μ := by
      have := eLpNorm_sub_le (p := 2) (μ := μ) hF0m.aestronglyMeasurable
        (hF0m.sub (hFkm k)).aestronglyMeasurable one_le_two
      convert this using 2
      funext x; simp
    rw [hot, hBdef]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hsq (cutExt n X.z g ph r c W χ ε), hsq (cutExt n X.z g ph r c W χ ε - Fk k)] at htri
    refine htri.trans ?_
    rw [add_comm]
    gcongr
    exact hdiff k
  have hevm : Measurable (ev n g ph r) := hevc.measurable
  have hlwm : ∀ t, Measurable (lw n g ph r t) := fun t => by
    unfold lw; exact (hevm.add_const _).log
  have hxxm : Measurable (xx n g ph r ε) := by
    unfold xx; exact measurable_const.sub (hlwm ε)
  have hetam : Measurable (eta n g ph r ε) := by
    unfold eta; exact hxxm.add hxxm.log
  have hwm : ∀ k, Measurable fun x => Real.exp (-wgt n g ph ph2 r j (δ k) x) /
      ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x) := fun k => by
    have : Measurable (wgt n g ph ph2 r j (δ k)) := by
      unfold wgt
      exact (hph2c.measurable.add (measurable_const.mul hphc.measurable)).add
        (measurable_const.mul (hlwm (δ k)))
    exact (Real.measurable_exp.comp this.neg).div (((hxxm.add_const 1).pow_const 2).add hetam)
  obtain ⟨Dm, hDm, hD⟩ := fx_denom_bounds n hB g ph ph2 r j ε hr hε hbound
  have hlim : ∀ p ∈ zeroSet n g, Tendsto (fun k => Fk k p) atTop (𝓝 (c p * jac n X.z g p)) := by
    intro p hp
    obtain ⟨e, he, hpe, ρ, hρ, C1, hC1, A, hball, hbb⟩ := fx_exists_ball_bounds n X.z hz g hg ph ph2
      hph hph2 r hr j ε hε p hp (W p) (hL.2 p hp).1 (hL.2 p hp).2.1
    have hF0p : cutExt n X.z g ph r c W χ ε p = c p * jac n X.z g p :=
      fx_cutExt_eq_of_mem n X.z g ph r c W m χ hχ ε hε hS hL p hp p (hL.2 p hp).2.1
        (by rw [fx_ev_eq_zero n g ph r p hp]; positivity)
    have hδ2 : Tendsto (fun k => δ k ^ 2) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa using hδlim.pow 2
      · exact pow_pos (hδpos k) 2
    have key := fx_tendsto_zero_of_weighted n hn hV X.z hz e he p hpe ρ hρ hball
      (Real.exp (-A) / Dm) C1 (72 * G.toReal) (by positivity) hC1 (fun k => δ k ^ 2) hδ2
      (fun k x => cutExt n X.z g ph r c W χ ε x - Fk k x)
      (fun k x => Real.exp (-wgt n g ph ph2 r j (δ k) x) /
        ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))
      (fun k => hF0m.sub (hFkm k)) hwm ?_ ?_ ?_
    · have := key.const_sub (c p * jac n X.z g p)
      simpa [hF0p] using this
    · intro k
      have h1 : DifferentiableOn ℂ (fun y => c p * jac n X.z g (e.symm y) - Fk k (e.symm y))
          (ball (X.z p) ρ) :=
        (((fx_differentiableOn_jac_chart n X.z g hg e he).mono hball).const_mul (c p)).sub
          ((hFk k e he).mono hball)
      refine h1.congr fun y hy => ?_
      obtain ⟨hU, hev, -, -⟩ := hbb y hy
      show cutExt n X.z g ph r c W χ ε (e.symm y) - Fk k (e.symm y) = _
      rw [fx_cutExt_eq_of_mem n X.z g ph r c W m χ hχ ε hε hS hL p hp _ hU hev]
    · intro k y hy
      obtain ⟨-, -, hevC, hψA⟩ := hbb y hy
      have hDx := hD (e.symm y)
      have hpos : 0 < ev n g ph r (e.symm y) + δ k ^ 2 := by
        have := fx_ev_nonneg n g ph r (e.symm y); have := hδpos k; positivity
      rw [fx_exp_neg_wgt n g ph ph2 r j (δ k) _ hpos]
      have h1 : (C1 * ‖y - X.z p‖ ^ 2 + δ k ^ 2) ^ (-(n : ℝ)) ≤
          (ev n g ph r (e.symm y) + δ k ^ 2) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg n))
      have h2 : Real.exp (-A) ≤ Real.exp (-ph2 (e.symm y) - ((n : ℝ) + j) * ph (e.symm y)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hR : 0 ≤ (C1 * ‖y - X.z p‖ ^ 2 + δ k ^ 2) ^ (-(n : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hDm hDx.1]
      exact mul_le_mul (mul_le_mul h2 h1 hR (Real.exp_pos _).le) hDx.2 hDx.1.le
        (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hpos.le _))
    · intro k
      refine (hFkb k).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hGfin.ne, ENNReal.ofReal_ofNat]
      gcongr
      exact hshell k
  obtain ⟨Fl, hFl, hFlp, hFlB⟩ := fx_exists_holo_limit n X _ hψ₀s hC hE hCVX (zeroSet n g) hS
    (fun p => c p * jac n X.z g p) B.toReal ENNReal.toReal_nonneg Fk hFk
    (fun k => by rw [← fx_otNorm_eq_wint, ENNReal.ofReal_toReal hBfin]; exact hFkB k) hlim
  refine ⟨Fl, hFl, hFlp, ?_⟩
  rw [fx_otNorm_eq_wint]
  exact hFlB.trans (ENNReal.ofReal_toReal hBfin).le

end

end ReciprocityTheory.L2DbarEstimates.I
