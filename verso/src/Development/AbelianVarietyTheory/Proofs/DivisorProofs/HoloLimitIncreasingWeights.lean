import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

/- English proof (translation)
Introduce `n M _ _ _ _ _ X F0 om c p q Fk B hF0 hom hc hombd hp hpanti hpq hF hBtop hB`. Establish `hz` using `X.isLocalHomeomorph`. Establish `hpc : ∀ k, Continuous (p k)` using `fun k => by`. Use `Complex.continuous_re.comp (Smooth.continuous n X.z hz _ (hp k))` as an intermediate fact. Conclude with `this.congr fun x => by simp`.

Establish `hcont : ∀ G : M → ℂ, Holo n X.z G → Continuous G` using `fun G hG => Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hG)`. Establish `hC : ReciprocityTheory.L2DbarEstimates.I.HoloClosedNeed n M` using `ReciprocityTheory.L2DbarEstimates.F.holoClosedNeed n M (regMAll n M)`. Establish `hE : ReciprocityTheory.L2DbarEstimates.I.EvalNeed n M` using `ReciprocityTheory.L2DbarEstimates.F.evalNeed n M C.mv`. Use `set Iw : ℕ → (M → ℂ) → ℝ≥0∞ := fun k G => ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z with hIw`. Use `set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-p 0 x))) with hμ`.

Establish `hkey : ∀ f : M → ℂ, wint n X.z f (p 0) = eLpNorm f 2 μ ^ (2 : ℝ)` using `fun f => by`. Rewrite using `[ReciprocityTheory.L2DbarEstimates.I.fx_wint_eq_withDensity n X.z (p 0) (hpc 0).measurable f, ReciprocityTheory.L2DbarEstimates.I.fx_lintegral_enorm_sq_eq]`. Establish `hN : ∀ (v : Lp ℂ 2 μ) (G : M → ℂ), (v : M → ℂ) =ᵐ[μ] G → wint n X.z G (p 0) = ENNReal.ofReal (‖v‖ ^ 2)` using `fun v G h => by`. Rewrite using `[hkey, ReciprocityTheory.L2DbarEstimates.I.fx_lp_norm_sq_eq μ v G h]`. Establish `hmono : ∀ G k k', k ≤ k' → Iw k G ≤ Iw k' G` using `fun G k k' h => by`.

Use `lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h1 : Real.exp (-p k x) ≤ Real.exp (-p k' x)` using `Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))`. Establish `h0 : 0 ≤ om x` using `hc.le.trans (hombd x).1`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)`. Establish `hmeas : ∀ G : M → ℂ, Continuous G → ∀ (w : M → ℝ), Continuous w → Measurable fun x => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-w x)))` using `fun G hG w hw => (ENNReal.continuous_ofReal.comp (((hF0.sub hG).norm.pow 2).mul (hom.mul (Real.continuous_exp.comp hw.neg)))).measurable`.

Establish `hbd : ∀ G : M → ℂ, Continuous G → wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤ ENNReal.ofReal (2 / c) * (Iw 0 G + Iw 0 (Fk 0))` using `fun G hG => by`. Rewrite using `[hIw, ← lintegral_add_left (hmeas G hG _ (hpc 0)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Establish `ha : 0 ≤ ‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p 0 x))`. Use `hc.le.trans (hombd x).1` as an intermediate fact.

Check the signs of the components of the expression. Establish `hb : 0 ≤ ‖F0 x - Fk 0 x‖ ^ 2 * (om x * Real.exp (-p 0 x))`. Use `hc.le.trans (hombd x).1` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul (by positivity)]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Use `set s := ‖F0 x - G x‖`. Use `set t := ‖F0 x - Fk 0 x‖`. Use `set e := Real.exp (-p 0 x)`. Establish `he : 0 < e` using `Real.exp_pos _`.

Establish `hu : ‖G x - Fk 0 x‖ ≤ s + t`. Combine the equalities or inequalities in the displayed calculation. Establish `hu2 : ‖G x - Fk 0 x‖ ^ 2 ≤ 2 * (s ^ 2 + t ^ 2)`. Establish `h0` using `norm_nonneg (G x - Fk 0 x)`. Use polynomial arithmetic with `[sq_nonneg (s - t), norm_nonneg (F0 x - G x), norm_nonneg (F0 x - Fk 0 x)]`.

Establish `hoc : 1 ≤ om x / c` using `(one_le_div hc).mpr (hombd x).1`. Establish `hst : 0 ≤ s ^ 2 + t ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hIfin : ∀ k, Iw 0 (Fk k) ≤ B` using `fun k => (hmono (Fk k) 0 k (Nat.zero_le k)).trans (hB k)`. Establish `hfin : ENNReal.ofReal (2 / c) * (B + B) < ⊤` using `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hBtop, hBtop⟩)`.

Establish `hbdB : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B → wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤ ENNReal.ofReal (2 / c) * (B + B)` using `fun G hG h => (hbd G hG).trans (by gcongr; exact hIfin 0)`. Establish `hEv : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ (G₁ G₂ : M → ℂ), Holo n X.z G₁ → Holo n X.z G₂ → ∀ w : Lp ℂ 2 μ, (w : M → ℂ) =ᵐ[μ] (fun x => G₁ x - G₂ x) → ‖G₁ x - G₂ x‖ ≤ C * ‖w‖`. Introduce `x`. Take `⟨C, hC⟩` from `hE X (p 0) x (hp 0)`. Use `⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun G₁ G₂ h₁ h₂ w hw => ?_⟩` and prove the remaining obligations.

Establish `h` using `hC _ (Holo.sub n X.z _ _ h₁ h₂)`. Rewrite `h` using `[hN w _ hw]`. Establish `h' : ENNReal.ofReal (‖G₁ x - G₂ x‖ ^ 2) ≤ ENNReal.ofReal (max C 0 * ‖w‖ ^ 2)`. Rewrite using `[ENNReal.ofReal_mul (le_max_right _ _)]`. Conclude with `h.trans (by gcongr; exact le_max_left _ _)`.

Rewrite `h'` using `[ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Rewrite using `[← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, Real.sq_sqrt (le_max_right _ _)]`. Conclude with `h'`. Use `choose Cev hCev0 hCev using hEv`. Establish `hmem : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B → MemLp (fun x => G x - Fk 0 x) 2 μ` using `fun G hG h => by`.

Use `⟨(hG.sub (hcont _ (hF 0))).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `h1` using `((hkey _).symm.trans_le (hbdB G hG h)).trans_lt hfin`. Conclude with `(ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h1`. Set `K : ℕ → Set (Lp ℂ 2 μ)` to `fun k => {v | ∃ G : M → ℂ, Holo n X.z G ∧ (v : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B}`. Establish `hanti : Antitone K`.

Introduce `k k' h v hv`. Take `⟨G, hG, hvG, hI⟩` from `hv`. Conclude with `⟨G, hG, hvG, (hmono G k k' h).trans hI⟩`. Establish `hne : ∀ k, (K k).Nonempty` using `fun k => ⟨(hmem (Fk k) (hcont _ (hF k)) (hIfin k)).toLp _, Fk k, hF k, MemLp.coeFn_toLp _, hB k⟩`. Establish `hclosed : ∀ k, IsClosed (K k)`.

Introduce `k`. Use `IsSeqClosed.isClosed fun vs v hvs hlimv => ?_` and prove the remaining obligations. Establish `hvs' : ∀ i, ∃ G : M → ℂ, Holo n X.z G ∧ (vs i : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B` using `hvs`. Use `choose G hG hvG hIG using hvs'`. Establish `hvm : Measurable (v : M → ℂ)` using `(Lp.stronglyMeasurable v).measurable`.

Establish `hF0m : Measurable (Fk 0)` using `(hcont _ (hF 0)).measurable`. Establish `hd : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - ((v : M → ℂ) x + Fk 0 x)` using `fun i => by filter_upwards [Lp.coeFn_sub (vs i) v, hvG i] with x h1 h2`. Rewrite using `[h1, Pi.sub_apply, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim0 : Tendsto (fun i => ‖vs i - v‖) atTop (𝓝 0)` using `tendsto_iff_norm_sub_tendsto_zero.mp hlimv`.

Establish `hw : Tendsto (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0)) atTop (𝓝 0)`. Establish `he : (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0)) = fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)` using `funext fun i => hN _ _ (hd i)`. Rewrite using `[he]`. Establish `: Tendsto (fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)) atTop (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2)))` using `(ENNReal.continuous_ofReal.tendsto _).comp (hlim0.pow 2)`. Simplify using `using this`.

Take `⟨Gl, hGl, hfG⟩` from `hC X (p 0) G (fun x => (v : M → ℂ) x + Fk 0 x) (hp 0) hG (hvm.add hF0m) hw`. Establish `hfGμ : (fun x => (v : M → ℂ) x + Fk 0 x) =ᵐ[μ] Gl` using `(withDensity_absolutelyContinuous _ _).ae_le hfG`. Establish `hvGl : (v : M → ℂ) =ᵐ[μ] fun x => Gl x - Fk 0 x` using `by filter_upwards [hfGμ] with x hx`. Rewrite using `[← hx]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hd2 : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - Gl x` using `fun i => by filter_upwards [hd i, hfGμ] with x h1 h2`. Rewrite using `[h1, h2]`. Establish `hpt : ∀ x, Tendsto (fun i => G i x) atTop (𝓝 (Gl x))`. Introduce `x`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`.

Use `squeeze_zero (fun i => norm_nonneg _) (fun i => hCev x (G i) Gl (hG i) hGl _ (hd2 i)) ?_` and prove the remaining obligations. Simplify using `using hlim0.const_mul (Cev x)`. Use `⟨Gl, hGl, hvGl, ?_⟩` and prove the remaining obligations. Establish `hf : ∀ x, Tendsto (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 * (om x * Real.exp (-p k x)))) atTop (𝓝 (ENNReal.ofReal (‖F0 x - Gl x‖ ^ 2 * (om x * Real.exp (-p k x)))))` using `fun x => (ENNReal.continuous_ofReal.tendsto _).comp (((tendsto_const_nhds.sub (hpt x)).norm.pow 2).mul_const _)`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Conclude with `((hf x).liminf_eq).symm`. Use `_ ≤ liminf (fun i => Iw k (G i)) atTop := lintegral_liminf_le fun i => hmeas _ (hcont _ (hG i)) _ (hpc k)`. Use `_ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hIG)`. Establish `hmid : ∀ k, ∀ v ∈ K k, ∀ w ∈ K k, (2 : ℂ)⁻¹ • (v + w) ∈ K k`.

Introduce and unpack `k v ⟨G, hG, hvG, hIv⟩ w ⟨G', hG', hwG, hIw'⟩`. Use `⟨fun x => (2 : ℂ)⁻¹ * (G x + G' x), Holo.mul n X.z _ _ (Holo.const n X.z _) (Holo.add n X.z _ _ hG hG'), ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (v + w), Lp.coeFn_add v w, hvG, hwG] with x h1 h2 h3 h4`. Rewrite using `[h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hhalf : ENNReal.ofReal (1 / 2) * (B + B) = B`. Rewrite using `[← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hIw, ← lintegral_add_left (hmeas G (hcont _ hG) _ (hpc k)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ om x * Real.exp (-p k x)`. Use `hc.le.trans (hombd x).1` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by norm_num)]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `hs : F0 x - (2 : ℂ)⁻¹ * (G x + G' x) = (2 : ℂ)⁻¹ * ((F0 x - G x) + (F0 x - G' x))` using `by ring`. Establish `hn : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ≤ (‖F0 x - G x‖ + ‖F0 x - G' x‖) / 2`. Rewrite using `[hs, norm_mul, norm_inv, Complex.norm_two]`. Use `norm_add_le (F0 x - G x) (F0 x - G' x)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn2 : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ^ 2 ≤ (‖F0 x - G x‖ ^ 2 + ‖F0 x - G' x‖ ^ 2) / 2`. Establish `h0'` using `norm_nonneg (F0 x - (2 : ℂ)⁻¹ * (G x + G' x))`. Use polynomial arithmetic with `[sq_nonneg (‖F0 x - G x‖ - ‖F0 x - G' x‖), mul_le_mul hn hn h0' (by positivity)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hn2 h0]`.

Use `_ ≤ ENNReal.ofReal (1 / 2) * (B + B) := by gcongr`. Use `_ = B := hhalf`. Establish `hbdd : Bornology.IsBounded (K 0)` using `by set R := (ENNReal.ofReal (2 / c) * (B + B)).toReal with hRdef`. Use `(Metric.isBounded_closedBall (x := (0 : Lp ℂ 2 μ)) (r := R + 1)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨G, hG, hvG, hI⟩`.

Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Establish `h1` using `(hN v _ hvG).symm.trans_le (hbdB G (hcont _ hG) hI)`. Rewrite `h1` using `[ENNReal.ofReal_le_iff_le_toReal hfin.ne]`. Establish `hR : 0 ≤ R` using `ENNReal.toReal_nonneg`. Use polynomial arithmetic with `[norm_nonneg v, sq_nonneg (‖v‖ - 1)]`.

Take `⟨v, hv⟩` from `cvx (Lp ℂ 2 μ) K hanti hne hclosed hmid hbdd`. Take `⟨G, hG, hvG, -⟩` from `hv 0`. Establish `hIk : ∀ k, Iw k G ≤ B` using `fun k => by`. Take `⟨G', hG', hvG', hI'⟩` from `hv k`. Establish `heq : G = G'` using `funext fun x => by`.

Establish `h0 : (⇑(0 : Lp ℂ 2 μ) : M → ℂ) =ᵐ[μ] fun x => G x - G' x` using `by filter_upwards [Lp.coeFn_zero ℂ 2 μ, hvG, hvG'] with x h1 h2 h3`. Rewrite using `[h1, Pi.zero_apply]`. Take the linear combination `h2 - h3`. Establish `h1` using `hCev x G G' hG hG' 0 h0`. Rewrite `h1` using `[norm_zero, mul_zero]`.

Conclude with `sub_eq_zero.mp (norm_le_zero_iff.mp h1)`. Rewrite using `[heq]`. Conclude with `hI'`. Use `⟨G, hG, ?_⟩` and prove the remaining obligations. Establish `hmon : ∀ x, Monotone fun k => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x)))` using `fun x k k' h => by`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h1` using `Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))`. Establish `h0` using `hc.le.trans (hombd x).1`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)`. Establish `hlimx : ∀ x, Tendsto (fun k => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x)))) atTop (𝓝 (ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x)))))` using `fun x => (ENNReal.continuous_ofReal.tendsto _).comp ((((Real.continuous_exp.tendsto _).comp (hpq x).neg).const_mul _).const_mul _)`.

Establish `hT` using `lintegral_tendsto_of_tendsto_of_monotone (μ := vol n X.z) (fun k => (hmeas G (hcont _ hG) _ (hpc k)).aemeasurable) (ae_of_all _ hmon) (ae_of_all _ hlimx)`. Conclude with `le_of_tendsto' hT hIk`.
-/
theorem holo_limit_increasing_weights : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (F0 : M → ℂ) (om : M → ℝ) (c : ℝ) (p : ℕ → M → ℝ) (q : M → ℝ) (F : ℕ → M → ℂ) (B : ℝ≥0∞), Continuous F0 → Continuous om → 0 < c → (∀ x, c ≤ om x ∧ om x ≤ 1) → (∀ k, SmoothR n X.z (p k)) → (∀ x, Antitone (fun k => p k x)) → (∀ x, Tendsto (fun k => p k x) atTop (𝓝 (q x))) → (∀ k, Holo n X.z (F k)) → B < ⊤ → (∀ k, ∫⁻ x, ENNReal.ofReal (‖F0 x - F k x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z ≤ B) → ∃ G : M → ℂ, Holo n X.z G ∧ ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))) ∂vol n X.z ≤ B := by
  intro n M _ _ _ _ _ X F0 om c p q Fk B hF0 hom hc hombd hp hpanti hpq hF hBtop hB
  have hz := X.isLocalHomeomorph
  have hpc : ∀ k, Continuous (p k) := fun k => by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ (hp k))
    exact this.congr fun x => by simp
  have hcont : ∀ G : M → ℂ, Holo n X.z G → Continuous G := fun G hG =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hG)
  have hC : ReciprocityTheory.L2DbarEstimates.I.HoloClosedNeed n M :=
    ReciprocityTheory.L2DbarEstimates.F.holoClosedNeed n M (regMAll n M)
  have hE : ReciprocityTheory.L2DbarEstimates.I.EvalNeed n M := ReciprocityTheory.L2DbarEstimates.F.evalNeed n M C.mv
  set Iw : ℕ → (M → ℂ) → ℝ≥0∞ := fun k G =>
    ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z with hIw
  set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-p 0 x)))
    with hμ
  have hkey : ∀ f : M → ℂ, wint n X.z f (p 0) = eLpNorm f 2 μ ^ (2 : ℝ) := fun f => by
    rw [ReciprocityTheory.L2DbarEstimates.I.fx_wint_eq_withDensity n X.z (p 0) (hpc 0).measurable f,
      ReciprocityTheory.L2DbarEstimates.I.fx_lintegral_enorm_sq_eq]
  have hN : ∀ (v : Lp ℂ 2 μ) (G : M → ℂ), (v : M → ℂ) =ᵐ[μ] G →
      wint n X.z G (p 0) = ENNReal.ofReal (‖v‖ ^ 2) := fun v G h => by
    rw [hkey, ReciprocityTheory.L2DbarEstimates.I.fx_lp_norm_sq_eq μ v G h]

  have hmono : ∀ G k k', k ≤ k' → Iw k G ≤ Iw k' G := fun G k k' h => by
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.exp (-p k x) ≤ Real.exp (-p k' x) :=
      Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))
    have h0 : 0 ≤ om x := hc.le.trans (hombd x).1
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)

  have hmeas : ∀ G : M → ℂ, Continuous G → ∀ (w : M → ℝ), Continuous w →
      Measurable fun x => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-w x))) :=
    fun G hG w hw => (ENNReal.continuous_ofReal.comp (((hF0.sub hG).norm.pow 2).mul
      (hom.mul (Real.continuous_exp.comp hw.neg)))).measurable

  have hbd : ∀ G : M → ℂ, Continuous G → wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤
      ENNReal.ofReal (2 / c) * (Iw 0 G + Iw 0 (Fk 0)) := fun G hG => by
    rw [hIw, ← lintegral_add_left (hmeas G hG _ (hpc 0)),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    have ha : 0 ≤ ‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p 0 x)) := by
      have := hc.le.trans (hombd x).1; positivity
    have hb : 0 ≤ ‖F0 x - Fk 0 x‖ ^ 2 * (om x * Real.exp (-p 0 x)) := by
      have := hc.le.trans (hombd x).1; positivity
    rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set s := ‖F0 x - G x‖
    set t := ‖F0 x - Fk 0 x‖
    set e := Real.exp (-p 0 x)
    have he : 0 < e := Real.exp_pos _
    have hu : ‖G x - Fk 0 x‖ ≤ s + t := by
      calc ‖G x - Fk 0 x‖ = ‖(F0 x - Fk 0 x) - (F0 x - G x)‖ := by congr 1; ring
        _ ≤ t + s := norm_sub_le _ _
        _ = s + t := add_comm _ _
    have hu2 : ‖G x - Fk 0 x‖ ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
      have h0 := norm_nonneg (G x - Fk 0 x)
      nlinarith [sq_nonneg (s - t), norm_nonneg (F0 x - G x), norm_nonneg (F0 x - Fk 0 x)]
    have hoc : 1 ≤ om x / c := (one_le_div hc).mpr (hombd x).1
    have hst : 0 ≤ s ^ 2 + t ^ 2 := by positivity
    calc ‖G x - Fk 0 x‖ ^ 2 * e ≤ 2 * (s ^ 2 + t ^ 2) * e := by gcongr
      _ ≤ 2 * (s ^ 2 + t ^ 2) * e * (om x / c) := le_mul_of_one_le_right (by positivity) hoc
      _ = 2 / c * (s ^ 2 * (om x * e) + t ^ 2 * (om x * e)) := by field_simp

  have hIfin : ∀ k, Iw 0 (Fk k) ≤ B := fun k => (hmono (Fk k) 0 k (Nat.zero_le k)).trans (hB k)
  have hfin : ENNReal.ofReal (2 / c) * (B + B) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hBtop, hBtop⟩)
  have hbdB : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B →
      wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤ ENNReal.ofReal (2 / c) * (B + B) :=
    fun G hG h => (hbd G hG).trans (by gcongr; exact hIfin 0)

  have hEv : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ (G₁ G₂ : M → ℂ), Holo n X.z G₁ → Holo n X.z G₂ →
      ∀ w : Lp ℂ 2 μ, (w : M → ℂ) =ᵐ[μ] (fun x => G₁ x - G₂ x) → ‖G₁ x - G₂ x‖ ≤ C * ‖w‖ := by
    intro x
    obtain ⟨C, hC⟩ := hE X (p 0) x (hp 0)
    refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun G₁ G₂ h₁ h₂ w hw => ?_⟩
    have h := hC _ (Holo.sub n X.z _ _ h₁ h₂)
    rw [hN w _ hw] at h
    have h' : ENNReal.ofReal (‖G₁ x - G₂ x‖ ^ 2) ≤ ENNReal.ofReal (max C 0 * ‖w‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      exact h.trans (by gcongr; exact le_max_left _ _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h'
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (le_max_right _ _)]
    exact h'
  choose Cev hCev0 hCev using hEv
  have hmem : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B → MemLp (fun x => G x - Fk 0 x) 2 μ :=
    fun G hG h => by
    refine ⟨(hG.sub (hcont _ (hF 0))).aestronglyMeasurable, ?_⟩
    have h1 := ((hkey _).symm.trans_le (hbdB G hG h)).trans_lt hfin
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h1
  let K : ℕ → Set (Lp ℂ 2 μ) := fun k => {v | ∃ G : M → ℂ, Holo n X.z G ∧
    (v : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B}
  have hanti : Antitone K := by
    intro k k' h v hv
    obtain ⟨G, hG, hvG, hI⟩ := hv
    exact ⟨G, hG, hvG, (hmono G k k' h).trans hI⟩
  have hne : ∀ k, (K k).Nonempty := fun k =>
    ⟨(hmem (Fk k) (hcont _ (hF k)) (hIfin k)).toLp _, Fk k, hF k, MemLp.coeFn_toLp _, hB k⟩

  have hclosed : ∀ k, IsClosed (K k) := by
    intro k
    refine IsSeqClosed.isClosed fun vs v hvs hlimv => ?_
    have hvs' : ∀ i, ∃ G : M → ℂ, Holo n X.z G ∧
        (vs i : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B := hvs
    choose G hG hvG hIG using hvs'
    have hvm : Measurable (v : M → ℂ) := (Lp.stronglyMeasurable v).measurable
    have hF0m : Measurable (Fk 0) := (hcont _ (hF 0)).measurable
    have hd : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ]
        fun x => G i x - ((v : M → ℂ) x + Fk 0 x) := fun i => by
      filter_upwards [Lp.coeFn_sub (vs i) v, hvG i] with x h1 h2
      rw [h1, Pi.sub_apply, h2]; ring
    have hlim0 : Tendsto (fun i => ‖vs i - v‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlimv
    have hw : Tendsto (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0))
        atTop (𝓝 0) := by
      have he : (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0)) =
          fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2) := funext fun i => hN _ _ (hd i)
      rw [he]
      have : Tendsto (fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hlim0.pow 2)
      simpa using this
    obtain ⟨Gl, hGl, hfG⟩ :=
      hC X (p 0) G (fun x => (v : M → ℂ) x + Fk 0 x) (hp 0) hG (hvm.add hF0m) hw
    have hfGμ : (fun x => (v : M → ℂ) x + Fk 0 x) =ᵐ[μ] Gl :=
      (withDensity_absolutelyContinuous _ _).ae_le hfG
    have hvGl : (v : M → ℂ) =ᵐ[μ] fun x => Gl x - Fk 0 x := by
      filter_upwards [hfGμ] with x hx
      rw [← hx]; ring
    have hd2 : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - Gl x := fun i => by
      filter_upwards [hd i, hfGμ] with x h1 h2
      rw [h1, h2]
    have hpt : ∀ x, Tendsto (fun i => G i x) atTop (𝓝 (Gl x)) := by
      intro x
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun i => norm_nonneg _)
        (fun i => hCev x (G i) Gl (hG i) hGl _ (hd2 i)) ?_
      simpa using hlim0.const_mul (Cev x)
    refine ⟨Gl, hGl, hvGl, ?_⟩
    have hf : ∀ x, Tendsto (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 *
        (om x * Real.exp (-p k x)))) atTop
        (𝓝 (ENNReal.ofReal (‖F0 x - Gl x‖ ^ 2 * (om x * Real.exp (-p k x))))) := fun x =>
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_const_nhds.sub (hpt x)).norm.pow 2).mul_const _)
    calc Iw k Gl = ∫⁻ x, liminf (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 *
          (om x * Real.exp (-p k x)))) atTop ∂vol n X.z := by
          refine lintegral_congr fun x => ?_
          exact ((hf x).liminf_eq).symm
      _ ≤ liminf (fun i => Iw k (G i)) atTop :=
          lintegral_liminf_le fun i => hmeas _ (hcont _ (hG i)) _ (hpc k)
      _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hIG)
  have hmid : ∀ k, ∀ v ∈ K k, ∀ w ∈ K k, (2 : ℂ)⁻¹ • (v + w) ∈ K k := by
    rintro k v ⟨G, hG, hvG, hIv⟩ w ⟨G', hG', hwG, hIw'⟩
    refine ⟨fun x => (2 : ℂ)⁻¹ * (G x + G' x),
      Holo.mul n X.z _ _ (Holo.const n X.z _) (Holo.add n X.z _ _ hG hG'), ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (v + w), Lp.coeFn_add v w, hvG, hwG]
        with x h1 h2 h3 h4
      rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, smul_eq_mul]; ring
    · have hhalf : ENNReal.ofReal (1 / 2) * (B + B) = B := by
        rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc Iw k (fun x => (2 : ℂ)⁻¹ * (G x + G' x))
          ≤ ENNReal.ofReal (1 / 2) * (Iw k G + Iw k G') := by
            rw [hIw, ← lintegral_add_left (hmeas G (hcont _ hG) _ (hpc k)),
              ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_mono fun x => ?_
            have h0 : 0 ≤ om x * Real.exp (-p k x) := by
              have := hc.le.trans (hombd x).1; positivity
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by norm_num)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hs : F0 x - (2 : ℂ)⁻¹ * (G x + G' x) =
                (2 : ℂ)⁻¹ * ((F0 x - G x) + (F0 x - G' x)) := by ring
            have hn : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ≤
                (‖F0 x - G x‖ + ‖F0 x - G' x‖) / 2 := by
              rw [hs, norm_mul, norm_inv, Complex.norm_two]
              have := norm_add_le (F0 x - G x) (F0 x - G' x)
              linarith
            have hn2 : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ^ 2 ≤
                (‖F0 x - G x‖ ^ 2 + ‖F0 x - G' x‖ ^ 2) / 2 := by
              have h0' := norm_nonneg (F0 x - (2 : ℂ)⁻¹ * (G x + G' x))
              nlinarith [sq_nonneg (‖F0 x - G x‖ - ‖F0 x - G' x‖),
                mul_le_mul hn hn h0' (by positivity)]
            nlinarith [mul_le_mul_of_nonneg_right hn2 h0]
        _ ≤ ENNReal.ofReal (1 / 2) * (B + B) := by gcongr
        _ = B := hhalf
  have hbdd : Bornology.IsBounded (K 0) := by
    set R := (ENNReal.ofReal (2 / c) * (B + B)).toReal with hRdef
    refine (Metric.isBounded_closedBall (x := (0 : Lp ℂ 2 μ)) (r := R + 1)).subset ?_
    rintro v ⟨G, hG, hvG, hI⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (hN v _ hvG).symm.trans_le (hbdB G (hcont _ hG) hI)
    rw [ENNReal.ofReal_le_iff_le_toReal hfin.ne] at h1
    have hR : 0 ≤ R := ENNReal.toReal_nonneg
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  obtain ⟨v, hv⟩ := cvx (Lp ℂ 2 μ) K hanti hne hclosed hmid hbdd
  obtain ⟨G, hG, hvG, -⟩ := hv 0
  have hIk : ∀ k, Iw k G ≤ B := fun k => by
    obtain ⟨G', hG', hvG', hI'⟩ := hv k
    have heq : G = G' := funext fun x => by
      have h0 : (⇑(0 : Lp ℂ 2 μ) : M → ℂ) =ᵐ[μ] fun x => G x - G' x := by
        filter_upwards [Lp.coeFn_zero ℂ 2 μ, hvG, hvG'] with x h1 h2 h3
        rw [h1, Pi.zero_apply]
        linear_combination h2 - h3
      have h1 := hCev x G G' hG hG' 0 h0
      rw [norm_zero, mul_zero] at h1
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
    rw [heq]; exact hI'
  refine ⟨G, hG, ?_⟩
  have hmon : ∀ x, Monotone fun k =>
      ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) := fun x k k' h => by
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))
    have h0 := hc.le.trans (hombd x).1
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)
  have hlimx : ∀ x, Tendsto (fun k =>
      ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x)))) atTop
      (𝓝 (ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))))) := fun x =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((((Real.continuous_exp.tendsto _).comp (hpq x).neg).const_mul _).const_mul _)
  have hT := lintegral_tendsto_of_tendsto_of_monotone
    (μ := vol n X.z) (fun k => (hmeas G (hcont _ hG) _ (hpc k)).aemeasurable)
    (ae_of_all _ hmon) (ae_of_all _ hlimx)
  exact le_of_tendsto' hT hIk

end

end GlobalTheory
