import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.DetMEq

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def thF (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) : ℂ :=
  paTh Y q F v * (starRingEnd ℂ) (F v) * (paW q v : ℂ)

/- English proof (translation)
Take `⟨C, hC0, hb⟩` from `paU_pt (q := q) hF`. Establish `hL` using `lat_summable (c := c) hP hA Y hq hR0 hlat hR`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `v0`. Use `set R := ‖v0‖ + 1 with hRdef`.

Establish `hon : ContinuousOn (fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v) (Metric.ball v0 1)`. Use `continuousOn_tsum (u := fun γ : lat Y.b => C * (1 + R) ^ c * Real.exp ((q * Real.pi) * R ^ 2) * ((1 + ‖(γ : EuclideanSpace ℂ ι)‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 4))) (fun γ => (continuous_const.mul (paU_continuous (q := q) _ hF)).continuou …` and prove the remaining obligations. Rewrite using `[norm_mul, Y.ka_abs γ γ.2, one_mul]`. Use `(hb γ v).trans ?_` and prove the remaining obligations. Establish `hvR : ‖v‖ ≤ R`.

Establish `h1` using `Metric.mem_ball.1 hv`. Rewrite `h1` using `[dist_eq_norm]`. Establish `h2` using `norm_sub_norm_le v v0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv0` using `norm_nonneg v`.

Establish `hq0 : 0 ≤ (q : ℝ) * Real.pi` using `by positivity`. Establish `hsq : (q * Real.pi) * ‖v‖ ^ 2 ≤ (q * Real.pi) * R ^ 2` using `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hvR 2) hq0`. Use `gcongr`. Conclude with `hon.continuousAt (Metric.ball_mem_nhds v0 one_pos)`.
-/
theorem paTh_continuous (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) : Continuous (paTh Y q F) := by
  obtain ⟨C, hC0, hb⟩ := paU_pt (q := q) hF
  have hL := lat_summable (c := c) hP hA Y hq hR0 hlat hR
  rw [continuous_iff_continuousAt]
  intro v0
  set R := ‖v0‖ + 1 with hRdef
  have hon : ContinuousOn (fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v) (Metric.ball v0 1) := by
    refine continuousOn_tsum (u := fun γ : lat Y.b => C * (1 + R) ^ c * Real.exp ((q * Real.pi) * R ^ 2) *
      ((1 + ‖(γ : EuclideanSpace ℂ ι)‖) ^ (2 * c) *
        Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 4)))
      (fun γ => (continuous_const.mul (paU_continuous (q := q) _ hF)).continuousOn)
      (hL.mul_left _) (fun γ v hv => ?_)
    rw [norm_mul, Y.ka_abs γ γ.2, one_mul]
    refine (hb γ v).trans ?_
    have hvR : ‖v‖ ≤ R := by
      have h1 := Metric.mem_ball.1 hv
      rw [dist_eq_norm] at h1
      have h2 := norm_sub_norm_le v v0
      linarith
    have hv0 := norm_nonneg v
    have hq0 : 0 ≤ (q : ℝ) * Real.pi := by positivity
    have hsq : (q * Real.pi) * ‖v‖ ^ 2 ≤ (q * Real.pi) * R ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hvR 2) hq0
    gcongr
  exact hon.continuousAt (Metric.ball_mem_nhds v0 one_pos)

/- English proof (translation)
Use `lat_countable (ι := ι) Y.b` as an intermediate fact. Take `⟨C, hC0, hU⟩` from `paU_int hq hF hF`. Take `⟨C', hC'0, hb⟩` from `paU_pt (q := q) hF`. Establish `hL` using `lat_summable (c := c) hP hA Y hq hR0 hlat hR`. Establish `hcont : Continuous (thF Y q F)`.

Use `paTh_continuous hP hA Y hq hR0 hlat hR hF` as an intermediate fact. Use `paPoly_continuous hF` as an intermediate fact. Use `paW_continuous (ι := ι) q` as an intermediate fact. Unfold `thF`. Use `fun_prop`.

Use `⟨⟨hcont.aestronglyMeasurable, ?_⟩, hcont⟩` and prove the remaining obligations. Use `set g : lat Y.b → EuclideanSpace ℂ ι → ℝ := fun γ v => ‖paU q γ F v‖ * ‖F v‖ * paW q v with hg`. Establish `hg0 : ∀ γ v, 0 ≤ g γ v` using `fun γ v => by have := (paW_pos q v).le; simp only [hg]; positivity`. Establish `hpt : ∀ v, Summable (fun γ : lat Y.b => ‖paU q γ F v‖)` using `fun v => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => hb γ v) (hL.mul_left (C' * (1 + ‖v‖) ^ c * Real.exp ((q * Real.pi) * ‖v‖ ^ 2)))`. Establish `hgs : ∀ v, Summable (fun γ => g γ v)` using `fun v => by`.

Simplify `(hpt v).mul_right (‖F v‖ * paW q v)` using `only [hg, mul_assoc]`. Establish `hfle : ∀ v, ‖thF Y q F v‖ ≤ ∑' γ, g γ v`. Introduce `v`. Establish `hth : ‖paTh Y q F v‖ ≤ ∑' γ : lat Y.b, ‖paU q γ F v‖`. Unfold `paTh`.

Use `(norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)` and prove the remaining obligations. Use `(hpt v).congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Y.ka_abs γ γ.2, one_mul]`. Conclude with `tsum_congr fun γ => by rw [norm_mul, Y.ka_abs γ γ.2, one_mul]`. Simplify using `only [hg]`.

Rewrite using `[tsum_mul_right, tsum_mul_right, thF, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (paW_pos q v).le]`. Use `(paW_pos q v).le` as an intermediate fact. Use `gcongr`. Establish `hsI : Summable (fun γ : lat Y.b => ∫ v, g γ v)` using `Summable.of_nonneg_of_le (fun γ => integral_nonneg (hg0 γ)) (fun γ => (hU γ).2) (hL.mul_left C)`. Use `show ∫⁻ v, ‖thF Y q F v‖ₑ < ⊤`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun v => ?_` and prove the remaining obligations. Rewrite using `[← ofReal_norm, ← ENNReal.ofReal_tsum_of_nonneg (fun γ => hg0 γ v) (hgs v)]`. Conclude with `ENNReal.ofReal_le_ofReal (hfle v)`. Use `_ = ∑' γ, ∫⁻ v, ENNReal.ofReal (g γ v) := lintegral_tsum (fun γ => (hU γ).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)`.

Use `_ = ∑' γ, ENNReal.ofReal (∫ v, g γ v) := by`. Use `congr 1`. Use function extensionality and compare the values at `γ`. Rewrite using `[ofReal_integral_eq_lintegral_ofReal (hU γ).1 (Filter.Eventually.of_forall (hg0 γ))]`. Use `_ = ENNReal.ofReal (∑' γ, ∫ v, g γ v) := (ENNReal.ofReal_tsum_of_nonneg (fun γ => integral_nonneg (hg0 γ)) hsI).symm`.

Use `_ < ⊤ := ENNReal.ofReal_lt_top`.
-/
theorem thF_integrable (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) : Integrable (thF Y q F) ∧ Continuous (thF Y q F) := by
  have := lat_countable (ι := ι) Y.b
  obtain ⟨C, hC0, hU⟩ := paU_int hq hF hF
  obtain ⟨C', hC'0, hb⟩ := paU_pt (q := q) hF
  have hL := lat_summable (c := c) hP hA Y hq hR0 hlat hR
  have hcont : Continuous (thF Y q F) := by
    have := paTh_continuous hP hA Y hq hR0 hlat hR hF
    have := paPoly_continuous hF
    have := paW_continuous (ι := ι) q
    unfold thF; fun_prop
  refine ⟨⟨hcont.aestronglyMeasurable, ?_⟩, hcont⟩
  set g : lat Y.b → EuclideanSpace ℂ ι → ℝ := fun γ v => ‖paU q γ F v‖ * ‖F v‖ * paW q v with hg
  have hg0 : ∀ γ v, 0 ≤ g γ v := fun γ v => by have := (paW_pos q v).le; simp only [hg]; positivity
  have hpt : ∀ v, Summable (fun γ : lat Y.b => ‖paU q γ F v‖) := fun v =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => hb γ v)
      (hL.mul_left (C' * (1 + ‖v‖) ^ c * Real.exp ((q * Real.pi) * ‖v‖ ^ 2)))
  have hgs : ∀ v, Summable (fun γ => g γ v) := fun v => by
    simpa only [hg, mul_assoc] using (hpt v).mul_right (‖F v‖ * paW q v)
  have hfle : ∀ v, ‖thF Y q F v‖ ≤ ∑' γ, g γ v := by
    intro v
    have hth : ‖paTh Y q F v‖ ≤ ∑' γ : lat Y.b, ‖paU q γ F v‖ := by
      unfold paTh
      refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
      · refine (hpt v).congr fun γ => ?_
        rw [norm_mul, Y.ka_abs γ γ.2, one_mul]
      · exact tsum_congr fun γ => by rw [norm_mul, Y.ka_abs γ γ.2, one_mul]
    simp only [hg]
    rw [tsum_mul_right, tsum_mul_right, thF, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (paW_pos q v).le]
    have := (paW_pos q v).le
    gcongr
  have hsI : Summable (fun γ : lat Y.b => ∫ v, g γ v) :=
    Summable.of_nonneg_of_le (fun γ => integral_nonneg (hg0 γ)) (fun γ => (hU γ).2) (hL.mul_left C)
  show ∫⁻ v, ‖thF Y q F v‖ₑ < ⊤
  calc ∫⁻ v, ‖thF Y q F v‖ₑ ≤ ∫⁻ v, ∑' γ, ENNReal.ofReal (g γ v) := by
        refine lintegral_mono fun v => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_tsum_of_nonneg (fun γ => hg0 γ v) (hgs v)]
        exact ENNReal.ofReal_le_ofReal (hfle v)
    _ = ∑' γ, ∫⁻ v, ENNReal.ofReal (g γ v) :=
        lintegral_tsum (fun γ => (hU γ).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ = ∑' γ, ENNReal.ofReal (∫ v, g γ v) := by
        congr 1; funext γ
        rw [ofReal_integral_eq_lintegral_ofReal (hU γ).1 (Filter.Eventually.of_forall (hg0 γ))]
    _ = ENNReal.ofReal (∑' γ, ∫ v, g γ v) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun γ => integral_nonneg (hg0 γ)) hsI).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/- English proof (translation)
Establish `hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v` using `fun v w => by`. Rewrite using `[Hf, PiLp.inner_apply]`. Apply the tactic sequence `try rfl`. Establish `hn : ∀ v : EuclideanSpace ℂ ι, ((‖v‖ ^ 2 : ℝ) : ℂ) = inner ℂ v v` using `fun v => by`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Use `first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `norm_cast`.

Establish `hexp : ∀ r : ℝ, ((Real.exp r : ℝ) : ℂ) = cexp (r : ℂ)` using `fun r => Complex.ofReal_exp r`. Simplify using `only [paW, hH, hexp]`. Rewrite using `[← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Establish `h1 : ((-(↑q * Real.pi) * ‖x + γ‖ ^ 2 : ℝ) : ℂ) = -((q : ℂ) * Real.pi) * inner ℂ (x + γ) (x + γ)`.

Rewrite using `[← hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((-(↑q * Real.pi) * ‖x‖ ^ 2 : ℝ) : ℂ) = -((q : ℂ) * Real.pi) * inner ℂ x x`. Rewrite using `[← hn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Simplify using `only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, map_sub, map_mul, map_div₀, map_neg, Complex.conj_ofReal, map_natCast, map_ofNat, inner_conj_symm, neg_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key2 (q : ℕ) (γ x : EuclideanSpace ℂ ι) :
    cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * ((paW q (x + γ) : ℝ) : ℂ) =
      ((paW q x : ℝ) : ℂ) * (starRingEnd ℂ) (cexp (q * Real.pi * Hf x (-γ) - q * Real.pi * Hf (-γ) (-γ) / 2)) := by
  have hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v := fun v w => by
    rw [Hf, PiLp.inner_apply]
    try rfl
  have hn : ∀ v : EuclideanSpace ℂ ι, ((‖v‖ ^ 2 : ℝ) : ℂ) = inner ℂ v v := fun v => by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    first
    | rfl
    | simp
    | norm_cast
  have hexp : ∀ r : ℝ, ((Real.exp r : ℝ) : ℂ) = cexp (r : ℂ) := fun r => Complex.ofReal_exp r
  simp only [paW, hH, hexp]
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h1 : ((-(↑q * Real.pi) * ‖x + γ‖ ^ 2 : ℝ) : ℂ) =
      -((q : ℂ) * Real.pi) * inner ℂ (x + γ) (x + γ) := by
    rw [← hn]
    push_cast
    ring
  have h2 : ((-(↑q * Real.pi) * ‖x‖ ^ 2 : ℝ) : ℂ) = -((q : ℂ) * Real.pi) * inner ℂ x x := by
    rw [← hn]
    push_cast
    ring
  rw [h1, h2]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, map_sub, map_mul,
    map_div₀, map_neg, Complex.conj_ofReal, map_natCast, map_ofNat, inner_conj_symm, neg_neg]
  ring

/- English proof (translation)
Establish `hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v` using `fun v w => by`. Rewrite using `[Hf, PiLp.inner_apply]`. Apply the tactic sequence `try rfl`. Simplify using `only [paTh]`. Rewrite using `[← tsum_mul_left, ← (Equiv.addLeft g).tsum_eq (fun γ : lat Y.b => Y.ka γ * paU q γ F ((g : EuclideanSpace ℂ ι) + x))]`.

Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_addLeft, Submodule.coe_add]`. Rewrite using `[hC g g.2 γ γ.2]`. Simplify using `only [paU]`. Establish `harg : (g : EuclideanSpace ℂ ι) + x - ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) = x - γ` using `by abel`.

Rewrite using `[harg]`. Establish `hAB : -((Real.pi : ℂ) * (q : ℂ) * ((Hf (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι)).im : ℂ)) * I + ((q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + x) ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) - (q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + ( …`. Simplify using `only [hH, inner_add_left, inner_add_right]`. Establish `hc : inner ℂ (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι) = (starRingEnd ℂ) (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι))` using `(inner_conj_symm _ _).symm`. Establish `hre : (starRingEnd ℂ) (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)) = inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι) - 2 * ((inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)).im : ℂ) * I`.

Establish `hs` using `Complex.sub_conj (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι))`. Move the coercions through the operations in `at hs`. Take the linear combination `-hs`. Rewrite using `[hc, hre]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : cexp (-((Real.pi : ℂ) * (q : ℂ) * ((Hf (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι)).im : ℂ)) * I) * cexp ((q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + x) ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) - (q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSp …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, hAB]`. Take the linear combination `(Y.ka g * Y.ka γ * F (x - γ)) * key`.
-/
private theorem paTh_add_lattice {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ)
    (x : EuclideanSpace ℂ ι) (g : lat Y.b) :
    paTh Y q F ((g : EuclideanSpace ℂ ι) + x) =
      Y.ka g * cexp (q * Real.pi * Hf x g + q * Real.pi * Hf (g : EuclideanSpace ℂ ι) g / 2) *
        paTh Y q F x := by
  have hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v := fun v w => by
    rw [Hf, PiLp.inner_apply]
    try rfl
  simp only [paTh]
  rw [← tsum_mul_left, ← (Equiv.addLeft g).tsum_eq
    (fun γ : lat Y.b => Y.ka γ * paU q γ F ((g : EuclideanSpace ℂ ι) + x))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addLeft, Submodule.coe_add]
  rw [hC g g.2 γ γ.2]
  simp only [paU]
  have harg : (g : EuclideanSpace ℂ ι) + x - ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) =
      x - γ := by abel
  rw [harg]
  have hAB : -((Real.pi : ℂ) * (q : ℂ) * ((Hf (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι)).im : ℂ)) * I +
      ((q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + x) ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) -
        (q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι))
          ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) / 2) =
      ((q : ℂ) * (Real.pi : ℂ) * Hf x g + (q : ℂ) * (Real.pi : ℂ) * Hf (g : EuclideanSpace ℂ ι) g / 2) +
      ((q : ℂ) * (Real.pi : ℂ) * Hf x γ - (q : ℂ) * (Real.pi : ℂ) * Hf (γ : EuclideanSpace ℂ ι) γ / 2) := by
    simp only [hH, inner_add_left, inner_add_right]
    have hc : inner ℂ (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι) =
        (starRingEnd ℂ) (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)) :=
      (inner_conj_symm _ _).symm
    have hre : (starRingEnd ℂ) (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)) =
        inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι) -
          2 * ((inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)).im : ℂ) * I := by
      have hs := Complex.sub_conj (inner ℂ (γ : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι))
      push_cast at hs
      linear_combination -hs
    rw [hc, hre]
    ring
  have key : cexp (-((Real.pi : ℂ) * (q : ℂ) * ((Hf (g : EuclideanSpace ℂ ι) (γ : EuclideanSpace ℂ ι)).im : ℂ)) * I) *
      cexp ((q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + x) ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) -
        (q : ℂ) * (Real.pi : ℂ) * Hf ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι))
          ((g : EuclideanSpace ℂ ι) + (γ : EuclideanSpace ℂ ι)) / 2) =
      cexp ((q : ℂ) * (Real.pi : ℂ) * Hf x g + (q : ℂ) * (Real.pi : ℂ) * Hf (g : EuclideanSpace ℂ ι) g / 2) *
      cexp ((q : ℂ) * (Real.pi : ℂ) * Hf x γ - (q : ℂ) * (Real.pi : ℂ) * Hf (γ : EuclideanSpace ℂ ι) γ / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hAB]
  linear_combination (Y.ka g * Y.ka γ * F (x - γ)) * key

/- English proof (translation)
Establish `h0 : Y.ka 0 = 1`. Establish `h00` using `hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)`. Establish `hz : Hf (0 : EuclideanSpace ℂ ι) (0 : EuclideanSpace ℂ ι) = 0` using `by simp [Hf]`. Rewrite `h00` using `[add_zero, hz, Complex.zero_im]`. Simplify using `only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at h00`.

Establish `hn : Y.ka 0 ≠ 0`. Introduce `h`. Establish `h1` using `Y.ka_abs 0 (Submodule.zero_mem _)`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.

Conclude with `mul_left_cancel₀ hn (h00.symm.trans (mul_one _).symm)`. Establish `hneg : (Hf (g : EuclideanSpace ℂ ι) (-(g : EuclideanSpace ℂ ι))).im = 0`. Establish `e1 : Hf (g : EuclideanSpace ℂ ι) (-(g : EuclideanSpace ℂ ι)) = -Hf (g : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι)`. Simplify using `[Hf, Finset.sum_neg_distrib]`. Rewrite using `[e1, Complex.neg_im, neg_eq_zero]`.

Simplify using `[Hf, Complex.mul_conj, Complex.im_sum]`. Establish `hg` using `hC (g : EuclideanSpace ℂ ι) g.2 (-(g : EuclideanSpace ℂ ι)) (Submodule.neg_mem _ g.2)`. Rewrite `hg` using `[add_neg_cancel, h0, hneg]`. Simplify using `only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at hg`. Establish `hconj : (starRingEnd ℂ) (Y.ka g) * Y.ka g = 1`.

Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs g g.2]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hconj, one_mul]`. Use `_ = (starRingEnd ℂ) (Y.ka g) * (Y.ka g * Y.ka (-(g : EuclideanSpace ℂ ι))) := by ring`.

Use `_ = (starRingEnd ℂ) (Y.ka g) := by rw [← hg, mul_one]`.
-/
private theorem ka_neg_eq_conj {Y : GT ι} {q : ℕ} (hC : Coc Y q) (g : lat Y.b) :
    Y.ka (-(g : EuclideanSpace ℂ ι)) = (starRingEnd ℂ) (Y.ka g) := by
  have h0 : Y.ka 0 = 1 := by
    have h00 := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    have hz : Hf (0 : EuclideanSpace ℂ ι) (0 : EuclideanSpace ℂ ι) = 0 := by simp [Hf]
    rw [add_zero, hz, Complex.zero_im] at h00
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at h00
    have hn : Y.ka 0 ≠ 0 := by
      intro h
      have h1 := Y.ka_abs 0 (Submodule.zero_mem _)
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact mul_left_cancel₀ hn (h00.symm.trans (mul_one _).symm)
  have hneg : (Hf (g : EuclideanSpace ℂ ι) (-(g : EuclideanSpace ℂ ι))).im = 0 := by
    have e1 : Hf (g : EuclideanSpace ℂ ι) (-(g : EuclideanSpace ℂ ι)) =
        -Hf (g : EuclideanSpace ℂ ι) (g : EuclideanSpace ℂ ι) := by
      simp [Hf, Finset.sum_neg_distrib]
    rw [e1, Complex.neg_im, neg_eq_zero]
    simp [Hf, Complex.mul_conj, Complex.im_sum]
  have hg := hC (g : EuclideanSpace ℂ ι) g.2 (-(g : EuclideanSpace ℂ ι)) (Submodule.neg_mem _ g.2)
  rw [add_neg_cancel, h0, hneg] at hg
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one] at hg
  have hconj : (starRingEnd ℂ) (Y.ka g) * Y.ka g = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs g g.2]
    norm_num
  calc Y.ka (-(g : EuclideanSpace ℂ ι))
      = ((starRingEnd ℂ) (Y.ka g) * Y.ka g) * Y.ka (-(g : EuclideanSpace ℂ ι)) := by
        rw [hconj, one_mul]
    _ = (starRingEnd ℂ) (Y.ka g) * (Y.ka g * Y.ka (-(g : EuclideanSpace ℂ ι))) := by ring
    _ = (starRingEnd ℂ) (Y.ka g) := by rw [← hg, mul_one]

/- English proof (translation)
Establish `hpt : ∀ g : lat Y.b, thF Y q F (g +ᵥ x) = paTh Y q F x * (paW q x : ℂ) * (starRingEnd ℂ) (Y.ka (-(g : EuclideanSpace ℂ ι)) * paU q (-(g : EuclideanSpace ℂ ι)) F x)`. Introduce `g`. Establish `hv : (g +ᵥ x : EuclideanSpace ℂ ι) = (g : EuclideanSpace ℂ ι) + x` using `rfl`. Rewrite using `[hv]`. Unfold `thF`.

Rewrite using `[paTh_add_lattice hC F x g, ka_neg_eq_conj hC g]`. Establish `hk` using `key2 q (g : EuclideanSpace ℂ ι) x`. Rewrite `hk` using `[add_comm x (g : EuclideanSpace ℂ ι)]`. Simplify using `only [paU, map_mul, Complex.conj_conj, sub_neg_eq_add]`. Rewrite using `[add_comm x (g : EuclideanSpace ℂ ι)]`.

Take the linear combination `(Y.ka g * paTh Y q F x * (starRingEnd ℂ) (F ((g : EuclideanSpace ℂ ι) + x))) * hk`. Rewrite using `[tsum_congr hpt, tsum_mul_left]`. Establish `hsum : ∑' g : lat Y.b, (starRingEnd ℂ) (Y.ka (-(g : EuclideanSpace ℂ ι)) * paU q (-(g : EuclideanSpace ℂ ι)) F x) = (starRingEnd ℂ) (paTh Y q F x)`. Simplify using `only [paTh]`. Rewrite using `[starRingEnd_apply, tsum_star]`.

Rewrite using `[← (Equiv.neg (lat Y.b)).tsum_eq (fun g : lat Y.b => star (Y.ka g * paU q g F x))]`. Use `tsum_congr fun g => ?_` and prove the remaining obligations. Simplify using `only [Equiv.neg_apply, Submodule.coe_neg, starRingEnd_apply]`. Rewrite using `[hsum]`. Establish `hmc : paTh Y q F x * (starRingEnd ℂ) (paTh Y q F x) = ((‖paTh Y q F x‖ ^ 2 : ℝ) : ℂ)` using `by first`.

Consider the case `rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Consider the case `(rw [Complex.mul_conj']; push_cast; ring)`. Move the coercions through the operations in `at hmc ⊢`. Take the linear combination `(paW q x : ℂ) * hmc`.
-/
theorem unfold_pt {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ) (x : EuclideanSpace ℂ ι) :
    ∑' g : lat Y.b, thF Y q F (g +ᵥ x) = ((‖paTh Y q F x‖ ^ 2 * paW q x : ℝ) : ℂ) := by
  have hpt : ∀ g : lat Y.b, thF Y q F (g +ᵥ x) =
      paTh Y q F x * (paW q x : ℂ) *
        (starRingEnd ℂ) (Y.ka (-(g : EuclideanSpace ℂ ι)) * paU q (-(g : EuclideanSpace ℂ ι)) F x) := by
    intro g
    have hv : (g +ᵥ x : EuclideanSpace ℂ ι) = (g : EuclideanSpace ℂ ι) + x := rfl
    rw [hv]
    unfold thF
    rw [paTh_add_lattice hC F x g, ka_neg_eq_conj hC g]
    have hk := key2 q (g : EuclideanSpace ℂ ι) x
    rw [add_comm x (g : EuclideanSpace ℂ ι)] at hk
    simp only [paU, map_mul, Complex.conj_conj, sub_neg_eq_add]
    rw [add_comm x (g : EuclideanSpace ℂ ι)]
    linear_combination (Y.ka g * paTh Y q F x * (starRingEnd ℂ) (F ((g : EuclideanSpace ℂ ι) + x))) * hk
  rw [tsum_congr hpt, tsum_mul_left]
  have hsum : ∑' g : lat Y.b,
      (starRingEnd ℂ) (Y.ka (-(g : EuclideanSpace ℂ ι)) * paU q (-(g : EuclideanSpace ℂ ι)) F x) =
      (starRingEnd ℂ) (paTh Y q F x) := by
    simp only [paTh]
    rw [starRingEnd_apply, tsum_star]
    rw [← (Equiv.neg (lat Y.b)).tsum_eq (fun g : lat Y.b => star (Y.ka g * paU q g F x))]
    refine tsum_congr fun g => ?_
    simp only [Equiv.neg_apply, Submodule.coe_neg, starRingEnd_apply]
  rw [hsum]
  have hmc : paTh Y q F x * (starRingEnd ℂ) (paTh Y q F x) = ((‖paTh Y q F x‖ ^ 2 : ℝ) : ℂ) := by
    first
    | rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    | (rw [Complex.mul_conj']; push_cast; ring)
  push_cast at hmc ⊢
  linear_combination (paW q x : ℂ) * hmc

instance lat_vaddInv (Y : GT ι) :
    VAddInvariantMeasure (lat Y.b) (EuclideanSpace ℂ ι) volume :=
  ⟨fun g s _ => by
    simp only [Submodule.vadd_def, vadd_eq_add]
    exact measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩

/- English proof (translation)
Use `lat_countable (ι := ι) Y.b` as an intermediate fact. Take `⟨hfi, hfc⟩` from `thF_integrable hP hA Y hq hR0 hlat hR hF`. Establish `hfd` using `ZSpan.isAddFundamentalDomain Y.b (volume : Measure (EuclideanSpace ℂ ι))`. Establish `e1 : paIP q (paTh Y q F) F = ∑' g : lat Y.b, ∫ x in ZSpan.fundamentalDomain Y.b, thF Y q F (g +ᵥ x)` using `hfd.integral_eq_tsum'' (thF Y q F) hfi`. Establish `hmeas : ∀ g : lat Y.b, AEStronglyMeasurable (fun x => thF Y q F (g +ᵥ x)) (volume.restrict (ZSpan.fundamentalDomain Y.b))` using `fun g => by`.

Simplify using `only [Submodule.vadd_def, vadd_eq_add]`. Conclude with `(hfc.comp (continuous_const.add continuous_id)).aestronglyMeasurable`. Establish `hfin : ∑' g : lat Y.b, ∫⁻ x in ZSpan.fundamentalDomain Y.b, ‖thF Y q F (g +ᵥ x)‖ₑ ≠ ⊤`. Rewrite using `[← hfd.lintegral_eq_tsum'' (fun x => ‖thF Y q F x‖ₑ)]`. Conclude with `hfi.2.ne`.

Rewrite `e1` using `[← integral_tsum hmeas hfin]`. Rewrite `e1` using `[unfold_pt hC F]`. Rewrite using `[e1, integral_complex_ofReal, Complex.ofReal_re, GT.l2, setAverage_eq, measureReal_def, vol_eq, ENNReal.toReal_one, inv_one, one_smul]`. Both sides reduce to the same expression.
-/
theorem paUnfold_w (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hC : ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I))
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    Y.l2 q (paTh Y q F) = (paIP q (paTh Y q F) F).re := by
  have := lat_countable (ι := ι) Y.b
  obtain ⟨hfi, hfc⟩ := thF_integrable hP hA Y hq hR0 hlat hR hF
  have hfd := ZSpan.isAddFundamentalDomain Y.b (volume : Measure (EuclideanSpace ℂ ι))
  have e1 : paIP q (paTh Y q F) F = ∑' g : lat Y.b, ∫ x in ZSpan.fundamentalDomain Y.b, thF Y q F (g +ᵥ x) :=
    hfd.integral_eq_tsum'' (thF Y q F) hfi
  have hmeas : ∀ g : lat Y.b, AEStronglyMeasurable (fun x => thF Y q F (g +ᵥ x))
      (volume.restrict (ZSpan.fundamentalDomain Y.b)) := fun g => by
    simp only [Submodule.vadd_def, vadd_eq_add]
    exact (hfc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hfin : ∑' g : lat Y.b, ∫⁻ x in ZSpan.fundamentalDomain Y.b, ‖thF Y q F (g +ᵥ x)‖ₑ ≠ ⊤ := by
    rw [← hfd.lintegral_eq_tsum'' (fun x => ‖thF Y q F x‖ₑ)]
    exact hfi.2.ne
  rw [← integral_tsum hmeas hfin] at e1
  simp_rw [unfold_pt hC F] at e1
  rw [e1, integral_complex_ofReal, Complex.ofReal_re, GT.l2, setAverage_eq, measureReal_def, vol_eq,
    ENNReal.toReal_one, inv_one, one_smul]
  rfl

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
