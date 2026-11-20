import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.CompactIntegralBoundedByQuotientNorm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaL

open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal

noncomputable section

namespace CompanionTheory.D.gk.RF

/- English proof (translation)
Introduce `A _ Q hc hq ht`. Establish `key : ∀ s, ‖Q s‖ < 1 → Q s = 0` using `fun s h => by`. Establish `h1 : ‖Q s‖ ≤ ‖Q s‖ * ‖Q s‖` using `by conv_lhs => rw [← hq s]`. Conclude with `norm_mul_le _ _`. Conclude with `norm_eq_zero.1 (by nlinarith [norm_nonneg (Q s)])`.

Establish `hcl : IsClopen {s | Q s = 0}` using `⟨isClosed_eq hc continuous_const, by`. Establish `: {s | Q s = 0} = {s | ‖Q s‖ < 1}` using `Set.ext fun s => ⟨fun h => by simp [show Q s = 0 from h], key s⟩`. Rewrite using `[this]`. Conclude with `isOpen_lt hc.norm continuous_const⟩`. Take `⟨s₀, hs₀⟩` from `((tendsto_zero_iff_norm_tendsto_zero.1 ht).eventually (gt_mem_nhds one_pos)).exists`.

Introduce `s`. Conclude with `(hcl.eq_univ ⟨s₀, key s₀ hs₀⟩).ge (Set.mem_univ s)`.
-/
theorem idemZero : IdemZero := by
  intro A _ Q hc hq ht
  have key : ∀ s, ‖Q s‖ < 1 → Q s = 0 := fun s h => by
    have h1 : ‖Q s‖ ≤ ‖Q s‖ * ‖Q s‖ := by conv_lhs => rw [← hq s]
                                          exact norm_mul_le _ _
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (Q s)])
  have hcl : IsClopen {s | Q s = 0} := ⟨isClosed_eq hc continuous_const, by
    have : {s | Q s = 0} = {s | ‖Q s‖ < 1} := Set.ext fun s => ⟨fun h => by simp [show Q s = 0 from h], key s⟩
    rw [this]; exact isOpen_lt hc.norm continuous_const⟩
  obtain ⟨s₀, hs₀⟩ := ((tendsto_zero_iff_norm_tendsto_zero.1 ht).eventually (gt_mem_nhds one_pos)).exists
  intro s
  exact (hcl.eq_univ ⟨s₀, key s₀ hs₀⟩).ge (Set.mem_univ s)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/- English proof (translation)
Establish `: Fact ((1 : ℝ≥0∞) ≠ ∞)` using `⟨by simp⟩`. Set `f : Lp ℂ 1 μ` to `hφ.toL1 φ`. Establish `hc : Continuous fun u : G => DomMulAct.mk u • f` using `(DomMulAct.continuous_mk).smul continuous_const`. Establish `h1 : Tendsto (fun u : G => ‖f - DomMulAct.mk u • f‖) (𝓝 1) (𝓝 0)`. Use `(continuous_const.sub hc (f := fun _ => f)).norm.tendsto 1` as an intermediate fact.

Simplify using `using this`. Use `h1.congr fun u => ?_` and prove the remaining obligations. Rewrite using `[L1.norm_eq_integral_norm]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `h2` using `(measurePreserving_mul_left μ u).quasiMeasurePreserving.ae hφ.coeFn_toL1`.

Use `filter_upwards [Lp.coeFn_sub f (DomMulAct.mk u • f), DomMulAct.smul_Lp_ae_eq (DomMulAct.mk u) f, hφ.coeFn_toL1, h2] with y a b c d`. Rewrite using `[a, Pi.sub_apply, b, c]`. Simplify using `only [Equiv.symm_apply_apply, smul_eq_mul]`. Rewrite using `[d]`.
-/
theorem tendsto_transl {φ : G → ℂ} (hφ : Integrable φ μ) :
    Tendsto (fun u => ∫ y, ‖φ y - φ (u * y)‖ ∂μ) (𝓝 1) (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let f : Lp ℂ 1 μ := hφ.toL1 φ
  have hc : Continuous fun u : G => DomMulAct.mk u • f := (DomMulAct.continuous_mk).smul continuous_const
  have h1 : Tendsto (fun u : G => ‖f - DomMulAct.mk u • f‖) (𝓝 1) (𝓝 0) := by
    have := (continuous_const.sub hc (f := fun _ => f)).norm.tendsto 1
    simpa using this
  refine h1.congr fun u => ?_
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have h2 := (measurePreserving_mul_left μ u).quasiMeasurePreserving.ae hφ.coeFn_toL1
  filter_upwards [Lp.coeFn_sub f (DomMulAct.mk u • f), DomMulAct.smul_Lp_ae_eq (DomMulAct.mk u) f, hφ.coeFn_toL1, h2]
    with y a b c d
  rw [a, Pi.sub_apply, b, c]
  simp only [Equiv.symm_apply_apply, smul_eq_mul]
  rw [d]

def eI (r : ℝ) : ℂ := Complex.exp ((r : ℂ) * Complex.I)

/- English proof (translation)
The claim follows from `Complex.norm_exp_ofReal_mul_I r`.
-/
theorem norm_eI (r : ℝ) : ‖eI r‖ = 1 := Complex.norm_exp_ofReal_mul_I r

/- English proof (translation)
Simplify using `only [eI, Complex.ofReal_add, add_mul, Complex.exp_add]`.
-/
theorem eI_add (r r' : ℝ) : eI (r + r') = eI r * eI r' := by
  simp only [eI, Complex.ofReal_add, add_mul, Complex.exp_add]

/- English proof (translation)
Unfold `eI`. Use `fun_prop`.
-/
theorem continuous_eI : Continuous eI := by unfold eI; fun_prop

/- English proof (translation)
Use `le_min ((norm_sub_le _ _).trans (by rw [norm_eI, norm_eI]; norm_num)) ?_` and prove the remaining obligations. Establish `: eI r - eI r' = (eI (r - r') - 1) * eI r'` using `by rw [sub_mul, ← eI_add, sub_add_cancel, one_mul]`. Rewrite using `[this, norm_mul, norm_eI, mul_one, eI, mul_comm]`. Conclude with `Real.norm_exp_I_mul_ofReal_sub_one_le`.
-/
theorem norm_eI_sub (r r' : ℝ) : ‖eI r - eI r'‖ ≤ min 2 |r - r'| := by
  refine le_min ((norm_sub_le _ _).trans (by rw [norm_eI, norm_eI]; norm_num)) ?_
  have : eI r - eI r' = (eI (r - r') - 1) * eI r' := by rw [sub_mul, ← eI_add, sub_add_cancel, one_mul]
  rw [this, norm_mul, norm_eI, mul_one, eI, mul_comm]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/- English proof (translation)
The claim follows from `hφ.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hM)`.
-/
theorem integrable_mul_bc {φ : G → ℂ} (hφ : Integrable φ μ) {F : G → ℂ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ y, ‖F y‖ ≤ M) : Integrable (fun y => φ y * F y) μ :=
  hφ.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hM)

/- English proof (translation)
The claim follows from `_root_.Bl.FirstLemmaL.goal1 hφ hi hF hM`.
-/
theorem reprod {φ : G → ℂ} (hφ : Integrable φ μ) (hi : ∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) {F : G → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ y, ‖F y‖ ≤ M) :
    ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ = ∫ w, φ w * F w ∂μ :=
  _root_.Bl.FirstLemmaL.goal1 hφ hi hF hM

end

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P`. Set `X : Submodule ℂ (G →ᵇ ℂ)` to `{ carrier := {F | (∀ m ∈ N, ∀ x, F (m * x) = F x) ∧ ∀ t x, F (a t * x) = F x} add_mem' := fun h h' => ⟨fun m hm x => by simp [h.1 m hm, h'.1 m hm], fun t x => by simp [h.2, h'.2]⟩ zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ smul_mem' := fun c _ h => ⟨fun m hm x => by simp [h. …`. Set `k : ℝ → (G →ᵇ ℂ) → G → G → ℂ` to `fun s F x y => F (x * y) * eI (s * (Ht (x * y) - Ht x))`. Establish `kc : ∀ s F, Continuous fun p : G × G => k s F p.1 p.2` using `fun s F => (F.continuous.comp continuous_mul).mul (continuous_eI.comp (continuous_const.mul ((P.hcont.comp continuous_mul).sub (P.hcont.comp continuous_fst))))`. Establish `kb : ∀ s F x y, ‖k s F x y‖ ≤ ‖F‖` using `fun s F x y => by`.

Simplify using `only [k, norm_mul, norm_eI, mul_one]`. Conclude with `F.norm_coe_le_norm _`. Establish `ki : ∀ s F x, Integrable (fun y => φ y * k s F x y) μ` using `fun s F x => integrable_mul_bc hφ ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)`. Set `q : ℝ → (G →ᵇ ℂ) → G → ℂ` to `fun s F x => ∫ y, φ y * k s F x y ∂μ`. Establish `qb : ∀ s F x, ‖q s F x‖ ≤ (∫ y, ‖φ y‖ ∂μ) * ‖F‖` using `fun s F x => by`.

Rewrite using `[← integral_mul_const]`. Conclude with `norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Eventually.of_forall fun y => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))`. Establish `qc : ∀ s F, Continuous (q s F)` using `fun s F => continuous_of_dominated (bound := fun y => ‖φ y‖ * ‖F‖) (fun x => (ki s F x).aestronglyMeasurable) (fun x => Eventually.of_forall fun y => by`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))`. Use the proof step `(hφ.norm.mul_const _) (Eventually.of_forall fun y => continuous_const.mul ((kc s F).comp (continuous_id.prodMk continuous_const)))`. Set `Ql : ℝ → (X →ₗ[ℂ] X)` to `fun s => { toFun := fun F => ⟨ofNormedAddCommGroup (q s F) (qc s F) _ (qb s F), fun m hm x => by show q s F (m * x) = q s F x`. Simplify using `only [q, k, mul_assoc m, F.2.1 m hm, P.hN m hm], fun t x => by`.

Use `show q s F (a t * x) = q s F x`. Simplify using `only [q, k, mul_assoc (a t), F.2.2, P.ha, add_sub_add_left_eq_sub]⟩`. Use the proof step `map_add' := fun F F' => Subtype.ext (BoundedContinuousFunction.ext fun x => by show q s (F + F') x = q s F x + q s F' x`. Rewrite using `[← integral_add (ki s F x) (ki s F' x)]`. Simplify using `only [q, k, BoundedContinuousFunction.add_apply, add_mul, mul_add])`.

Use the proof step `map_smul' := fun c F => Subtype.ext (BoundedContinuousFunction.ext fun x => by show q s (c • (F : G →ᵇ ℂ)) x = c * q s F x`. Rewrite using `[← integral_const_mul]`. Simplify using `only [q, k, BoundedContinuousFunction.smul_apply, smul_eq_mul]`. Conclude with `integral_congr_ae (Eventually.of_forall fun y => by ring)) }`. Establish `hφ0 : 0 ≤ ∫ y, ‖φ y‖ ∂μ` using `integral_nonneg fun _ => norm_nonneg _`.

Set `Q : ℝ → (X →L[ℂ] X)` to `fun s => (Ql s).mkContinuous (∫ y, ‖φ y‖ ∂μ) fun F => (BoundedContinuousFunction.norm_le (mul_nonneg hφ0 (norm_nonneg _))).2 (qb s F)`. Establish `Qa : ∀ s (F : X) x, (Q s F : G →ᵇ ℂ) x = q s F x` using `fun _ _ _ => rfl`. Establish `Qn : ∀ (T : X →L[ℂ] X) (d : ℝ), 0 ≤ d → (∀ (F : X) x, ‖(T F : G →ᵇ ℂ) x‖ ≤ d * ‖(F : G →ᵇ ℂ)‖) → ‖T‖ ≤ d` using `fun T d hd h => T.opNorm_le_bound hd fun F => (BoundedContinuousFunction.norm_le (mul_nonneg hd (norm_nonneg _))).2 (h F)`. Take `⟨c, hcc, hc⟩` from `P.bd`. Establish `hQc : Continuous Q`.

Use `continuous_iff_continuousAt.2 fun s₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_` and prove the remaining obligations. Establish `hI : ∀ s, Integrable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ → True` using `fun _ _ => trivial`. Establish `hc0 : ∀ y, 0 ≤ c y` using `fun y => (abs_nonneg _).trans (hc 1 y)`. Establish `hb : ∀ s y, ‖‖φ y‖ * min 2 (|s - s₀| * c y)‖ ≤ ‖φ y‖ * 2` using `fun s y => by`. Rewrite using `[norm_mul, norm_norm, Real.norm_of_nonneg (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))]`.

Conclude with `mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)`. Establish `hm : ∀ s, AEStronglyMeasurable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ` using `fun s => hφ.norm.aestronglyMeasurable.mul (continuous_const.min (continuous_const.mul hcc)).aestronglyMeasurable`. Establish `hd : Continuous fun s => ∫ y, ‖φ y‖ * min 2 (|s - s₀| * c y) ∂μ` using `continuous_of_dominated hm (fun s => Eventually.of_forall (hb s)) (hφ.norm.mul_const 2) (Eventually.of_forall fun y => by fun_prop)`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun s => Qn _ _ (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))) fun F x => ?_) (by simpa using hd.tendsto s₀)` and prove the remaining obligations. Use `show ‖q s F x - q s₀ F x‖ ≤ _`.

Rewrite using `[← integral_sub (ki s F x) (ki s₀ F x), ← integral_mul_const]`. Use `norm_integral_le_of_norm_le (((hφ.norm.mul_const 2).mono' (hm s) (Eventually.of_forall (hb s))).mul_const _) (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [k]`. Rewrite using `[← mul_sub, ← mul_sub, norm_mul, norm_mul, mul_assoc, mul_comm (min _ _)]`. Use `mul_le_mul_of_nonneg_left (mul_le_mul ((F : G →ᵇ ℂ).norm_coe_le_norm _) ((norm_eI_sub _ _).trans (min_le_min le_rfl ?_)) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)` and prove the remaining obligations.

Rewrite using `[← sub_mul, abs_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hc x y) (abs_nonneg _)`. Establish `hQi : ∀ s, Q s * Q s = Q s` using `fun s => ContinuousLinearMap.ext fun F => Subtype.ext (BoundedContinuousFunction.ext fun x => by show ∫ y, φ y * (q s F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = q s F x`. Use `Eq.trans ?_ (reprod hφ hi ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x))` and prove the remaining obligations. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only [q, k, Function.comp_apply]`. Rewrite using `[← integral_mul_const]`. Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [mul_assoc, ← eI_add]`.

Use `congr 3`. Use the proof step `ring)`. Establish `hQt : Tendsto Q atTop (𝓝 0)`. Use `Metric.tendsto_atTop.2 fun e he => ?_` and prove the remaining obligations. Take `⟨τ, hτ, hU⟩` from `P.small _ ((tendsto_transl hφ).eventually (gt_mem_nhds he))`.

Use `⟨Real.pi / τ + 1, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hs0 : 0 < s` using `lt_of_lt_of_le (by positivity) hs`. Rewrite using `[dist_zero_right]`. Use `(Qn _ (e / 2) (by positivity) fun F x => ?_).trans_lt (half_lt_self he)` and prove the remaining obligations. Take `⟨m, hm, hu⟩` from `hU (Real.pi / s) (by`.

Rewrite using `[abs_of_pos (by positivity), div_lt_iff₀ hs0, ← div_lt_iff₀' hτ]; linarith) x`. Use `set u := x⁻¹ * (m * a (Real.pi / s)) * x with hu'`. Establish `h1 : ∀ y, k s F x (u * y) = -k s F x y` using `fun y => by`. Establish `e1 : x * (u * y) = m * (a (Real.pi / s) * (x * y))` using `by rw [hu']; group`. Simplify using `only [k, e1, F.2.1 m hm, F.2.2, P.hN m hm, P.ha]`.

Rewrite using `[add_sub_assoc, mul_add, eI_add, mul_div_cancel₀ _ hs0.ne']`. Simplify using `[eI]`. Establish `h2 : q s F x = -∫ y, φ (u * y) * k s F x y ∂μ`. Rewrite using `[← integral_neg]`. Use `(integral_mul_left_eq_self (fun y => φ y * k s F x y) u).symm.trans ?_` and prove the remaining obligations.

Simplify using `only [h1, mul_neg]`. Establish `hi2 : Integrable (fun y => φ (u * y) * k s F x y) μ` using `integrable_mul_bc (hφ.comp_mul_left u) ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)`. Establish `h3 : 2 * q s F x = ∫ y, (φ y - φ (u * y)) * k s F x y ∂μ`. Simplify using `only [sub_mul]`. Rewrite using `[integral_sub (ki s F x) hi2, two_mul]`.

Use `nth_rewrite 2 [h2]`. Both sides reduce to the same expression. Establish `h4 : ‖2 * q s F x‖ ≤ (∫ y, ‖φ y - φ (u * y)‖ ∂μ) * ‖(F : G →ᵇ ℂ)‖`. Rewrite using `[h3, ← integral_mul_const]`. Conclude with `norm_integral_le_of_norm_le ((hφ.sub (hφ.comp_mul_left u)).norm.mul_const _) (Eventually.of_forall fun y => by`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))`. Rewrite `h4` using `[norm_mul, Complex.norm_two]`. Rewrite using `[Qa]`. Establish `h5 : ∫ y, ‖φ y - φ (u * y)‖ ∂μ < e` using `hu`.

Use polynomial arithmetic with `[norm_nonneg (F : G →ᵇ ℂ)]`. Introduce `s F ⟨hFc, M, hM⟩ hN ha x`. Establish `h0` using `congrArg (fun T : X →L[ℂ] X => (T ⟨ofNormedAddCommGroup F hFc M hM, hN, ha⟩ : G →ᵇ ℂ) x) (idemZero _ Q hQc hQi hQt s)`. Establish `h1 : ∫ y, φ y * (F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = 0` using `h0`. Establish `h2` using `congrArg (· * eI (s * Ht x)) h1`.

Simplify using `only [zero_mul, ← integral_mul_const, mul_assoc, ← eI_add] at h2`. Rewrite using `[← h2]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `beta_reduce`. Use `congr 2`.

Rewrite using `[← mul_add, sub_add_cancel]`. Both sides reduce to the same expression.
-/
theorem selTw : SelTw := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P
  let X : Submodule ℂ (G →ᵇ ℂ) :=
    { carrier := {F | (∀ m ∈ N, ∀ x, F (m * x) = F x) ∧ ∀ t x, F (a t * x) = F x}
      add_mem' := fun h h' => ⟨fun m hm x => by simp [h.1 m hm, h'.1 m hm], fun t x => by simp [h.2, h'.2]⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
      smul_mem' := fun c _ h => ⟨fun m hm x => by simp [h.1 m hm], fun t x => by simp [h.2]⟩ }
  let k : ℝ → (G →ᵇ ℂ) → G → G → ℂ := fun s F x y => F (x * y) * eI (s * (Ht (x * y) - Ht x))
  have kc : ∀ s F, Continuous fun p : G × G => k s F p.1 p.2 := fun s F =>
    (F.continuous.comp continuous_mul).mul (continuous_eI.comp (continuous_const.mul
      ((P.hcont.comp continuous_mul).sub (P.hcont.comp continuous_fst))))
  have kb : ∀ s F x y, ‖k s F x y‖ ≤ ‖F‖ := fun s F x y => by
    simp only [k, norm_mul, norm_eI, mul_one]; exact F.norm_coe_le_norm _
  have ki : ∀ s F x, Integrable (fun y => φ y * k s F x y) μ := fun s F x =>
    integrable_mul_bc hφ ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)
  let q : ℝ → (G →ᵇ ℂ) → G → ℂ := fun s F x => ∫ y, φ y * k s F x y ∂μ
  have qb : ∀ s F x, ‖q s F x‖ ≤ (∫ y, ‖φ y‖ ∂μ) * ‖F‖ := fun s F x => by
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
  have qc : ∀ s F, Continuous (q s F) := fun s F =>
    continuous_of_dominated (bound := fun y => ‖φ y‖ * ‖F‖) (fun x => (ki s F x).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
      (hφ.norm.mul_const _) (Eventually.of_forall fun y =>
        continuous_const.mul ((kc s F).comp (continuous_id.prodMk continuous_const)))
  let Ql : ℝ → (X →ₗ[ℂ] X) := fun s =>
    { toFun := fun F => ⟨ofNormedAddCommGroup (q s F) (qc s F) _ (qb s F), fun m hm x => by
          show q s F (m * x) = q s F x
          simp only [q, k, mul_assoc m, F.2.1 m hm, P.hN m hm], fun t x => by
          show q s F (a t * x) = q s F x
          simp only [q, k, mul_assoc (a t), F.2.2, P.ha, add_sub_add_left_eq_sub]⟩
      map_add' := fun F F' => Subtype.ext (BoundedContinuousFunction.ext fun x => by
        show q s (F + F') x = q s F x + q s F' x
        rw [← integral_add (ki s F x) (ki s F' x)]
        simp only [q, k, BoundedContinuousFunction.add_apply, add_mul, mul_add])
      map_smul' := fun c F => Subtype.ext (BoundedContinuousFunction.ext fun x => by
        show q s (c • (F : G →ᵇ ℂ)) x = c * q s F x
        rw [← integral_const_mul]
        simp only [q, k, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)) }
  have hφ0 : 0 ≤ ∫ y, ‖φ y‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  let Q : ℝ → (X →L[ℂ] X) := fun s => (Ql s).mkContinuous (∫ y, ‖φ y‖ ∂μ) fun F =>
    (BoundedContinuousFunction.norm_le (mul_nonneg hφ0 (norm_nonneg _))).2 (qb s F)
  have Qa : ∀ s (F : X) x, (Q s F : G →ᵇ ℂ) x = q s F x := fun _ _ _ => rfl
  have Qn : ∀ (T : X →L[ℂ] X) (d : ℝ), 0 ≤ d → (∀ (F : X) x, ‖(T F : G →ᵇ ℂ) x‖ ≤ d * ‖(F : G →ᵇ ℂ)‖) → ‖T‖ ≤ d :=
    fun T d hd h => T.opNorm_le_bound hd fun F =>
      (BoundedContinuousFunction.norm_le (mul_nonneg hd (norm_nonneg _))).2 (h F)
  obtain ⟨c, hcc, hc⟩ := P.bd
  have hQc : Continuous Q := by
    refine continuous_iff_continuousAt.2 fun s₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hI : ∀ s, Integrable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ → True := fun _ _ => trivial
    have hc0 : ∀ y, 0 ≤ c y := fun y => (abs_nonneg _).trans (hc 1 y)
    have hb : ∀ s y, ‖‖φ y‖ * min 2 (|s - s₀| * c y)‖ ≤ ‖φ y‖ * 2 := fun s y => by
      rw [norm_mul, norm_norm, Real.norm_of_nonneg (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
    have hm : ∀ s, AEStronglyMeasurable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ := fun s =>
      hφ.norm.aestronglyMeasurable.mul (continuous_const.min (continuous_const.mul hcc)).aestronglyMeasurable
    have hd : Continuous fun s => ∫ y, ‖φ y‖ * min 2 (|s - s₀| * c y) ∂μ :=
      continuous_of_dominated hm (fun s => Eventually.of_forall (hb s)) (hφ.norm.mul_const 2)
        (Eventually.of_forall fun y => by fun_prop)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => Qn _ _ (integral_nonneg fun y =>
      mul_nonneg (norm_nonneg _) (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))) fun F x => ?_)
      (by simpa using hd.tendsto s₀)
    show ‖q s F x - q s₀ F x‖ ≤ _
    rw [← integral_sub (ki s F x) (ki s₀ F x), ← integral_mul_const]
    refine norm_integral_le_of_norm_le
      (((hφ.norm.mul_const 2).mono' (hm s) (Eventually.of_forall (hb s))).mul_const _) (Eventually.of_forall fun y => ?_)
    simp only [k]
    rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, mul_assoc, mul_comm (min _ _)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ((F : G →ᵇ ℂ).norm_coe_le_norm _) ((norm_eI_sub _ _).trans
      (min_le_min le_rfl ?_)) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hc x y) (abs_nonneg _)
  have hQi : ∀ s, Q s * Q s = Q s := fun s => ContinuousLinearMap.ext fun F => Subtype.ext
    (BoundedContinuousFunction.ext fun x => by
      show ∫ y, φ y * (q s F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = q s F x
      refine Eq.trans ?_ (reprod hφ hi ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x))
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [q, k, Function.comp_apply]
      rw [← integral_mul_const]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [mul_assoc, ← eI_add]
      congr 3
      ring)
  have hQt : Tendsto Q atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun e he => ?_
    obtain ⟨τ, hτ, hU⟩ := P.small _ ((tendsto_transl hφ).eventually (gt_mem_nhds he))
    refine ⟨Real.pi / τ + 1, fun s hs => ?_⟩
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    rw [dist_zero_right]
    refine (Qn _ (e / 2) (by positivity) fun F x => ?_).trans_lt (half_lt_self he)
    obtain ⟨m, hm, hu⟩ := hU (Real.pi / s) (by
      rw [abs_of_pos (by positivity), div_lt_iff₀ hs0, ← div_lt_iff₀' hτ]; linarith) x
    set u := x⁻¹ * (m * a (Real.pi / s)) * x with hu'
    have h1 : ∀ y, k s F x (u * y) = -k s F x y := fun y => by
      have e1 : x * (u * y) = m * (a (Real.pi / s) * (x * y)) := by rw [hu']; group
      simp only [k, e1, F.2.1 m hm, F.2.2, P.hN m hm, P.ha]
      rw [add_sub_assoc, mul_add, eI_add, mul_div_cancel₀ _ hs0.ne']
      simp [eI]
    have h2 : q s F x = -∫ y, φ (u * y) * k s F x y ∂μ := by
      rw [← integral_neg]
      refine (integral_mul_left_eq_self (fun y => φ y * k s F x y) u).symm.trans ?_
      simp only [h1, mul_neg]
    have hi2 : Integrable (fun y => φ (u * y) * k s F x y) μ :=
      integrable_mul_bc (hφ.comp_mul_left u) ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)
    have h3 : 2 * q s F x = ∫ y, (φ y - φ (u * y)) * k s F x y ∂μ := by
      simp only [sub_mul]
      rw [integral_sub (ki s F x) hi2, two_mul]
      nth_rewrite 2 [h2]
      rfl
    have h4 : ‖2 * q s F x‖ ≤ (∫ y, ‖φ y - φ (u * y)‖ ∂μ) * ‖(F : G →ᵇ ℂ)‖ := by
      rw [h3, ← integral_mul_const]
      exact norm_integral_le_of_norm_le ((hφ.sub (hφ.comp_mul_left u)).norm.mul_const _)
        (Eventually.of_forall fun y => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
    rw [norm_mul, Complex.norm_two] at h4
    rw [Qa]
    have h5 : ∫ y, ‖φ y - φ (u * y)‖ ∂μ < e := hu
    nlinarith [norm_nonneg (F : G →ᵇ ℂ)]
  intro s F ⟨hFc, M, hM⟩ hN ha x
  have h0 := congrArg (fun T : X →L[ℂ] X => (T ⟨ofNormedAddCommGroup F hFc M hM, hN, ha⟩ : G →ᵇ ℂ) x)
    (idemZero _ Q hQc hQi hQt s)
  have h1 : ∫ y, φ y * (F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = 0 := h0
  have h2 := congrArg (· * eI (s * Ht x)) h1
  simp only [zero_mul, ← integral_mul_const, mul_assoc, ← eI_add] at h2
  rw [← h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  congr 2
  rw [← mul_add, sub_add_cancel]
  rfl

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P F ⟨hFc, M, hM⟩ hN x`. Set `Fr : ℝ → G → ℂ` to `fun r y => F (a (r - Ht y) * y)`. Establish `Frc : Continuous fun p : ℝ × G => Fr p.1 p.2` using `hFc.comp ((P.cont.comp (continuous_fst.sub (P.hcont.comp continuous_snd))).mul continuous_snd)`. Establish `tw : ∀ r s, ∫ y, φ y * (Fr r (x * y) * eI (s * Ht (x * y))) ∂μ = 0` using `fun r s => selTw G μ φ hφ hi N a Ht P s (Fr r) ⟨Frc.comp (continuous_const.prodMk continuous_id), M, fun _ => hM _⟩ (fun m hm y => by`. Use `hN _ (P.norm (r - Ht y) m hm) (a (r - Ht y) * y)` as an intermediate fact.

Simplify using `only [Fr, P.hN m hm]`. Rewrite using `[← this]`. Use `congr 1`. Use the proof step `group)`. Use the proof step `(fun t y => by`.

Simplify using `only [Fr, P.ha]`. Rewrite using `[← mul_assoc, ← P.add]`. Use `congr 3`. Use the proof step `ring) x`. Establish `step : ∀ r (g : ℝ → ℂ), Integrable g → ∫ y, φ y * Fr r (x * y) * (∫ s, g s * eI (s * (r - Ht (x * y)))) ∂μ = 0`.

Introduce `r g hg`. Establish `hc1 : Continuous fun y => Fr r (x * y)` using `Frc.comp (continuous_const.prodMk (continuous_const.mul continuous_id))`. Establish `hI : Integrable (fun p : G × ℝ => φ p.1 * Fr r (x * p.1) * g p.2 * eI (p.2 * (r - Ht (x * p.1)))) (μ.prod volume)` using `((integrable_mul_bc hφ hc1 fun _ => hM _).mul_prod hg).mul_bdd (c := 1) (continuous_eI.comp (continuous_snd.mul (continuous_const.sub (P.hcont.comp (continuous_const.mul continuous_fst))))).aestronglyMeasurable (Eventually.of_forall fun p => (norm_eI _).le)`. Simplify using `only [← integral_const_mul, ← mul_assoc]`. Rewrite using `[integral_integral_swap hI]`.

Use `integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `congrArg (g s * eI (s * r) * ·) (tw r (-s))` as an intermediate fact. Simplify using `only [mul_zero, ← integral_const_mul] at this`. Use `beta_reduce`. Rewrite using `[Pi.zero_apply, ← this]`.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[mul_sub, sub_eq_add_neg, eI_add, neg_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `ψ : ℝ → ℂ` to `fun u => ∫ y, φ y * F (a u * (x * y)) ∂μ`.

Establish `hc2 : Continuous fun p : ℝ × G => F (a p.1 * (x * p.2))` using `hFc.comp ((P.cont.comp continuous_fst).mul (continuous_const.mul continuous_snd))`. Establish `ψc : Continuous ψ` using `continuous_of_dominated (bound := fun y => ‖φ y‖ * M) (fun u => (integrable_mul_bc hφ (hc2.comp (continuous_const.prodMk continuous_id)) fun _ => hM _).aestronglyMeasurable) (fun u => Eventually.of_forall fun y => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))`. Use the proof step `(hφ.norm.mul_const _) (Eventually.of_forall fun y => continuous_const.mul (hc2.comp (continuous_id.prodMk continuous_const)))`.

Establish `key : ∀ g ρ : ℝ → ℂ, Integrable g → Integrable ρ → Continuous ρ → (∀ u, ρ u = ∫ s, g s * eI (s * u)) → ∫ u, ρ u * ψ u = 0`. Introduce `g ρ hg hρ hρc he`. Establish `hI : Integrable (fun p : G × ℝ => φ p.1 * ρ p.2 * F (a p.2 * (x * p.1))) (μ.prod volume)` using `(hφ.mul_prod hρ).mul_bdd (c := M) (hc2.comp continuous_swap).aestronglyMeasurable (Eventually.of_forall fun _ => hM _)`. Establish `hmp : MeasurePreserving (fun p : G × ℝ => (p.1, p.2 - Ht (x * p.1))) (μ.prod volume) (μ.prod volume)` using `MeasurePreserving.skew_product (g := fun y r => r - Ht (x * y)) (MeasurePreserving.id μ) (continuous_snd.sub (P.hcont.comp (continuous_const.mul continuous_fst))).measurable (Eventually.of_forall fun y => (measurePreserving_sub_right volume _).map_eq)`. Establish `hI2` using `hmp.integrable_comp_of_integrable hI`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [ψ, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ y, (∫ u, φ y * ρ u * F (a u * (x * y))) ∂μ := (integral_integral_swap hI).symm`. Use `_ = ∫ y, (∫ r, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y))) ∂μ := by`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Conclude with `(integral_sub_right_eq_self (fun u => φ y * ρ u * F (a u * (x * y))) _).symm`. Use `_ = ∫ r, ∫ y, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y)) ∂μ := integral_integral_swap hI2`. Use `_ = 0 := by`. Use `integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[Pi.zero_apply, ← step r g hg]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[← he]`.

Simplify using `only [Fr]`. Expand and normalize the polynomial expressions, which then agree. Establish `hψ : ∀ u, ψ u = 0`. Establish `hae` using `ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ)) ψc.locallyIntegrable fun ρ hρ hs => by`. Set `f : SchwartzMap ℝ ℂ` to `(hs.comp_left (g := Complex.ofReal) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hρ)`.

Set `g : ℝ → ℂ` to `fun s => ((2 * Real.pi)⁻¹ : ℝ) • FourierTransform.fourier (f : ℝ → ℂ) ((2 * Real.pi)⁻¹ * s)`. Establish `hf : Integrable (FourierTransform.fourier (f : ℝ → ℂ))` using `(FourierTransform.fourier f).integrable`. Establish `h2 : (2 * Real.pi)⁻¹ ≠ 0` using `by positivity`. Use `key g f ((hf.comp_mul_left' h2).smul ((2 * Real.pi)⁻¹ : ℝ)) f.integrable f.continuous fun u => by` as an intermediate fact. Rewrite using `[← congrFun (f.continuous.fourierInv_fourier_eq f.integrable hf) u, Real.fourierInv_eq']`.

Establish `e` using `Measure.integral_comp_mul_left (fun v => Complex.exp ((2 * Real.pi * inner ℝ v u : ℝ) * Complex.I) • FourierTransform.fourier (f : ℝ → ℂ) v) (2 * Real.pi)⁻¹`. Rewrite `e` using `[inv_inv, abs_of_pos (by positivity)]`. Rewrite using `[← inv_smul_smul₀ (show (2 * Real.pi) ≠ 0 by positivity) (∫ v, _), ← e, ← integral_smul]`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Simplify using `only [g, eI, smul_eq_mul, Complex.real_smul, RCLike.inner_apply, conj_trivial]`. Rewrite using `[show 2 * Real.pi * (u * ((2 * Real.pi)⁻¹ * s)) = s * u by field_simp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← this]`. Simplify using `only [Complex.real_smul]`.

Both sides reduce to the same expression. Conclude with `congrFun ((ψc.ae_eq_iff_eq volume continuous_const).1 hae)`. Establish `a0 : a 0 = 1`. Use `P.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `left_eq_mul.1 this`. Simplify `hψ 0` using `[ψ, a0]`.
-/
theorem selP : Sel := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P F ⟨hFc, M, hM⟩ hN x
  let Fr : ℝ → G → ℂ := fun r y => F (a (r - Ht y) * y)
  have Frc : Continuous fun p : ℝ × G => Fr p.1 p.2 :=
    hFc.comp ((P.cont.comp (continuous_fst.sub (P.hcont.comp continuous_snd))).mul continuous_snd)
  have tw : ∀ r s, ∫ y, φ y * (Fr r (x * y) * eI (s * Ht (x * y))) ∂μ = 0 := fun r s =>
    selTw G μ φ hφ hi N a Ht P s (Fr r) ⟨Frc.comp (continuous_const.prodMk continuous_id), M, fun _ => hM _⟩
      (fun m hm y => by
        have := hN _ (P.norm (r - Ht y) m hm) (a (r - Ht y) * y)
        simp only [Fr, P.hN m hm]
        rw [← this]
        congr 1
        group)
      (fun t y => by
        simp only [Fr, P.ha]
        rw [← mul_assoc, ← P.add]
        congr 3
        ring) x

  have step : ∀ r (g : ℝ → ℂ), Integrable g →
      ∫ y, φ y * Fr r (x * y) * (∫ s, g s * eI (s * (r - Ht (x * y)))) ∂μ = 0 := by
    intro r g hg
    have hc1 : Continuous fun y => Fr r (x * y) := Frc.comp (continuous_const.prodMk (continuous_const.mul continuous_id))
    have hI : Integrable (fun p : G × ℝ => φ p.1 * Fr r (x * p.1) * g p.2 * eI (p.2 * (r - Ht (x * p.1))))
        (μ.prod volume) :=
      ((integrable_mul_bc hφ hc1 fun _ => hM _).mul_prod hg).mul_bdd (c := 1)
        (continuous_eI.comp (continuous_snd.mul (continuous_const.sub
          (P.hcont.comp (continuous_const.mul continuous_fst))))).aestronglyMeasurable
        (Eventually.of_forall fun p => (norm_eI _).le)
    simp only [← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap hI]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
    have := congrArg (g s * eI (s * r) * ·) (tw r (-s))
    simp only [mul_zero, ← integral_const_mul] at this
    beta_reduce
    rw [Pi.zero_apply, ← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [mul_sub, sub_eq_add_neg, eI_add, neg_mul]
    ring
  let ψ : ℝ → ℂ := fun u => ∫ y, φ y * F (a u * (x * y)) ∂μ
  have hc2 : Continuous fun p : ℝ × G => F (a p.1 * (x * p.2)) :=
    hFc.comp ((P.cont.comp continuous_fst).mul (continuous_const.mul continuous_snd))
  have ψc : Continuous ψ :=
    continuous_of_dominated (bound := fun y => ‖φ y‖ * M)
      (fun u => (integrable_mul_bc hφ (hc2.comp (continuous_const.prodMk continuous_id)) fun _ => hM _).aestronglyMeasurable)
      (fun u => Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
      (hφ.norm.mul_const _) (Eventually.of_forall fun y =>
        continuous_const.mul (hc2.comp (continuous_id.prodMk continuous_const)))
  have key : ∀ g ρ : ℝ → ℂ, Integrable g → Integrable ρ → Continuous ρ → (∀ u, ρ u = ∫ s, g s * eI (s * u)) →
      ∫ u, ρ u * ψ u = 0 := by
    intro g ρ hg hρ hρc he
    have hI : Integrable (fun p : G × ℝ => φ p.1 * ρ p.2 * F (a p.2 * (x * p.1))) (μ.prod volume) :=
      (hφ.mul_prod hρ).mul_bdd (c := M) (hc2.comp continuous_swap).aestronglyMeasurable
        (Eventually.of_forall fun _ => hM _)
    have hmp : MeasurePreserving (fun p : G × ℝ => (p.1, p.2 - Ht (x * p.1))) (μ.prod volume) (μ.prod volume) :=
      MeasurePreserving.skew_product (g := fun y r => r - Ht (x * y)) (MeasurePreserving.id μ)
        (continuous_snd.sub (P.hcont.comp (continuous_const.mul continuous_fst))).measurable
        (Eventually.of_forall fun y => (measurePreserving_sub_right volume _).map_eq)
    have hI2 := hmp.integrable_comp_of_integrable hI
    calc ∫ u, ρ u * ψ u = ∫ u, ∫ y, φ y * ρ u * F (a u * (x * y)) ∂μ := by
          simp only [ψ, ← integral_const_mul]
          congr 1; funext u; congr 1; funext y; ring
      _ = ∫ y, (∫ u, φ y * ρ u * F (a u * (x * y))) ∂μ := (integral_integral_swap hI).symm
      _ = ∫ y, (∫ r, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y))) ∂μ := by
          congr 1; funext y
          exact (integral_sub_right_eq_self (fun u => φ y * ρ u * F (a u * (x * y))) _).symm
      _ = ∫ r, ∫ y, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y)) ∂μ := integral_integral_swap hI2
      _ = 0 := by
          refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
          beta_reduce
          rw [Pi.zero_apply, ← step r g hg]
          congr 1; funext y
          rw [← he]
          simp only [Fr]
          ring
  have hψ : ∀ u, ψ u = 0 := by
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ)) ψc.locallyIntegrable
      fun ρ hρ hs => by
        let f : SchwartzMap ℝ ℂ := (hs.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
          (Complex.ofRealCLM.contDiff.comp hρ)
        let g : ℝ → ℂ := fun s => ((2 * Real.pi)⁻¹ : ℝ) • FourierTransform.fourier (f : ℝ → ℂ) ((2 * Real.pi)⁻¹ * s)
        have hf : Integrable (FourierTransform.fourier (f : ℝ → ℂ)) := (FourierTransform.fourier f).integrable
        have h2 : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
        have := key g f ((hf.comp_mul_left' h2).smul ((2 * Real.pi)⁻¹ : ℝ)) f.integrable f.continuous fun u => by
          rw [← congrFun (f.continuous.fourierInv_fourier_eq f.integrable hf) u, Real.fourierInv_eq']
          have e := Measure.integral_comp_mul_left
            (fun v => Complex.exp ((2 * Real.pi * inner ℝ v u : ℝ) * Complex.I) • FourierTransform.fourier (f : ℝ → ℂ) v)
            (2 * Real.pi)⁻¹
          rw [inv_inv, abs_of_pos (by positivity)] at e
          rw [← inv_smul_smul₀ (show (2 * Real.pi) ≠ 0 by positivity) (∫ v, _), ← e, ← integral_smul]
          congr 1; funext s
          simp only [g, eI, smul_eq_mul, Complex.real_smul, RCLike.inner_apply, conj_trivial]
          rw [show 2 * Real.pi * (u * ((2 * Real.pi)⁻¹ * s)) = s * u by field_simp]
          ring
        rw [← this]
        simp only [Complex.real_smul]
        rfl
    exact congrFun ((ψc.ae_eq_iff_eq volume continuous_const).1 hae)
  have a0 : a 0 = 1 := by
    have := P.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  simpa [ψ, a0] using hψ 0

end CompanionTheory.D.gk.RF
