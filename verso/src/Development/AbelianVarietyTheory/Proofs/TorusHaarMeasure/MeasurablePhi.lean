import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralFundSetInterLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralBallLtTopOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOpenSaturation
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivInFFPf

open Filter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Take `⟨x1, ho1, F1, hF1, hlt⟩` from `hfin`. Use `FundSetPf.countable_GL (E := E) (r := r)` as an intermediate fact. Establish `hle` using `GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1) measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1`. Simplify using `only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hle`. Set `S : Set (Frame X.Ψ r)` to `⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1`.

Establish `hS : MeasurableSet S` using `MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X ho1 hF1.1 hF1.2.1)`. Establish `hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)`. Introduce `x`. Simplify using `only [S, Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, y, hy, b, hb, h⟩`. Use `⟨y, hy, γ.1, γ.2, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]`. Introduce and unpack `⟨y, hy, γ, hγ, b, hb, rfl⟩`. Conclude with `⟨⟨γ, hγ⟩, y, hy, b, hb, FundSetPf.lact_inv _ _⟩`.

Establish `hψ : Measurable (Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞))` using `measurable_one.indicator hS.compl`. Establish `hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Sᶜ.indicator 1 x`. Introduce `x _ b hb`. Establish `: rmul x b ∈ S ↔ x ∈ S`. Simplify using `only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]`.

Simplify using `only [Set.indicator, Set.mem_compl_iff, this, Pi.one_apply]`. Establish `h0 : ∫⁻ z, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0`. Rewrite using `[hM r X x0 x1 ho ho1 _ hψ hB]`. Use `(lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero` and prove the remaining obligations. Use `filter_upwards [hF1.2.2.2] with z hz`.

Conclude with `Set.indicator_of_notMem (Set.notMem_compl_iff.2 ((hSiff _).2 hz)) _`. Establish `hae` using `(lintegral_eq_zero_iff (hψ.comp (FundSetPf.cont_cpt X x0).measurable)).1 h0`. Use `lt_of_le_of_lt (measure_mono_ae ?_) (hle.trans_lt hlt)` and prove the remaining obligations. Use `filter_upwards [hae] with z hz hzF`. Use `⟨hzF, (hSiff _).1 ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Establish `: Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) = 0` using `hz`. Rewrite `this` using `[Set.indicator_of_mem (show _ ∈ Sᶜ from hn)]`. Conclude with `one_ne_zero this`.
-/
theorem muF_lt_top (hM : MeasInvStatement (E := E)) (hfin : FinMu X) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) : muF X x0 FF < ⊤ := by
  classical
  obtain ⟨x1, ho1, F1, hF1, hlt⟩ := hfin
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hle
  let S : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X ho1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
  have hψ : Measurable (Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) := measurable_one.indicator hS.compl
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Sᶜ.indicator 1 x := by
    intro x _ b hb
    have : rmul x b ∈ S ↔ x ∈ S := by
      simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
        GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
    simp only [Set.indicator, Set.mem_compl_iff, this, Pi.one_apply]
  have h0 : ∫⁻ z, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ hψ hB]
    refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
    filter_upwards [hF1.2.2.2] with z hz
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 ((hSiff _).2 hz)) _
  have hae := (lintegral_eq_zero_iff (hψ.comp (FundSetPf.cont_cpt X x0).measurable)).1 h0
  refine lt_of_le_of_lt (measure_mono_ae ?_) (hle.trans_lt hlt)
  filter_upwards [hae] with z hz hzF
  refine ⟨hzF, (hSiff _).1 ?_⟩
  by_contra hn
  have : Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) = 0 := hz
  rw [Set.indicator_of_mem (show _ ∈ Sᶜ from hn)] at this
  exact one_ne_zero this

variable (Xa : ArchInM X) (Fl : FlatM X Xa)

/- English proof (translation)
Use `FundSetPf.countable_GL (E := E) (r := r)` as an intermediate fact. Establish `hn` using `Xa.n_ge`. Establish `: Nonempty (Fin (nd X))` using `⟨⟨0, by omega⟩⟩`. Establish `hc : (⋃ j : Fin Fl.δ, ⋃ γ : GL (Fin r) E, {z | ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (Fl.xs j) b)}).Countable`. Use `Set.countable_iUnion fun j => Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_` and prove the remaining obligations.

Introduce and unpack `z ⟨b, hb, h⟩ z' ⟨b', hb', h'⟩`. Use `FundSetPf.cpt_uniq X ho (ExtFPf.invF_mem X hb) (ExtFPf.invF_mem X hb') ?_` and prove the remaining obligations. Rewrite using `[h, h', FundSetPf.lact_rmul, FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_invF X hb']`. Establish `hac : muF X x0 ≪ volume` using `(withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict`. Use `filter_upwards [hac.ae_le (hc.ae_notMem volume)] with z hz hzO`.

Assume the negation of the conclusion as `hs`. Use `push Not at hs`. Take `⟨j, γ, -, b, hb, h⟩` from `(Fl.S_eq _ hzO).1 hs`. Conclude with `hz (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨γ, b, hb, h⟩⟩)`.
-/
theorem ae_exists_ne {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 → ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := by
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hn := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have hc : (⋃ j : Fin Fl.δ, ⋃ γ : GL (Fin r) E,
      {z | ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (Fl.xs j) b)}).Countable := by
    refine Set.countable_iUnion fun j => Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_
    rintro z ⟨b, hb, h⟩ z' ⟨b', hb', h'⟩
    refine FundSetPf.cpt_uniq X ho (ExtFPf.invF_mem X hb) (ExtFPf.invF_mem X hb') ?_
    rw [h, h', FundSetPf.lact_rmul, FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_assoc,
      ExtFPf.rmul_invF X hb, ExtFPf.rmul_invF X hb']
  have hac : muF X x0 ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  filter_upwards [hac.ae_le (hc.ae_notMem volume)] with z hz hzO
  by_contra hs
  push Not at hs
  obtain ⟨j, γ, -, b, hb, h⟩ := (Fl.S_eq _ hzO).1 hs
  exact hz (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨γ, b, hb, h⟩⟩)

noncomputable def phi (n : ℕ) (h : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (X.dom.indicator (fun x => X.pnorm (Xa.Fp + n • Xa.L) h x ^ 2) x *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) x ^ (-(1 / 2 : ℝ)) *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) x ^ (-((n : ℝ) - 1 / 2)))

/- English proof (translation)
Simplify using `only [phi, Set.indicator_of_mem hx]`.
-/
theorem phi_of_mem (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi Xa Fl n h x = ENNReal.ofReal (X.pnorm (Xa.Fp + n • Xa.L) h x ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
  simp only [phi, Set.indicator_of_mem hx]

/- English proof (translation)
The claim follows from `hP.1.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)`.
-/
theorem pnorm_contOn {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom :=
  hP.1.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)

/- English proof (translation)
Rewrite using `[← Set.piecewise_eq_indicator]`. Conclude with `ContinuousOn.measurable_piecewise hf continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet`.
-/
theorem measurable_cut {f : Frame X.Ψ r → ℝ} (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

/- English proof (translation)
Establish `h1` using `measurable_cut ((pnorm_contOn hh).pow 2)`. Establish `h2 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)` using `measurable_cut (continuousOn_finsetSum _ fun k _ => (pnorm_contOn (Xa.w_van k).1.1.1).pow 2)`. Establish `h3 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2)` using `measurable_cut (continuousOn_finsetSum _ fun k _ => (pnorm_contOn (Fl.s_van k).1.1.1).pow 2)`. Conclude with `((h1.mul (h2.pow_const _)).mul (h3.pow_const _)).ennreal_ofReal`.
-/
theorem measurable_phi (n : ℕ) {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (Xa.Fp + n • Xa.L) h) :
    Measurable (phi Xa Fl n h) := by
  have h1 := measurable_cut ((pnorm_contOn hh).pow 2)
  have h2 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) :=
    measurable_cut (continuousOn_finsetSum _ fun k _ => (pnorm_contOn (Xa.w_van k).1.1.1).pow 2)
  have h3 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) :=
    measurable_cut (continuousOn_finsetSum _ fun k _ => (pnorm_contOn (Fl.s_van k).1.1.1).pow 2)
  exact ((h1.mul (h2.pow_const _)).mul (h3.pow_const _)).ennreal_ofReal

/- English proof (translation)
Introduce `γ hγ x hx b hb`. Establish `hxb` using `OntoS.dom_rmul X hx hb`. Establish `key : ∀ {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}, X.IsSec la P → X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x` using `fun hP => by`. Rewrite using `[DivMetricPf.pnorm_lact hN' hP hγ hxb, DivMetricPf.pnorm_rmul hN hP hx hb]`. Rewrite using `[phi_of_mem Xa Fl n h hx, phi_of_mem Xa Fl n h (OntoS.dom_lact X hγ hxb), key hh]`.

Simplify using `only [fun k => key (Xa.w_van k).1.1.1, fun k => key (Fl.s_van k).1.1.1]`.
-/
theorem phi_inv (hN : NfacRmulStatement (E := E)) (hN' : NfacLactStatement (E := E)) (n : ℕ)
    {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (Xa.Fp + n • Xa.L) h) :
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phi Xa Fl n h (lact γ (rmul x b)) = phi Xa Fl n h x := by
  intro γ hγ x hx b hb
  have hxb := OntoS.dom_rmul X hx hb
  have key : ∀ {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}, X.IsSec la P →
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x := fun hP => by
    rw [DivMetricPf.pnorm_lact hN' hP hγ hxb, DivMetricPf.pnorm_rmul hN hP hx hb]
  rw [phi_of_mem Xa Fl n h hx, phi_of_mem Xa Fl n h (OntoS.dom_lact X hγ hxb), key hh]
  simp only [fun k => key (Xa.w_van k).1.1.1, fun k => key (Fl.s_van k).1.1.1]

/- English proof (translation)
Simplify using `only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]`. Conclude with `mul_pos (Real.exp_pos _) (sum_normSq_pos h)`.
-/
theorem sum_pnorm_pos {N : ℕ} {la : Wt X.Ψ r} {P : Fin N → Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : ∃ k, P k x ≠ 0) : 0 < ∑ k, X.pnorm la (P k) x ^ 2 := by
  simp only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]
  exact mul_pos (Real.exp_pos _) (sum_normSq_pos h)

/- English proof (translation)
Establish `hw` using `sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz x hx)`. Establish `hs'` using `sum_pnorm_pos (la := Xa.L) hx hs`. Rewrite using `[phi_of_mem Xa Fl n h hx, Wdiv_eq_pnorm Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hs', pnorm_sq_eq_exp hx (Xa.Fp + n • Xa.L), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_eq (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : ∃ k, Fl.s k x ≠ 0) :
    phi Xa Fl n h x = ENNReal.ofReal (‖h x‖ ^ 2) * Wdiv X Xa Fl n x := by
  have hw := sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz x hx)
  have hs' := sum_pnorm_pos (la := Xa.L) hx hs
  rw [phi_of_mem Xa Fl n h hx, Wdiv_eq_pnorm Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw,
    ENNReal.ofReal_rpow_of_pos hs', pnorm_sq_eq_exp hx (Xa.Fp + n • Xa.L),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  ring

/- English proof (translation)
Distinguish the cases in `hs : ∃ k, Fl.s k x ≠ 0`. Establish `hw` using `sum_normSq_w_pos Xa hx`. Establish `hs' : 0 < ∑ k, ‖Fl.s k x‖ ^ 2` using `sum_normSq_pos hs`. Rewrite using `[phi_eq Xa Fl n h hx hs, Wdiv_of_mem Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hs', DivMetricPf.exp_neg_phla hx, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]`. Conclude with `le_of_eq (by ring)`.

Use `push Not at hs`. Establish `hn' : -((n : ℝ) - 1 / 2) ≠ 0`. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = 0`.

Simplify using `[pnorm_sq_eq_exp hx, hs]`. Rewrite using `[phi_of_mem Xa Fl n h hx, h0, Real.zero_rpow hn', mul_zero, ENNReal.ofReal_zero]`. Conclude with `zero_le`.
-/
theorem phi_le_local {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi Xa Fl n h x ≤
      ENNReal.ofReal (X.nfac Xa.Fp x ^ 2 * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (‖h x‖ ^ 2 * (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
  by_cases hs : ∃ k, Fl.s k x ≠ 0
  · have hw := sum_normSq_w_pos Xa hx
    have hs' : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_normSq_pos hs
    rw [phi_eq Xa Fl n h hx hs, Wdiv_of_mem Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw,
      ENNReal.ofReal_rpow_of_pos hs', DivMetricPf.exp_neg_phla hx,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    exact le_of_eq (by ring)
  · push Not at hs
    have hn' : -((n : ℝ) - 1 / 2) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h0 : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = 0 := by
      simp [pnorm_sq_eq_exp hx, hs]
    rw [phi_of_mem Xa Fl n h hx, h0, Real.zero_rpow hn', mul_zero, ENNReal.ofReal_zero]
    exact zero_le

/- English proof (translation)
Set `K : Frame X.Ψ r → ℝ` to `fun x => X.nfac Xa.Fp x ^ 2 * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ))`. Establish `hK : ContinuousOn K X.dom` using `((ExtFPf.nfac_contOn X Xa.Fp).pow 2).mul ((continuousOn_finsetSum _ fun k _ => (Xa.w_van k).1.1.1.1.continuousOn.norm.pow 2).rpow_const fun x hx => Or.inl (sum_normSq_w_pos Xa hx).ne')`. Establish `hd` using `(FourierCoefficientDomain.isOpen_dom X).mem_nhds hy`. Establish `ht : Tendsto (cpt X y) (𝓝 0) (𝓝 y)`. Use `(FundSetPf.cont_cpt X y).tendsto 0` as an intermediate fact.

Rewrite `this` using `[IW.cpt_zero]`. Then use the resulting hypothesis. Establish `hb : ∀ᶠ x in 𝓝 y, K x < K y + 1` using `(hK.continuousAt hd).eventually_lt continuousAt_const (by simp)`. Establish `hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), cpt X y z ∈ X.dom ∧ K (cpt X y z) < K y + 1 ∧ z ∈ Metric.ball (0 : V (nd X)) ρ` using `by filter_upwards [ht.eventually hd, ht.eventually hb, Metric.ball_mem_nhds (0 : V (nd X)) hρ] with z a b c`. Conclude with `⟨a, b, c⟩`. Take `⟨δ, hδ, hB⟩` from `Metric.eventually_nhds_iff_ball.1 hall`.

Use `⟨δ, hδ, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' measurableSet_ball fun z hz => ?_` and prove the remaining obligations. Use `(phi_le_local Xa Fl hn h (hB z hz).1).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_left (ENNReal.ofReal_le_ofReal (hB z hz).2.1.le) _`.

Use `_ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_mono_set fun z hz => (hB z hz).2.2).trans_lt hint)`.
-/
theorem local_int {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) < ⊤) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', phi Xa Fl n h (cpt X y z) < ⊤ := by
  let K : Frame X.Ψ r → ℝ := fun x => X.nfac Xa.Fp x ^ 2 * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ))
  have hK : ContinuousOn K X.dom :=
    ((ExtFPf.nfac_contOn X Xa.Fp).pow 2).mul ((continuousOn_finsetSum _ fun k _ =>
      (Xa.w_van k).1.1.1.1.continuousOn.norm.pow 2).rpow_const
        fun x hx => Or.inl (sum_normSq_w_pos Xa hx).ne')
  have hd := (FourierCoefficientDomain.isOpen_dom X).mem_nhds hy
  have ht : Tendsto (cpt X y) (𝓝 0) (𝓝 y) := by
    have := (FundSetPf.cont_cpt X y).tendsto 0
    rwa [IW.cpt_zero] at this
  have hb : ∀ᶠ x in 𝓝 y, K x < K y + 1 := (hK.continuousAt hd).eventually_lt continuousAt_const (by simp)
  have hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), cpt X y z ∈ X.dom ∧ K (cpt X y z) < K y + 1 ∧
      z ∈ Metric.ball (0 : V (nd X)) ρ := by
    filter_upwards [ht.eventually hd, ht.eventually hb, Metric.ball_mem_nhds (0 : V (nd X)) hρ] with z a b c
    exact ⟨a, b, c⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨δ, hδ, ?_⟩
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) δ, phi Xa Fl n h (cpt X y z)
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (K y + 1) * ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        refine (phi_le_local Xa Fl hn h (hB z hz).1).trans ?_
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hB z hz).2.1.le) _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((lintegral_mono_set fun z hz => (hB z hz).2.2).trans_lt hint)

/- English proof (translation)
Establish `hn' : 0 ≤ (n : ℝ) - 1 / 2`. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKs : 0 < K * s` using `hw.trans_le hK`. Establish `hs' : 0 < s` using `lt_of_le_of_ne hs (by rintro rfl; simp at hKs)`.

Establish `hK0 : 0 < K` using `(mul_pos_iff_of_pos_right hs').1 hKs`. Rewrite using `[abs_of_pos hK0]`. Establish `h1 : s ^ (-((n : ℝ) - 1 / 2)) ≤ K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2))`. Establish `: (K * s) ^ (-((n : ℝ) - 1 / 2)) ≤ w ^ (-((n : ℝ) - 1 / 2))` using `Real.rpow_le_rpow_of_nonpos hw hK (by linarith)`. Rewrite `this` using `[Real.mul_rpow hK0.le hs, Real.rpow_neg hK0.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK0 _)]`.

Conclude with `this`. Establish `h2 : w ^ (-(1 / 2 : ℝ)) * w ^ (-((n : ℝ) - 1 / 2)) = w ^ (-(n : ℝ))`. Rewrite using `[← Real.rpow_add hw]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : e * ‖a - b‖ ^ 2 ≤ 2 * F + 2 * G`. Establish `h4 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`. Use `pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg (‖a‖ - ‖b‖)]`. Rewrite using `[hF, hG]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 he]`. Establish `h5 : G * w ^ (-(n : ℝ)) ≤ C`. Rewrite using `[Real.rpow_neg hw.le, Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos hw n)]`. Conclude with `hC`. Establish `hKp` using `Real.rpow_pos_of_pos hK0 ((n : ℝ) - 1 / 2)`.

Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ 2 * F + 2 * G` using `le_trans (by positivity) h3`. Use `gcongr`. Use `_ = 2 * K ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) + 2 * K ^ ((n : ℝ) - 1 / 2) * (G * w ^ (-(n : ℝ))) := by rw [← h2]; ring`. Use `_ ≤ _ := by gcongr`.
-/
theorem real_bound {e F G w s K C : ℝ} {a b : ℂ} {n : ℕ} (hn : 1 ≤ n) (he : 0 ≤ e) (hF : F = e * ‖a‖ ^ 2)
    (hG : G = e * ‖b‖ ^ 2) (hw : 0 < w) (hs : 0 ≤ s) (hK : w ≤ K * s) (hC : G ≤ C * w ^ n) :
    e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2)) ≤
      2 * |K| ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) + 2 * |K| ^ ((n : ℝ) - 1 / 2) * C := by
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hKs : 0 < K * s := hw.trans_le hK
  have hs' : 0 < s := lt_of_le_of_ne hs (by rintro rfl; simp at hKs)
  have hK0 : 0 < K := (mul_pos_iff_of_pos_right hs').1 hKs
  rw [abs_of_pos hK0]
  have h1 : s ^ (-((n : ℝ) - 1 / 2)) ≤ K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2)) := by
    have : (K * s) ^ (-((n : ℝ) - 1 / 2)) ≤ w ^ (-((n : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hw hK (by linarith)
    rw [Real.mul_rpow hK0.le hs, Real.rpow_neg hK0.le,
      inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK0 _)] at this
    exact this
  have h2 : w ^ (-(1 / 2 : ℝ)) * w ^ (-((n : ℝ) - 1 / 2)) = w ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hw]; congr 1; ring
  have h3 : e * ‖a - b‖ ^ 2 ≤ 2 * F + 2 * G := by
    have h4 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [hF, hG]
    nlinarith [mul_le_mul_of_nonneg_left h4 he]
  have h5 : G * w ^ (-(n : ℝ)) ≤ C := by
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos hw n)]
    exact hC
  have hKp := Real.rpow_pos_of_pos hK0 ((n : ℝ) - 1 / 2)
  calc e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2))
      ≤ (2 * F + 2 * G) * w ^ (-(1 / 2 : ℝ)) * (K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2))) := by
        have : 0 ≤ 2 * F + 2 * G := le_trans (by positivity) h3
        gcongr
    _ = 2 * K ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) +
          2 * K ^ ((n : ℝ) - 1 / 2) * (G * w ^ (-(n : ℝ))) := by rw [← h2]; ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `hN hM r X Xa Fl hfin x0 ho FF hF f g hf hg hfi ⟨C, hC⟩ hvan`. Establish `h2` using `Xa.n_ge`. Establish `hT` using `Xa.T_ge`. Establish `hnT : nd X ≤ Xa.T` using `by nlinarith`. Establish `hT1 : 1 ≤ Xa.T` using `by omega`.

Establish `hh : X.IsSec (Xa.Fp + Xa.T • Xa.L) (fun x => f x - g x)` using `⟨hf.1.sub hg.1, fun x hx b hb => by simp only [hf.2.1 x hx b hb, hg.2.1 x hx b hb, mul_sub], fun γ hγ x hx => by simp only [hf.2.2 γ hγ x hx, hg.2.2 γ hγ x hx, mul_sub]⟩`. Use `set φ := phi Xa Fl Xa.T (fun x => f x - g x) with hφ`. Establish `hφm : Measurable φ` using `measurable_phi Xa Fl _ hh`. Establish `hφi` using `phi_inv Xa Fl hN.1 hN.2.1 _ hh`. Establish `hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x` using `fun x hx b hb => by`.

Establish `h` using `hφi 1 X.Γ.one_mem x hx b hb`. Rewrite `h` using `[FundSetPf.lact_one]`. Then use the resulting hypothesis. Establish `hloc : ∀ j, ∃ U : Set (Frame X.Ψ r), IsOpen U ∧ Fl.xs j ∈ U ∧ (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) ∧ ∫⁻ z in FF ∩ cpt X x0 ⁻¹' U, φ (cpt X x0 z) ∂muF X x0 < ⊤`. Introduce `j`. Take `⟨ρ, hρ, hint⟩` from `hvan j`.

Rewrite `hint` using `[Nat.cast_sub hnT, sub_add_cancel]`. Take `⟨ρ1, hρ1, hint1⟩` from `local_int Xa Fl hT1 (fun x => f x - g x) (Fl.xs_mem j) hρ hint`. Take `⟨x1, ho1, b1, hb1, e1⟩` from `ortho_holds r X _ (Fl.xs_mem j)`. Rewrite `hint1` using `[e1]`. Take `⟨ρ2, hρ2, hsub, hint2⟩` from `GlobalTheory.ChartChange.chart_change r X x1 b1 ho1 hb1 φ hφm hφB ρ1 hρ1 hint1`.

Use `⟨_, GlobalTheory.SatOpen.isOpen_saturation r X x1 ho1 _ Metric.isOpen_ball hsub, ⟨0, Metric.mem_ball_self hρ2, 1, X.Γ.one_mem, b1, hb1, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[FundSetPf.lact_one, IW.cpt_zero]`. Conclude with `e1`. Introduce and unpack `_ ⟨y, hy, γ, hγ, b, hb, rfl⟩ γ' hγ' b' hb'`. Use `⟨y, hy, γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩` and prove the remaining obligations.

Rewrite using `[FundSetPf.lact_mul, ← ExtFPf.rmul_assoc, FundSetPf.lact_rmul γ (rmul _ b)]`. Conclude with `(GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF φ hφm hφi _ measurableSet_ball hsub).trans_lt hint2`. Use `choose U hUo hUx hUs hUi using hloc`. Take `⟨K, hK⟩` from `Fl.family_le_coords (⋃ j, U j) (isOpen_iUnion hUo) (fun j => Set.mem_iUnion.2 ⟨j, hUx j⟩) (fun x hx γ hγ b hb => by`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 hx`.

Conclude with `Set.mem_iUnion.2 ⟨j, hUs j x hj γ hγ b hb⟩)`. Establish `hmeas : MeasurableSet (FF \ cpt X x0 ⁻¹' ⋃ j, U j)` using `hF.1.diff ((isOpen_iUnion hUo).preimage (FundSetPf.cont_cpt X x0)).measurableSet`. Establish `hoff : ∫⁻ z in FF \ cpt X x0 ⁻¹' ⋃ j, U j, φ (cpt X x0 z) ∂muF X x0 < ⊤` using `by set A : ℝ := 2 * |K| ^ ((Xa.T : ℝ) - 1 / 2) with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Use `setLIntegral_mono' hmeas fun z hz => ?_` and prove the remaining obligations. Establish `hx : cpt X x0 z ∈ X.dom` using `hF.2.1 hz.1`. Rewrite using `[hφ, phi_of_mem Xa Fl _ _ hx, ← ENNReal.ofReal_mul hA0]`. Use `le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le` and prove the remaining obligations. Rewrite using `[pnorm_sq_eq_exp hx (Xa.Fp + Xa.T • Xa.L) (fun x => f x - g x)]`.

Conclude with `real_bound hT1 (Real.exp_pos _).le (pnorm_sq_eq_exp hx _ f) (pnorm_sq_eq_exp hx _ g) (sum_pnorm_pos hx (Xa.w_nz _ hx)) (by positivity) (hK _ hx hz.2) (hC _ hx)`. Use `_ ≤ _ := lintegral_mono_set Set.diff_subset`. Use `_ < ⊤ := by`. Rewrite using `[lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]`. Conclude with `ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (muF_lt_top hM hfin ho hF)⟩`.

Establish `hcov : FF ⊆ (⋃ j, FF ∩ cpt X x0 ⁻¹' U j) ∪ (FF \ cpt X x0 ⁻¹' ⋃ j, U j)`. Introduce `z hz`. Distinguish the cases in `h : cpt X x0 z ∈ ⋃ j, U j`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 h`. Conclude with `Or.inl (Set.mem_iUnion.2 ⟨j, hz, hj⟩)`.

Conclude with `Or.inr ⟨hz, h⟩`. Establish `hall : ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0 < ⊤`. Use `((lintegral_mono_set hcov).trans (lintegral_union_le _ _ _)).trans_lt (ENNReal.add_lt_top.2 ⟨(lintegral_iUnion_le _ _).trans_lt ?_, hoff⟩)` and prove the remaining obligations. Rewrite using `[tsum_fintype]`. Conclude with `ENNReal.sum_lt_top.2 fun j _ => hUi j`.

Establish `hcongr : (fun z => ENNReal.ofReal (‖f (cpt X x0 z) - g (cpt X x0 z)‖ ^ 2) * Wdiv X Xa Fl Xa.T (cpt X x0 z)) =ᵐ[(muF X x0).restrict FF] fun z => φ (cpt X x0 z)` using `by filter_upwards [ae_restrict_mem hF.1, ae_restrict_of_ae (s := FF) (ae_exists_ne Xa Fl ho)] with z hz hs`. Conclude with `(phi_eq Xa Fl Xa.T (fun x => f x - g x) (hF.2.1 hz) (hs (hF.2.1 hz))).symm`. Conclude with `(lintegral_congr_ae hcongr).trans_lt hall`.
-/
theorem divInFF_of :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) →
      MeasInvStatement (E := E) → GlobalTheory.Up.DivInFF (E := E) := by
  intro hN hM r X Xa Fl hfin x0 ho FF hF f g hf hg hfi ⟨C, hC⟩ hvan
  have h2 := Xa.n_ge
  have hT := Xa.T_ge
  have hnT : nd X ≤ Xa.T := by nlinarith
  have hT1 : 1 ≤ Xa.T := by omega
  have hh : X.IsSec (Xa.Fp + Xa.T • Xa.L) (fun x => f x - g x) :=
    ⟨hf.1.sub hg.1, fun x hx b hb => by simp only [hf.2.1 x hx b hb, hg.2.1 x hx b hb, mul_sub],
      fun γ hγ x hx => by simp only [hf.2.2 γ hγ x hx, hg.2.2 γ hγ x hx, mul_sub]⟩
  set φ := phi Xa Fl Xa.T (fun x => f x - g x) with hφ
  have hφm : Measurable φ := measurable_phi Xa Fl _ hh
  have hφi := phi_inv Xa Fl hN.1 hN.2.1 _ hh
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := fun x hx b hb => by
    have h := hφi 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at h
  have hloc : ∀ j, ∃ U : Set (Frame X.Ψ r), IsOpen U ∧ Fl.xs j ∈ U ∧
      (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) ∧
      ∫⁻ z in FF ∩ cpt X x0 ⁻¹' U, φ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    intro j
    obtain ⟨ρ, hρ, hint⟩ := hvan j
    rw [Nat.cast_sub hnT, sub_add_cancel] at hint
    obtain ⟨ρ1, hρ1, hint1⟩ := local_int Xa Fl hT1 (fun x => f x - g x) (Fl.xs_mem j) hρ hint
    obtain ⟨x1, ho1, b1, hb1, e1⟩ := ortho_holds r X _ (Fl.xs_mem j)
    rw [e1] at hint1
    obtain ⟨ρ2, hρ2, hsub, hint2⟩ := GlobalTheory.ChartChange.chart_change r X x1 b1 ho1 hb1 φ hφm hφB ρ1 hρ1 hint1
    refine ⟨_, GlobalTheory.SatOpen.isOpen_saturation r X x1 ho1 _ Metric.isOpen_ball hsub,
      ⟨0, Metric.mem_ball_self hρ2, 1, X.Γ.one_mem, b1, hb1, ?_⟩, ?_, ?_⟩
    · rw [FundSetPf.lact_one, IW.cpt_zero]; exact e1
    · rintro _ ⟨y, hy, γ, hγ, b, hb, rfl⟩ γ' hγ' b' hb'
      refine ⟨y, hy, γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
      rw [FundSetPf.lact_mul, ← ExtFPf.rmul_assoc, FundSetPf.lact_rmul γ (rmul _ b)]
    · exact (GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF φ hφm hφi _
        measurableSet_ball hsub).trans_lt hint2
  choose U hUo hUx hUs hUi using hloc
  obtain ⟨K, hK⟩ := Fl.family_le_coords (⋃ j, U j) (isOpen_iUnion hUo) (fun j => Set.mem_iUnion.2 ⟨j, hUx j⟩)
    (fun x hx γ hγ b hb => by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨j, hUs j x hj γ hγ b hb⟩)
  have hmeas : MeasurableSet (FF \ cpt X x0 ⁻¹' ⋃ j, U j) :=
    hF.1.diff ((isOpen_iUnion hUo).preimage (FundSetPf.cont_cpt X x0)).measurableSet
  have hoff : ∫⁻ z in FF \ cpt X x0 ⁻¹' ⋃ j, U j, φ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    set A : ℝ := 2 * |K| ^ ((Xa.T : ℝ) - 1 / 2) with hA
    have hA0 : 0 ≤ A := by positivity
    calc ∫⁻ z in FF \ cpt X x0 ⁻¹' ⋃ j, U j, φ (cpt X x0 z) ∂muF X x0
        ≤ ∫⁻ z in FF \ cpt X x0 ⁻¹' ⋃ j, U j, (ENNReal.ofReal A *
          ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) +
          ENNReal.ofReal (A * C)) ∂muF X x0 := by
          refine setLIntegral_mono' hmeas fun z hz => ?_
          have hx : cpt X x0 z ∈ X.dom := hF.2.1 hz.1
          rw [hφ, phi_of_mem Xa Fl _ _ hx, ← ENNReal.ofReal_mul hA0]
          refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
          rw [pnorm_sq_eq_exp hx (Xa.Fp + Xa.T • Xa.L) (fun x => f x - g x)]
          exact real_bound hT1 (Real.exp_pos _).le (pnorm_sq_eq_exp hx _ f) (pnorm_sq_eq_exp hx _ g)
            (sum_pnorm_pos hx (Xa.w_nz _ hx)) (by positivity) (hK _ hx hz.2) (hC _ hx)
      _ ≤ _ := lintegral_mono_set Set.diff_subset
      _ < ⊤ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            setLIntegral_const]
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top (muF_lt_top hM hfin ho hF)⟩
  have hcov : FF ⊆ (⋃ j, FF ∩ cpt X x0 ⁻¹' U j) ∪ (FF \ cpt X x0 ⁻¹' ⋃ j, U j) := by
    intro z hz
    by_cases h : cpt X x0 z ∈ ⋃ j, U j
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
      exact Or.inl (Set.mem_iUnion.2 ⟨j, hz, hj⟩)
    · exact Or.inr ⟨hz, h⟩
  have hall : ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine ((lintegral_mono_set hcov).trans (lintegral_union_le _ _ _)).trans_lt
      (ENNReal.add_lt_top.2 ⟨(lintegral_iUnion_le _ _).trans_lt ?_, hoff⟩)
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun j _ => hUi j
  have hcongr : (fun z => ENNReal.ofReal (‖f (cpt X x0 z) - g (cpt X x0 z)‖ ^ 2) *
      Wdiv X Xa Fl Xa.T (cpt X x0 z)) =ᵐ[(muF X x0).restrict FF] fun z => φ (cpt X x0 z) := by
    filter_upwards [ae_restrict_mem hF.1, ae_restrict_of_ae (s := FF) (ae_exists_ne Xa Fl ho)] with z hz hs
    exact (phi_eq Xa Fl Xa.T (fun x => f x - g x) (hF.2.1 hz) (hs (hF.2.1 hz))).symm
  exact (lintegral_congr_ae hcongr).trans_lt hall

end GlobalTheory.Up.DivInFFPf
