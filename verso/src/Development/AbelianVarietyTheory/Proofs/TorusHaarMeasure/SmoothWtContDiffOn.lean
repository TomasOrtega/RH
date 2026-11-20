import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegrandAemeasurable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivUpPf

noncomputable section

/- English proof (translation)
Establish `h : ContDiffAt ℝ ∞ (fun y => ∑ k, ‖g k y‖ ^ 2) z`. Simplify using `only [← Complex.normSq_eq_norm_sq]`. Conclude with `ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hg k) hz)`. Conclude with `h.log (sum_normSq_pos hne).ne'`.
-/
theorem logSum_contDiffAt {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖g k y‖ ^ 2)) z := by
  have h : ContDiffAt ℝ ∞ (fun y => ∑ k, ‖g k y‖ ^ 2) z := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hg k) hz)
  exact h.log (sum_normSq_pos hne).ne'

/- English proof (translation)
Take `⟨k, hk⟩` from `hne`. Establish `hne' : (fun i => g i z) ≠ 0` using `fun h => hk (congrFun h k)`. Establish `h` using `leviLogNormSq n N g z ξ (fun i => (HE.contDiffAt_of_punct hU (hg i) hz).of_le HE.two_le_inf) hne'`. Simplify using `only [← Complex.normSq_eq_norm_sq]`. Establish `e : (fun y => ((Real.log (∑ k, Complex.normSq (g k y)) : ℝ) : ℂ)) = fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)` using `rfl`.

Rewrite using `[e, h, Complex.ofReal_re]`. Conclude with `div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)`.
-/
theorem logSum_levi_nonneg {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (∑ k, ‖g k y‖ ^ 2) : ℝ) : ℂ)) z ξ).re := by
  obtain ⟨k, hk⟩ := hne
  have hne' : (fun i => g i z) ≠ 0 := fun h => hk (congrFun h k)
  have h := leviLogNormSq n N g z ξ
    (fun i => (HE.contDiffAt_of_punct hU (hg i) hz).of_le HE.two_le_inf) hne'
  simp only [← Complex.normSq_eq_norm_sq]
  have e : (fun y => ((Real.log (∑ k, Complex.normSq (g k y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) := rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def smoothWt (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ :=
  phla X Xa.Fp (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) + ((-bb) * rhF X x0 z +
    (1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2)))

/- English proof (translation)
The claim follows from `OntoB.hol_comp X x0 (Xa.w_van k).1.1.1.1`.
-/
theorem w_diffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (k : Fin Xa.N) :
    DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Xa.w_van k).1.1.1.1

/- English proof (translation)
The claim follows from `OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1`.
-/
theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k : Fin (nd X)) :
    DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1

/- English proof (translation)
The claim follows from `logSum_contDiffAt (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0) (w_diffOn Xa x0) hz (Xa.w_nz _ hz)`.
-/
theorem logw_contDiffAt (Xa : ArchInM X) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2)) z :=
  logSum_contDiffAt (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz)

/- English proof (translation)
Introduce `_ hz` and use `((IW.phla_cpt_cdAt X x0 hz Xa.Fp).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt`.
-/
theorem smoothWt_contDiffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ) :
    ContDiffOn ℝ ∞ (smoothWt Xa x0 bb) (OmF X x0) := fun _ hz =>
  ((IW.phla_cpt_cdAt X x0 hz Xa.Fp).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add
    ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add
      (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt

/- English proof (translation)
Establish `h1` using `(IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le HE.two_le_inf`. Establish `h2` using `(OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf`. Establish `h3` using `(OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf`. Establish `h4` using `(logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf`. Establish `h5` using `logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0) (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ`.

Unfold `smoothWt`. Rewrite using `[Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))), Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)), Y.Lo …`. Simplify using `only [Complex.add_re, Complex.re_ofReal_mul]`. Unfold `leviRh leviO leviM leviDens at hm`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem smoothWt_levi (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ)
    (hm : bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) :
    0 ≤ (leviV (nd X) (fun w => ((smoothWt Xa x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le HE.two_le_inf
  have h2 := (OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf
  have h3 := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  have h4 := (logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf
  have h5 := logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ
  unfold smoothWt
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2)
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (contDiffAt_const.mul h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hm
  linarith

/- English proof (translation)
Establish `hU` using `OntoB.isOpen_OmF X x0`. Establish `hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0))` using `(OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal`. Unfold `InAt muF`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Use `iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))` and prove the remaining obligations.

Establish `hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0`. Rewrite using `[ae_iff]`. Use `measure_mono_null (fun z hz => ?_) hnull` and prove the remaining obligations. Simplify using `using hz`. Use `filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'`.

Establish `hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0` using `⟨k0, hz' hz⟩`. Establish `hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2` using `sum_normSq_pos hs`. Establish `hdp` using `OntoB.densF_pos hz`. Establish `hka : 0 < kaF X x0 bb z` using `Real.exp_pos _`. Simplify using `only [Pi.mul_apply]`.

Rewrite using `[Wdiv_eq_exp Xa Fl m hz hs, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hdp.le]`. Use `congr 1`. Rewrite using `[Real.rpow_def_of_pos hsp, kaF, div_eq_mul_inv, ← Real.exp_neg]`. Use `conv_lhs => rw [← Real.exp_log hdp]`. Rewrite using `[mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]`.

Use `congr 2`. Unfold `Psdiv smoothWt`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inAt_iff (Xa : ArchInM X) (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (bb : ℝ) (m : ℕ)
    (k0 : Fin (nd X)) (hnull : volume {y | y ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 y) = 0} = 0)
    (F : V (nd X) → ℂ) :
    InAt X x0 (Wdiv X Xa Fl m) bb F ↔
      ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-((m : ℝ) - 1 / 2)) *
        Real.exp (-smoothWt Xa x0 bb z)) < ⊤ := by
  have hU := OntoB.isOpen_OmF X x0
  have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
  unfold InAt muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))
  have hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    simpa using hz
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'
  have hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := ⟨k0, hz' hz⟩
  have hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := sum_normSq_pos hs
  have hdp := OntoB.densF_pos hz
  have hka : 0 < kaF X x0 bb z := Real.exp_pos _
  simp only [Pi.mul_apply]
  rw [Wdiv_eq_exp Xa Fl m hz hs, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hdp.le]
  congr 1
  rw [Real.rpow_def_of_pos hsp, kaF, div_eq_mul_inv, ← Real.exp_neg]
  conv_lhs => rw [← Real.exp_log hdp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  unfold Psdiv smoothWt
  ring

end

end GlobalTheory.Up.DivUpPf

namespace GlobalTheory.Up

open DivUpPf

/- English proof (translation)
Introduce `r X Xa Fl x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI`. Establish `hU` using `OntoB.isOpen_OmF X x0`. Establish `hc` using `OmFConnStatement_holds r X x0 ho`. Establish `hnull` using `HE.zeros_null hU (s_diffOn Fl x0 k0) (HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds))`. Take `⟨S, hS, -⟩` from `exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)`.

Establish `hT : nd X ≤ Xa.T`. Establish `h2` using `Xa.n_ge`. Establish `hT` using `Xa.T_ge`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcast : ((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) = (Xa.T : ℝ)`.

Rewrite using `[Nat.cast_sub hT]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hI` using `[inAt_iff Xa Fl x0 bb _ k0 hnull, ← hcast]`. Take `⟨H, hH, hFH⟩` from `SkodaIter.iterated_division (nd X) Xa.n_ge (OmF X x0) hU hc (fun k z => Fl.s k (cpt X x0 z)) k0 (s_diffOn Fl x0) ⟨z0, hz0, hz0'⟩ ⟨S, hS⟩ (smoothWt Xa x0 bb) (smoothWt_contDiffOn Xa x0 bb) (fun z hz ξ => smoothWt_levi Xa x0 bb hz ξ (hm z hz ξ)) (Xa.T - nd X) F hF hI`. Conclude with `⟨H, fun α => ⟨(hH α).1, (inAt_iff Xa Fl x0 bb _ k0 hnull _).2 (hH α).2⟩, hFH⟩`.
-/
theorem divUp_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : DivUp (E := E) := by
  intro r X Xa Fl x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI
  have hU := OntoB.isOpen_OmF X x0
  have hc := OmFConnStatement_holds r X x0 ho
  have hnull := HE.zeros_null hU (s_diffOn Fl x0 k0)
    (HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds))
  obtain ⟨S, hS, -⟩ := exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)
  have hT : nd X ≤ Xa.T := by
    have h2 := Xa.n_ge
    have hT := Xa.T_ge
    nlinarith
  have hcast : ((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) = (Xa.T : ℝ) := by
    rw [Nat.cast_sub hT]; ring
  rw [inAt_iff Xa Fl x0 bb _ k0 hnull, ← hcast] at hI
  obtain ⟨H, hH, hFH⟩ := SkodaIter.iterated_division (nd X) Xa.n_ge (OmF X x0) hU hc
    (fun k z => Fl.s k (cpt X x0 z)) k0 (s_diffOn Fl x0) ⟨z0, hz0, hz0'⟩ ⟨S, hS⟩
    (smoothWt Xa x0 bb) (smoothWt_contDiffOn Xa x0 bb)
    (fun z hz ξ => smoothWt_levi Xa x0 bb hz ξ (hm z hz ξ)) (Xa.T - nd X) F hF hI
  exact ⟨H, fun α => ⟨(hH α).1, (inAt_iff Xa Fl x0 bb _ k0 hnull _).2 (hH α).2⟩, hFH⟩

end GlobalTheory.Up
