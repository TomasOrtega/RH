import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex UnitAddTorus Topology

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def tof_torMk (d : ℕ) : (Fin d → ℝ) → UnitAddTorus (Fin d) := fun x i => (x i : UnitAddCircle)

/- English proof (translation)
Establish `hc : Continuous (tof_torMk d)`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `show Continuous fun x : Fin d → ℝ => ((x i : ℝ) : UnitAddCircle)`. Use `first`. Consider the case `exact continuous_quotient_mk'.comp (continuous_apply i)`.

Consider the case `exact (AddCircle.continuous_mk' 1).comp (continuous_apply i)`. Consider the case `fun_prop`. Consider the case `continuity`. Establish `hsurj : Function.Surjective (tof_torMk d)`. Introduce `t`.

Use `choose x hx using fun i => QuotientAddGroup.mk_surjective (t i)`. Conclude with `⟨x, funext hx⟩`. Establish `ho : IsOpenMap (tof_torMk d)` using `by first`. Consider the case `exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)`. Consider the case `exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe _)`.

Consider the case `exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe) (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)`. Use `first`. Consider the case `exact ho.isQuotientMap hc hsurj`. Consider the case `exact IsOpenQuotientMap.isQuotientMap ⟨hsurj, hc, ho⟩`.
-/
theorem tof_torMk_isQuotientMap (d : ℕ) : IsQuotientMap (tof_torMk d) := by
  have hc : Continuous (tof_torMk d) := by
    refine continuous_pi fun i => ?_
    show Continuous fun x : Fin d → ℝ => ((x i : ℝ) : UnitAddCircle)
    first
    | exact continuous_quotient_mk'.comp (continuous_apply i)
    | exact (AddCircle.continuous_mk' 1).comp (continuous_apply i)
    | fun_prop
    | continuity
  have hsurj : Function.Surjective (tof_torMk d) := by
    intro t
    choose x hx using fun i => QuotientAddGroup.mk_surjective (t i)
    exact ⟨x, funext hx⟩
  have ho : IsOpenMap (tof_torMk d) := by
    first
    | exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
    | exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe _)
    | exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
        (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  first
  | exact ho.isQuotientMap hc hsurj
  | exact IsOpenQuotientMap.isQuotientMap ⟨hsurj, hc, ho⟩

def tof_torMkC (d : ℕ) : C((Fin d → ℝ), UnitAddTorus (Fin d)) :=
  ⟨tof_torMk d, (tof_torMk_isQuotientMap d).continuous⟩

/- English proof (translation)
Conclude with `tof_torMk_isQuotientMap d`.
-/
theorem tof_torMkC_isQuotientMap (d : ℕ) : IsQuotientMap (tof_torMkC d) := by
  exact tof_torMk_isQuotientMap d

/- English proof (translation)
Establish `key : ∀ i, ∃ k : ℤ, b i = a i + k`. Introduce `i`. Establish `hi : ((a i : ℝ) : UnitAddCircle) = ((b i : ℝ) : UnitAddCircle)` using `congrFun h i`. Establish `h0 : ((b i - a i : ℝ) : UnitAddCircle) = 0` using `by first`. Consider the case `rw [QuotientAddGroup.mk_sub, hi, sub_self]`.

Consider the case `rw [AddCircle.coe_sub, hi, sub_self]`. Consider the case `simp [hi]`. Take `⟨k, hk⟩ : ∃ k : ℤ, k • (1 : ℝ) = b i - a i` from `by first`. Consider the case `exact (AddCircle.coe_eq_zero_iff 1).mp h0`. Consider the case `exact AddCircle.coe_eq_zero_iff.mp h0`.

Consider the case `exact AddSubgroup.mem_zmultiples_iff.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [zsmul_eq_mul, mul_one] at hk`. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose n hn using key`.

Conclude with `⟨n, funext fun i => hn i⟩`.
-/
theorem tof_torMk_eq {d : ℕ} {a b : Fin d → ℝ} (h : tof_torMk d a = tof_torMk d b) :
    ∃ n : Fin d → ℤ, b = a + fun i => (n i : ℝ) := by
  have key : ∀ i, ∃ k : ℤ, b i = a i + k := by
    intro i
    have hi : ((a i : ℝ) : UnitAddCircle) = ((b i : ℝ) : UnitAddCircle) := congrFun h i
    have h0 : ((b i - a i : ℝ) : UnitAddCircle) = 0 := by
      first
      | rw [QuotientAddGroup.mk_sub, hi, sub_self]
      | rw [AddCircle.coe_sub, hi, sub_self]
      | simp [hi]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k • (1 : ℝ) = b i - a i := by
      first
      | exact (AddCircle.coe_eq_zero_iff 1).mp h0
      | exact AddCircle.coe_eq_zero_iff.mp h0
      | exact AddSubgroup.mem_zmultiples_iff.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using key
  exact ⟨n, funext fun i => hn i⟩

/- English proof (translation)
Introduce `a b h`. Take `⟨n, rfl⟩` from `tof_torMk_eq (a := a) (b := b) h`. Conclude with `(hper a n).symm`.
-/
theorem tof_torMk_factors {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x) :
    Function.FactorsThrough (⟨F, hF⟩ : C((Fin d → ℝ), ℂ)) (tof_torMkC d) := by
  intro a b h
  obtain ⟨n, rfl⟩ := tof_torMk_eq (a := a) (b := b) h
  exact (hper a n).symm

def tof_torLift {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x) :
    C(UnitAddTorus (Fin d), ℂ) :=
  (tof_torMkC_isQuotientMap d).lift ⟨F, hF⟩ (tof_torMk_factors F hF hper)

/- English proof (translation)
Use `first`. Consider the case `exact ContinuousMap.congr_fun ((tof_torMkC_isQuotientMap d).lift_comp ⟨F, hF⟩ (tof_torMk_factors F hF hper)) y`. Consider the case `exact ContinuousMap.congr_fun ((tof_torMkC_isQuotientMap d).lift_comp (g := ⟨F, hF⟩) (h := tof_torMk_factors F hF hper)) y`. Consider the case `simp [tof_torLift]`.
-/
theorem tof_torLift_mk {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x)
    (y : Fin d → ℝ) : tof_torLift F hF hper (tof_torMk d y) = F y := by
  first
  | exact ContinuousMap.congr_fun
      ((tof_torMkC_isQuotientMap d).lift_comp ⟨F, hF⟩ (tof_torMk_factors F hF hper)) y
  | exact ContinuousMap.congr_fun
      ((tof_torMkC_isQuotientMap d).lift_comp (g := ⟨F, hF⟩) (h := tof_torMk_factors F hF hper)) y
  | simp [tof_torLift]

/- English proof (translation)
Use `first`. Consider the case `(simp only [Set.setOf_forall]`. Conclude with `MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioc)`. Consider the case `measurability`.
-/
theorem tof_box_measurable (d : ℕ) : MeasurableSet {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} := by
  first
  | (simp only [Set.setOf_forall]
     exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioc)
  | measurability

/- English proof (translation)
Apply the tactic sequence `have e : mFourier n (tof_torMk d y) = ∏ i, fourier (n i) ((y i : ℝ) : UnitAddCircle) := by first | rfl | simp [mFourier, tof_torMk]`. Rewrite using `[e]`. Simplify using `only [fourier_coe_apply, Complex.ofReal_one, div_one]`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tof_mFourier_torMk {d : ℕ} (n : Fin d → ℤ) (y : Fin d → ℝ) :
    mFourier n (tof_torMk d y) = cexp (2 * Real.pi * I * ∑ i, (n i : ℂ) * y i) := by
  have e : mFourier n (tof_torMk d y) = ∏ i, fourier (n i) ((y i : ℝ) : UnitAddCircle) := by
    first | rfl | simp [mFourier, tof_torMk]
  rw [e]
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  ring

/- English proof (translation)
Establish `h` using `AddCircle.measurePreserving_mk (1 : ℝ) 0`. Rewrite `h` using `[zero_add]`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals (try (rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]))`. Apply the tactic sequence `all_goals (try rfl)`.
-/
private theorem measurePreserving_coe_unitAddCircle_restrict_Ioc :
    MeasurePreserving (fun x : ℝ => (x : UnitAddCircle)) (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (volume : Measure UnitAddCircle) := by
  have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [zero_add] at h
  convert h using 1
  all_goals (try (rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]))
  all_goals (try rfl)

/- English proof (translation)
Establish `hbox : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hbox, show (volume : Measure (Fin d → ℝ)) = Measure.pi (fun _ => volume) from rfl, Measure.restrict_pi_pi]`. Use `first`.

Consider the case `exact measurePreserving_pi _ _ (fun _ => measurePreserving_coe_unitAddCircle_restrict_Ioc)`. Consider the case `exact measurePreserving_pi (fun _ => measurePreserving_coe_unitAddCircle_restrict_Ioc)`.
-/
private theorem measurePreserving_torMk_restrict_Ioc (d : ℕ) :
    MeasurePreserving (tof_torMk d)
      ((volume : Measure (Fin d → ℝ)).restrict {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1})
      (volume : Measure (UnitAddTorus (Fin d))) := by
  have hbox : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
      Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp
  rw [hbox, show (volume : Measure (Fin d → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  first
  | exact measurePreserving_pi _ _ (fun _ => measurePreserving_coe_unitAddCircle_restrict_Ioc)
  | exact measurePreserving_pi (fun _ => measurePreserving_coe_unitAddCircle_restrict_Ioc)

/- English proof (translation)
Establish `hmp` using `measurePreserving_torMk_restrict_Ioc d`. Rewrite using `[← hmp.map_eq, integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable]`.
-/
private theorem integral_torus_eq_setIntegral_Ioc_torMk {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] (g : UnitAddTorus (Fin d) → E) (hg : Continuous g) :
    ∫ t, g t = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, g (tof_torMk d x) := by
  have hmp := measurePreserving_torMk_restrict_Ioc d
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable]

/- English proof (translation)
Establish `key : ∀ x ∈ {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, mFourier (-n) (tof_torMk d x) • f (tof_torMk d x) = cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x`. Introduce `x _`. Rewrite using `[hfx, tof_mFourier_torMk, smul_eq_mul]`. Use `congr 2`. Use `first`.

Consider the case `simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]`. Consider the case `(simp [Finset.sum_neg_distrib]; ring)`. Establish `e : mFourierCoeff f n = ∫ t, mFourier (-n) t • f t` using `rfl`. Rewrite using `[e]`. Use `(integral_torus_eq_setIntegral_Ioc_torMk (fun t => mFourier (-n) t • f t) ((mFourier (-n)).continuous.smul f.continuous)).trans ?_` and prove the remaining obligations.

Use `first`. Consider the case `exact setIntegral_congr_fun (tof_box_measurable d) key`. Consider the case `exact setIntegral_congr (tof_box_measurable d) key`. Consider the case `exact setIntegral_congr_fun₀ (tof_box_measurable d).nullMeasurableSet key`.
-/
theorem tof_coeff_eq {d : ℕ} (f : C(UnitAddTorus (Fin d), ℂ)) (F : (Fin d → ℝ) → ℂ)
    (hfx : ∀ y, f (tof_torMk d y) = F y) (n : Fin d → ℤ) :
    mFourierCoeff f n = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x := by
  have key : ∀ x ∈ {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      mFourier (-n) (tof_torMk d x) • f (tof_torMk d x) =
        cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x := by
    intro x _
    rw [hfx, tof_mFourier_torMk, smul_eq_mul]
    congr 2
    first
    | simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
    | (simp [Finset.sum_neg_distrib]; ring)
  have e : mFourierCoeff f n = ∫ t, mFourier (-n) t • f t := rfl
  rw [e]
  refine (integral_torus_eq_setIntegral_Ioc_torMk (fun t => mFourier (-n) t • f t)
    ((mFourier (-n)).continuous.smul f.continuous)).trans ?_
  first
  | exact setIntegral_congr_fun (tof_box_measurable d) key
  | exact setIntegral_congr (tof_box_measurable d) key
  | exact setIntegral_congr_fun₀ (tof_box_measurable d).nullMeasurableSet key

/- English proof (translation)
Establish `hae : (ContinuousMap.toLp (E` using `ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] f := by first`. Consider the case `exact ContinuousMap.coeFn_toLp f`. Consider the case `exact ContinuousMap.coeFn_toLp (μ := volume) f`. Consider the case `exact ContinuousMap.coeFn_toLp ℂ f`. Consider the case `exact ContinuousMap.coeFn_toLp _ _ _ f`.

Establish `h` using `hasSum_sq_mFourierCoeff (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f)`. Establish `e1 : ∀ n, mFourierCoeff (ContinuousMap.toLp (E` using `ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f) n = mFourierCoeff f n := by`. Introduce `n`. Use `first`. Consider the case `exact mFourierCoeff_toLp f n`.

Consider the case `exact mFourierCoeff_toLp n`. Consider the case `exact mFourierCoeff_toLp (f := f) n`. Consider the case `simp [mFourierCoeff_toLp]`. Establish `e2 : ∫ t, ‖(ContinuousMap.toLp (E` using `ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f) t‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := integral_congr_ae (hae.mono fun t ht => by simp only [ht])`. Simplify using `only [e1] at h`.

Rewrite `h` using `[e2]`. Conclude with `h`.
-/
private theorem hasSum_norm_sq_mFourierCoeff_eq_integral_norm_sq {d : ℕ} (f : C(UnitAddTorus (Fin d), ℂ)) :
    HasSum (fun n : Fin d → ℤ => ‖mFourierCoeff f n‖ ^ 2) (∫ t, ‖f t‖ ^ 2) := by
  have hae : (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f :
      UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] f := by
    first
    | exact ContinuousMap.coeFn_toLp f
    | exact ContinuousMap.coeFn_toLp (μ := volume) f
    | exact ContinuousMap.coeFn_toLp ℂ f
    | exact ContinuousMap.coeFn_toLp _ _ _ f
  have h := hasSum_sq_mFourierCoeff
    (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f)
  have e1 : ∀ n, mFourierCoeff
      (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f) n =
        mFourierCoeff f n := by
    intro n
    first
    | exact mFourierCoeff_toLp f n
    | exact mFourierCoeff_toLp n
    | exact mFourierCoeff_toLp (f := f) n
    | simp [mFourierCoeff_toLp]
  have e2 : ∫ t, ‖(ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ f) t‖ ^ 2
      = ∫ t, ‖f t‖ ^ 2 :=
    integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  simp only [e1] at h
  rw [e2] at h
  exact h

/- English proof (translation)
Take `⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y` from `⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩`. Establish `hc : ∀ n, mFourierCoeff f n = 0` using `fun n => (tof_coeff_eq f F hfx n).trans (hcoef n)`. Establish `hp` using `hasSum_norm_sq_mFourierCoeff_eq_integral_norm_sq f`. Establish `h0 : HasSum (fun n : Fin d → ℤ => ‖mFourierCoeff f n‖ ^ 2) 0`. Establish `e : (fun n : Fin d → ℤ => ‖mFourierCoeff f n‖ ^ 2) = fun _ => (0 : ℝ)`.

Use function extensionality and compare the values at `n`. Rewrite using `[hc n]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `hasSum_zero`.

Establish `hI : ∫ t, ‖f t‖ ^ 2 = 0` using `hp.unique h0`. Establish `hcont : Continuous (fun t => ‖f t‖ ^ 2)` using `f.continuous.norm.pow 2`. Establish `hint : Integrable (fun t => ‖f t‖ ^ 2) (volume : Measure (UnitAddTorus (Fin d)))` using `by first`. Consider the case `exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ)`. Consider the case `exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Consider the case `exact (ContinuousMap.mk _ hcont).integrable`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg ‖f t‖) hint).mp hI`. Establish `heq : (fun t => ‖f t‖ ^ 2) = (0 : UnitAddTorus (Fin d) → ℝ)` using `by first`. Consider the case `exact (Continuous.ae_eq_iff_eq volume hcont continuous_zero).mp hae`. Consider the case `exact (Continuous.ae_eq_iff_eq hcont continuous_zero).mp hae`.

Establish `h1 : ‖f (tof_torMk d x)‖ ^ 2 = 0` using `congrFun heq (tof_torMk d x)`. Rewrite `h1` using `[hfx]`. Simplify using `using h1`.
-/
theorem tof_torus_unique {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x)
    (hcoef : ∀ n : Fin d → ℤ, ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x = 0) (x : Fin d → ℝ) :
    F x = 0 := by
  obtain ⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y :=
    ⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩
  have hc : ∀ n, mFourierCoeff f n = 0 := fun n => (tof_coeff_eq f F hfx n).trans (hcoef n)
  have hp := hasSum_norm_sq_mFourierCoeff_eq_integral_norm_sq f
  have h0 : HasSum (fun n : Fin d → ℤ => ‖mFourierCoeff f n‖ ^ 2) 0 := by
    have e : (fun n : Fin d → ℤ => ‖mFourierCoeff f n‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext n
      rw [hc n]
      simp
    rw [e]
    exact hasSum_zero
  have hI : ∫ t, ‖f t‖ ^ 2 = 0 := hp.unique h0
  have hcont : Continuous (fun t => ‖f t‖ ^ 2) := f.continuous.norm.pow 2
  have hint : Integrable (fun t => ‖f t‖ ^ 2) (volume : Measure (UnitAddTorus (Fin d))) := by
    first
    | exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ)
    | exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    | exact (ContinuousMap.mk _ hcont).integrable
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg ‖f t‖) hint).mp hI
  have heq : (fun t => ‖f t‖ ^ 2) = (0 : UnitAddTorus (Fin d) → ℝ) := by
    first
    | exact (Continuous.ae_eq_iff_eq volume hcont continuous_zero).mp hae
    | exact (Continuous.ae_eq_iff_eq hcont continuous_zero).mp hae
  have h1 : ‖f (tof_torMk d x)‖ ^ 2 = 0 := congrFun heq (tof_torMk d x)
  rw [hfx] at h1
  simpa using h1

/- English proof (translation)
Take `⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y` from `⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩`. Establish `hadd : ∀ x : Fin d → ℝ, tof_torMk d x + tof_torMk d s = tof_torMk d (x + s)`. Introduce `x`. Use function extensionality and compare the values at `i`. Use `show ((x i : ℝ) : UnitAddCircle) + ((s i : ℝ) : UnitAddCircle) = ((x i + s i : ℝ) : UnitAddCircle)`.

Use `first`. Consider the case `exact (QuotientAddGroup.mk_add _ _).symm`. Consider the case `rfl`. Consider the case `simp`. Establish `e1` using `integral_torus_eq_setIntegral_Ioc_torMk (fun t => f (t + tof_torMk d s)) (f.continuous.comp (continuous_id.add continuous_const))`.

Establish `e2` using `integral_torus_eq_setIntegral_Ioc_torMk (fun t => f t) f.continuous`. Establish `e3 : ∫ t, f (t + tof_torMk d s) = ∫ t, f t` using `by first`. Consider the case `exact integral_add_right_eq_self (fun t => f t) (tof_torMk d s)`. Consider the case `(rw [show (fun t => f (t + tof_torMk d s)) = fun t => f (tof_torMk d s + t) from`. Use function extensionality and compare the values at `fun t => by rw [add_comm]]`.

Conclude with `integral_add_left_eq_self (fun t => f t) (tof_torMk d s))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tof_box_shift {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x)
    (s : Fin d → ℝ) :
    ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, F (x + s) =
      ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, F x := by
  obtain ⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y :=
    ⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩
  have hadd : ∀ x : Fin d → ℝ, tof_torMk d x + tof_torMk d s = tof_torMk d (x + s) := by
    intro x
    funext i
    show ((x i : ℝ) : UnitAddCircle) + ((s i : ℝ) : UnitAddCircle) = ((x i + s i : ℝ) : UnitAddCircle)
    first
    | exact (QuotientAddGroup.mk_add _ _).symm
    | rfl
    | simp
  have e1 := integral_torus_eq_setIntegral_Ioc_torMk (fun t => f (t + tof_torMk d s))
    (f.continuous.comp (continuous_id.add continuous_const))
  have e2 := integral_torus_eq_setIntegral_Ioc_torMk (fun t => f t) f.continuous
  have e3 : ∫ t, f (t + tof_torMk d s) = ∫ t, f t := by
    first
    | exact integral_add_right_eq_self (fun t => f t) (tof_torMk d s)
    | (rw [show (fun t => f (t + tof_torMk d s)) = fun t => f (tof_torMk d s + t) from
          funext fun t => by rw [add_comm]]
       exact integral_add_left_eq_self (fun t => f t) (tof_torMk d s))
  calc ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, F (x + s)
      = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, f (tof_torMk d x + tof_torMk d s) :=
        congrArg (integral _) (funext fun x => by simp only [hadd, hfx])
    _ = ∫ t, f (t + tof_torMk d s) := e1.symm
    _ = ∫ t, f t := e3
    _ = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, f (tof_torMk d x) := e2
    _ = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, F x :=
        congrArg (integral _) (funext fun x => hfx x)

/- English proof (translation)
Take `⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y` from `⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩`. Establish `hc : ∀ n, mFourierCoeff f n = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x` using `fun n => tof_coeff_eq f F hfx n`. Establish `hs : Summable (fun n => mFourierCoeff f n)`. Simplify using `only [hc]`. Conclude with `hsum`.

Establish `hpt : HasSum (fun n => mFourierCoeff f n • mFourier n (tof_torMk d 0)) (f (tof_torMk d 0))` using `by first`. Consider the case `exact hasSum_mFourier_series_apply_of_summable hs (tof_torMk d 0)`. Consider the case `exact ContinuousMap.hasSum_apply (hasSum_mFourier_series_of_summable hs) (tof_torMk d 0)`. Consider the case `exact (hasSum_mFourier_series_of_summable hs).map (ContinuousMap.evalCLM ℂ (tof_torMk d 0)) (ContinuousMap.evalCLM ℂ (tof_torMk d 0)).continuous`. Establish `h1 : ∀ n : Fin d → ℤ, mFourier n (tof_torMk d 0) = 1`.

Introduce `n`. Rewrite using `[tof_mFourier_torMk]`. Simplify using the standard rewrite rules. Simplify using `only [h1, smul_eq_mul, mul_one, hfx, hc] at hpt`. Conclude with `hpt`.
-/
theorem tof_torus_inversion {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x)
    (hsum : Summable fun n : Fin d → ℤ => ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x) :
    HasSum (fun n : Fin d → ℤ => ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x) (F 0) := by
  obtain ⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y :=
    ⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩
  have hc : ∀ n, mFourierCoeff f n = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x := fun n => tof_coeff_eq f F hfx n
  have hs : Summable (fun n => mFourierCoeff f n) := by
    simp only [hc]
    exact hsum
  have hpt : HasSum (fun n => mFourierCoeff f n • mFourier n (tof_torMk d 0)) (f (tof_torMk d 0)) := by
    first
    | exact hasSum_mFourier_series_apply_of_summable hs (tof_torMk d 0)
    | exact ContinuousMap.hasSum_apply (hasSum_mFourier_series_of_summable hs) (tof_torMk d 0)
    | exact (hasSum_mFourier_series_of_summable hs).map (ContinuousMap.evalCLM ℂ (tof_torMk d 0))
        (ContinuousMap.evalCLM ℂ (tof_torMk d 0)).continuous
  have h1 : ∀ n : Fin d → ℤ, mFourier n (tof_torMk d 0) = 1 := by
    intro n
    rw [tof_mFourier_torMk]
    simp
  simp only [h1, smul_eq_mul, mul_one, hfx, hc] at hpt
  exact hpt

/- English proof (translation)
Take `⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y` from `⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩`. Establish `hp` using `hasSum_norm_sq_mFourierCoeff_eq_integral_norm_sq f`. Establish `e2 : ∫ t, ‖f t‖ ^ 2 = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, ‖F x‖ ^ 2` using `(integral_torus_eq_setIntegral_Ioc_torMk (fun t => ‖f t‖ ^ 2) (f.continuous.norm.pow 2)).trans (congrArg (integral _) (funext fun x => by simp only [hfx]))`. Rewrite `hp` using `[e2]`. Simplify `hp` using `only [tof_coeff_eq f F hfx]`.
-/
theorem tof_torus_parseval {d : ℕ} (F : (Fin d → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : Fin d → ℝ) (n : Fin d → ℤ), F (x + fun i => (n i : ℝ)) = F x) :
    HasSum (fun n : Fin d → ℤ => ‖∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      cexp (-(2 * Real.pi * I * ∑ i, (n i : ℂ) * x i)) * F x‖ ^ 2)
      (∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, ‖F x‖ ^ 2) := by
  obtain ⟨f, hfx⟩ : ∃ f : C(UnitAddTorus (Fin d), ℂ), ∀ y, f (tof_torMk d y) = F y :=
    ⟨tof_torLift F hF hper, tof_torLift_mk F hF hper⟩
  have hp := hasSum_norm_sq_mFourierCoeff_eq_integral_norm_sq f
  have e2 : ∫ t, ‖f t‖ ^ 2 = ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, ‖F x‖ ^ 2 :=
    (integral_torus_eq_setIntegral_Ioc_torMk (fun t => ‖f t‖ ^ 2) (f.continuous.norm.pow 2)).trans
      (congrArg (integral _) (funext fun x => by simp only [hfx]))
  rw [e2] at hp
  simpa only [tof_coeff_eq f F hfx] using hp

end

end ReciprocityTheory.ChartRestriction.G.I2
