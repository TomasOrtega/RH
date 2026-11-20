import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd t i)]`. Simplify using `[eMat, Matrix.one_apply, Fin.ext_iff]`. Introduce `b _ hb`. Rewrite using `[Matrix.of_apply, if_neg, zero_mul]`.

Introduce `hh; exact hb (Fin.ext (by simpa using hh))`. Simplify using the standard rewrite rules.
-/
theorem eMat_leftInv (r t : ℕ) :
    (Matrix.of fun (i : Fin r) (j : Fin (r + t)) => if (j : ℕ) = i then (1 : k) else 0) * eMat k r t = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd t i)]
  · simp [eMat, Matrix.one_apply, Fin.ext_iff]
  · intro b _ hb
    rw [Matrix.of_apply, if_neg, zero_mul]
    intro hh; exact hb (Fin.ext (by simpa using hh))
  · simp

/- English proof (translation)
Use `set χ : GL n k →* ℂˣ := μ.comp GeneralLinearGroup.det with hχd`. Establish `hχ : IsOpen (χ.ker : Set (GL n k))` using `hμ.preimage GeneralLinearGroup.continuous_det`. Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_` and prove the remaining obligations. Establish `hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL n k)) ∈ nhds g0` using `(hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)`. Use `filter_upwards [hn] with g hg`.

Establish `hg' : χ (g0⁻¹ * g) = 1` using `hg`. Establish `e : χ g = χ g0`. Use `congrArg (χ g0 * ·) hg'` as an intermediate fact. Simplify using `only [← map_mul, mul_inv_cancel_left, mul_one] at this`. Conclude with `this`.

Conclude with `congrArg (fun u : ℂˣ => (u : ℂ)) e`.
-/
theorem isLocallyConstant_char_det {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) :
    IsLocallyConstant fun g : GL n k => ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  set χ : GL n k →* ℂˣ := μ.comp GeneralLinearGroup.det with hχd
  have hχ : IsOpen (χ.ker : Set (GL n k)) := hμ.preimage GeneralLinearGroup.continuous_det
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL n k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν _ r t μ hrt hμs hμu h Φ hΦ`. Establish `hu : ∀ x : kˣ, ‖((μ x : ℂˣ) : ℂ)‖ = 1` using `hμu`. Use `set Φ' : Matrix (Fin r) (Fin r) k → ℂ := fun x => Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x) with hΦ'`. Use `set P : Matrix (Fin r) (Fin (r + t)) k := Matrix.of fun i j => if (j : ℕ) = i then 1 else 0 with hP`. Take `⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ` from `hΦ`.

Establish `hcont : Continuous fun x : Matrix (Fin r) (Fin r) k => (h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x` using `continuous_const.matrix_mul continuous_id`. Establish `hl' : IsLocallyConstant Φ'` using `hl.comp_continuous hcont`. Establish `hK' : HasCompactSupport Φ'`. Use `HasCompactSupport.intro (hK.image (f := fun y => P * h.val * y) (continuous_const.matrix_mul continuous_id)) fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Apply `hx` to reduce the goal to its premises. Use `⟨_, subset_tsupport _ h0, ?_⟩` and prove the remaining obligations. Use `show P * h.val * ((h⁻¹ : GL _ k).val * eMat k r t * x) = x`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc P, Units.mul_inv, Matrix.mul_one, hP, eMat_leftInv, Matrix.one_mul]`.

Take `⟨B, hB⟩` from `GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hK' (f := fun x : Matrix (Fin r) (Fin r) k => x.det) continuous_id.matrix_det)`. Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Establish `: BorelSpace (Matrix (Fin r) (Fin r) k)` using `inferInstanceAs (BorelSpace (Fin r → Fin r → k))`. Establish `: (volM ν (Fin r) (Fin r)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`.

Establish `: BorelSpace (GL (Fin r) k)` using `SplitFlip.borel_GL`. Establish `: SecondCountableTopology (GL (Fin r) k)` using `SplitFlip.secondCountable_GL`. Establish `hE` using `GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) (Fin r)`. Establish `hd` using `continuous_density_volGL (k := k) (n := Fin r)`. Establish `hn : IsLocallyConstant fun g : GL (Fin r) k => nabs k (GeneralLinearGroup.det g)` using `(isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det`.

Establish `hI : Integrable (fun g : GL (Fin r) k => Φ' g.val) ((volM ν (Fin r) (Fin r)).comap fun g : GL (Fin r) k => g.val)`. Establish `h1 : Integrable Φ' (volM ν (Fin r) (Fin r))` using `hl'.continuous.integrable_of_hasCompactSupport hK'`. Use `(hE.integrable_map_iff (g := Φ')).1 ?_` and prove the remaining obligations. Rewrite using `[hE.map_comap]`. Conclude with `h1.restrict`.

Establish `hloc : IsLocallyConstant fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)`. Unfold `om`. Use `((((isLocallyConstant_char_det hμs).mul (IsLocallyConstant.const _)).mul (hn.comp fun a => ((a ^ ((Fintype.card (Fin (r + t)) : ℝ) / 2) : ℝ) : ℂ))).mul (IsLocallyConstant.const _)).mul ?_` and prove the remaining obligations. Conclude with `hl'.comp_continuous Units.continuous_val`. Use `set c : ℝ := nabs k (GeneralLinearGroup.det h) ^ (-(Fintype.card (Fin r) : ℝ) / 2) with hc`.

Unfold `volGL`. Rewrite using `[integrable_withDensity_iff_integrable_smul' hd.measurable (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Use `(hI.norm.mul_const (c * B ^ (((t : ℝ) - r) / 2))).mono' (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hloc.continuous.aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `hp` using `nabs_pos' k (GeneralLinearGroup.det g)`. Establish `hq` using `nabs_pos' k (GeneralLinearGroup.det h)`.

Distinguish the cases in `h0 : Φ' g.val = 0`. Establish `: om μ g h Φ (eMat k r t) = 0`. Simplify using `only [om]`. Rewrite using `[show Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val) = 0 from h0, mul_zero]`. Simplify using `[this, h0]`.

Establish `h1 : nabs k (GeneralLinearGroup.det g) ≤ B` using `hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩`. Use `set a := nabs k (GeneralLinearGroup.det g) with ha`. Establish `e1 : ‖om μ g h Φ (eMat k r t)‖ = a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖`. Simplify using `only [om, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), Fintype.card_fin, Nat.cast_add, hc, ha, hΦ']`. Rewrite using `[Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k _).le _)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), e1, Fintype.card_fin]`. Establish `hc0 : 0 ≤ c` using `Real.rpow_nonneg hq.le _`. Establish `h2 : a ^ (((t : ℝ) - r) / 2) ≤ B ^ (((t : ℝ) - r) / 2)` using `Real.rpow_le_rpow hp.le h1 (div_nonneg (sub_nonneg.2 (by exact_mod_cast hrt)) (by norm_num))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show ((t : ℝ) - r) / 2 = -(r : ℝ) + ((r : ℝ) + t) / 2 by ring, Real.rpow_add hp]; ring`. Use `_ ≤ ‖Φ' g.val‖ * (c * B ^ (((t : ℝ) - r) / 2)) := by gcongr`.
-/
theorem integrable_om_eMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by
  intro k _ _ _ _ _ _ ν _ r t μ hrt hμs hμu h Φ hΦ
  have hu : ∀ x : kˣ, ‖((μ x : ℂˣ) : ℂ)‖ = 1 := hμu
  set Φ' : Matrix (Fin r) (Fin r) k → ℂ := fun x => Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x)
    with hΦ'
  set P : Matrix (Fin r) (Fin (r + t)) k := Matrix.of fun i j => if (j : ℕ) = i then 1 else 0 with hP
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hcont : Continuous fun x : Matrix (Fin r) (Fin r) k =>
      (h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x :=
    continuous_const.matrix_mul continuous_id
  have hl' : IsLocallyConstant Φ' := hl.comp_continuous hcont
  have hK' : HasCompactSupport Φ' := by
    refine HasCompactSupport.intro (hK.image (f := fun y => P * h.val * y)
      (continuous_const.matrix_mul continuous_id)) fun x hx => ?_
    by_contra h0
    apply hx
    refine ⟨_, subset_tsupport _ h0, ?_⟩
    show P * h.val * ((h⁻¹ : GL _ k).val * eMat k r t * x) = x
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc P, Units.mul_inv, Matrix.mul_one, hP, eMat_leftInv, Matrix.one_mul]
  obtain ⟨B, hB⟩ := GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hK'
    (f := fun x : Matrix (Fin r) (Fin r) k => x.det) continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix (Fin r) (Fin r) k) := inferInstanceAs (BorelSpace (Fin r → Fin r → k))
  have : (volM ν (Fin r) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL (Fin r) k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL (Fin r) k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) (Fin r)
  have hd := continuous_density_volGL (k := k) (n := Fin r)
  have hn : IsLocallyConstant fun g : GL (Fin r) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL (Fin r) k => Φ' g.val)
      ((volM ν (Fin r) (Fin r)).comap fun g : GL (Fin r) k => g.val) := by
    have h1 : Integrable Φ' (volM ν (Fin r) (Fin r)) := hl'.continuous.integrable_of_hasCompactSupport hK'
    refine (hE.integrable_map_iff (g := Φ')).1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  have hloc : IsLocallyConstant fun g : GL (Fin r) k => om μ g h Φ (eMat k r t) := by
    unfold om
    refine ((((isLocallyConstant_char_det hμs).mul (IsLocallyConstant.const _)).mul
      (hn.comp fun a => ((a ^ ((Fintype.card (Fin (r + t)) : ℝ) / 2) : ℝ) : ℂ))).mul
      (IsLocallyConstant.const _)).mul ?_
    exact hl'.comp_continuous Units.continuous_val
  set c : ℝ := nabs k (GeneralLinearGroup.det h) ^ (-(Fintype.card (Fin r) : ℝ) / 2) with hc
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (c * B ^ (((t : ℝ) - r) / 2))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hloc.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  have hq := nabs_pos' k (GeneralLinearGroup.det h)
  by_cases h0 : Φ' g.val = 0
  · have : om μ g h Φ (eMat k r t) = 0 := by
      simp only [om]
      rw [show Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val) = 0 from h0, mul_zero]
    simp [this, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  set a := nabs k (GeneralLinearGroup.det g) with ha
  have e1 : ‖om μ g h Φ (eMat k r t)‖ = a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖ := by
    simp only [om, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hq.le _),
      Fintype.card_fin, Nat.cast_add, hc, ha, hΦ']
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k _).le _)]
    ring
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _),
    e1, Fintype.card_fin]
  have hc0 : 0 ≤ c := Real.rpow_nonneg hq.le _
  have h2 : a ^ (((t : ℝ) - r) / 2) ≤ B ^ (((t : ℝ) - r) / 2) :=
    Real.rpow_le_rpow hp.le h1 (div_nonneg (sub_nonneg.2 (by exact_mod_cast hrt)) (by norm_num))
  calc a ^ (-(r : ℝ)) * (a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖)
      = ‖Φ' g.val‖ * (c * a ^ (((t : ℝ) - r) / 2)) := by
        rw [show ((t : ℝ) - r) / 2 = -(r : ℝ) + ((r : ℝ) + t) / 2 by ring, Real.rpow_add hp]; ring
    _ ≤ ‖Φ' g.val‖ * (c * B ^ (((t : ℝ) - r) / 2)) := by gcongr
end GlobalTheory.GodementJacquet
