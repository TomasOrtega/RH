import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GaugeSplittingAlgebra

noncomputable section
open MeasureTheory Module
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2

instance xpBorel (p m : ℕ) : BorelSpace (Xp p m) := by
  have : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace
  have : BorelSpace ((Fin p → ℂ) × (Fin m → ℂ) × ℝ) := Prod.borelSpace
  exact Prod.borelSpace

instance xpHaar (p m : ℕ) : (volume : Measure (Xp p m)).IsAddHaarMeasure := by
  have : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure ((Fin p → ℂ) × (Fin m → ℂ) × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/- English proof (translation)
Establish `hdet : LinearMap.det (t • LinearMap.id : E →ₗ[ℝ] E) = t ^ finrank ℝ E`. Rewrite using `[LinearMap.det_smul, LinearMap.det_id, mul_one]`. Establish `hne : LinearMap.det (t • LinearMap.id : E →ₗ[ℝ] E) ≠ 0`. Rewrite using `[hdet]`. Conclude with `pow_ne_zero _ ht`.

Establish `hmap` using `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar μ hne`. Establish `hf' : (fun x => f (t • x)) = fun x => f ((t • LinearMap.id : E →ₗ[ℝ] E) x)` using `rfl`. Rewrite using `[hf', ← MeasureTheory.lintegral_map hf (LinearMap.continuous_of_finiteDimensional _).measurable, hmap, MeasureTheory.lintegral_smul_measure, hdet, smul_eq_mul]`.
-/
lemma lint_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ} (ht : t ≠ 0) :
    ∫⁻ x, f (t • x) ∂μ = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ x, f x ∂μ := by
  have hdet : LinearMap.det (t • LinearMap.id : E →ₗ[ℝ] E) = t ^ finrank ℝ E := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hne : LinearMap.det (t • LinearMap.id : E →ₗ[ℝ] E) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ ht
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar μ hne
  have hf' : (fun x => f (t • x)) = fun x => f ((t • LinearMap.id : E →ₗ[ℝ] E) x) := rfl
  rw [hf', ← MeasureTheory.lintegral_map hf (LinearMap.continuous_of_finiteDimensional _).measurable, hmap,
    MeasureTheory.lintegral_smul_measure, hdet, smul_eq_mul]

def kc (s : ℝ) : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-s / 2))

/- English proof (translation)
Unfold `kc`. Establish `hi` using `integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := (volume : Measure ℂ)) (r := s) (by rw [Complex.finrank_real_complex]; exact_mod_cast hs)`. Conclude with `hi.lintegral_lt_top`.
-/
lemma kc_lt_top {s : ℝ} (hs : 2 < s) : kc s < ∞ := by
  unfold kc
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := (volume : Measure ℂ)) (r := s)
    (by rw [Complex.finrank_real_complex]; exact_mod_cast hs)
  exact hi.lintegral_lt_top

/- English proof (translation)
Establish `h1 : ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2)) = ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2))`. Rewrite using `[← MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℂ)) (fun w : ℂ => ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2))) c]`. Simplify using `only [add_sub_cancel_right]`. Rewrite using `[h1]`. Take `⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (D / Q)` from `⟨_, rfl⟩`.

Establish `htpos : 0 < t`. Rewrite using `[ht]`. Conclude with `Real.sqrt_pos.mpr (div_pos hD hQ)`. Establish `ht2 : t ^ 2 = D / Q`. Rewrite using `[ht]`.

Conclude with `Real.sq_sqrt (div_pos hD hQ).le`. Establish `hmeas : Measurable (fun w : ℂ => ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2)))` using `by first`. Consider the case `fun_prop`. Consider the case `measurability`. Establish `hmeas2 : Measurable (fun w : ℂ => ENNReal.ofReal ((1 + ‖w‖ ^ 2) ^ (-s / 2)))` using `by first`.

Consider the case `fun_prop`. Consider the case `measurability`. Establish `h2` using `lint_smul (volume : Measure ℂ) hmeas htpos.ne'`. Use `beta_reduce at h2`. Rewrite `h2` using `[Complex.finrank_real_complex]`.

Establish `h3 : ∀ z : ℂ, ENNReal.ofReal ((Q * ‖t • z‖ ^ 2 + D) ^ (-s / 2)) = ENNReal.ofReal (D ^ (-s / 2)) * ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-s / 2))`. Introduce `z`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos htpos, mul_pow, ht2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]`. Use `congr 1`. Rewrite using `[← Real.mul_rpow hD.le (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Rewrite `h2` using `[MeasureTheory.lintegral_const_mul _ hmeas2]`.

Establish `hinv : 0 < (t ^ 2)⁻¹` using `inv_pos.mpr (pow_pos htpos 2)`. Establish `h4 : ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2)) = ENNReal.ofReal (t ^ 2) * (ENNReal.ofReal (D ^ (-s / 2)) * kc s)`. Unfold `kc`. Rewrite using `[h2, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg htpos.le 2), abs_of_pos hinv, mul_inv_cancel₀ (pow_pos htpos 2).ne', ENNReal.ofReal_one, one_mul]`. Rewrite using `[h4, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg htpos.le 2), ht2]`.

Use `congr 2`. Rewrite using `[show (1 : ℝ) - s / 2 = 1 + (-s / 2) by ring, Real.rpow_add hD, Real.rpow_one, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma kernel (Q D : ℝ) (hQ : 0 < Q) (hD : 0 < D) (c : ℂ) (s : ℝ) :
    ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (Q⁻¹ * D ^ (1 - s / 2)) * kc s := by
  have h1 : ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2)) =
      ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2)) := by
    rw [← MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun w : ℂ => ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2))) c]
    simp only [add_sub_cancel_right]
  rw [h1]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (D / Q) := ⟨_, rfl⟩
  have htpos : 0 < t := by
    rw [ht]
    exact Real.sqrt_pos.mpr (div_pos hD hQ)
  have ht2 : t ^ 2 = D / Q := by
    rw [ht]
    exact Real.sq_sqrt (div_pos hD hQ).le
  have hmeas : Measurable (fun w : ℂ => ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2))) := by
    first
    | fun_prop
    | measurability
  have hmeas2 : Measurable (fun w : ℂ => ENNReal.ofReal ((1 + ‖w‖ ^ 2) ^ (-s / 2))) := by
    first
    | fun_prop
    | measurability
  have h2 := lint_smul (volume : Measure ℂ) hmeas htpos.ne'
  beta_reduce at h2
  rw [Complex.finrank_real_complex] at h2
  have h3 : ∀ z : ℂ, ENNReal.ofReal ((Q * ‖t • z‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (D ^ (-s / 2)) * ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-s / 2)) := by
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, mul_pow, ht2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    congr 1
    rw [← Real.mul_rpow hD.le (by positivity)]
    congr 1
    field_simp
    ring
  simp_rw [h3] at h2
  rw [MeasureTheory.lintegral_const_mul _ hmeas2] at h2
  have hinv : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (pow_pos htpos 2)
  have h4 : ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (t ^ 2) * (ENNReal.ofReal (D ^ (-s / 2)) * kc s) := by
    unfold kc
    rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg htpos.le 2), abs_of_pos hinv,
      mul_inv_cancel₀ (pow_pos htpos 2).ne', ENNReal.ofReal_one, one_mul]
  rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg htpos.le 2), ht2]
  congr 2
  rw [show (1 : ℝ) - s / 2 = 1 + (-s / 2) by ring, Real.rpow_add hD, Real.rpow_one, div_eq_mul_inv]
  ring

/- English proof (translation)
Rewrite using `[MeasurableEquiv.piFinSuccAbove_symm_apply]`. Use `first`. Consider the case `exact Fin.insertNth_zero' q.1 q.2`. Consider the case `simp [Fin.insertNthEquiv, Fin.insertNth_zero']`. Consider the case `rfl`.
-/
lemma cons_symm {p : ℕ} (q : ℂ × (Fin p → ℂ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm q = Fin.cons q.1 q.2 := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  first
  | exact Fin.insertNth_zero' q.1 q.2
  | simp [Fin.insertNthEquiv, Fin.insertNth_zero']
  | rfl

/- English proof (translation)
Establish `hpi` using `(MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => (volume : Measure ℂ)) 0).symm`. Establish `hF : Measurable fun x : Fin (p + 1) → ℂ => ∫⁻ r : R, G (x, r)` using `hG.lintegral_prod_right'`. Establish `hcons : ∀ w : ℂ, Measurable (fun q : (Fin p → ℂ) × R => ((Fin.cons w q.1 : Fin (p + 1) → ℂ), q.2))`. Introduce `w`. Establish `hm : Measurable (fun q : (Fin p → ℂ) × R => ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm (w, q.1), q.2))` using `by first`.

Consider the case `exact ((MeasurableEquiv.measurable _).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd`. Consider the case `exact ((MeasurableEquiv.measurable _).comp (measurable_const.prod_mk measurable_fst)).prod_mk measurable_snd`. Simplify `hm` using `only [cons_symm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[MeasureTheory.lintegral_prod (fun y : ℂ × (Fin p → ℂ) => ∫⁻ r : R, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm y, r)) (hF.comp (MeasurableEquiv.measurable _)).aemeasurable]`.

Simplify using `only [cons_symm]`. Use `_ = ∫⁻ w : ℂ, ∫⁻ q : (Fin p → ℂ) × R, G (Fin.cons w q.1, q.2) := by`. Use `MeasureTheory.lintegral_congr fun w => ?_` and prove the remaining obligations. Conclude with `(MeasureTheory.lintegral_prod (fun q : (Fin p → ℂ) × R => G (Fin.cons w q.1, q.2)) (hG.comp (hcons w)).aemeasurable).symm`.
-/
lemma split_cons {p : ℕ} {R : Type*} [MeasureSpace R] [SFinite (volume : Measure R)]
    (G : (Fin (p + 1) → ℂ) × R → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G z = ∫⁻ w : ℂ, ∫⁻ q : (Fin p → ℂ) × R, G (Fin.cons w q.1, q.2) := by
  have hpi := (MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => (volume : Measure ℂ)) 0).symm
  have hF : Measurable fun x : Fin (p + 1) → ℂ => ∫⁻ r : R, G (x, r) := hG.lintegral_prod_right'
  have hcons : ∀ w : ℂ, Measurable (fun q : (Fin p → ℂ) × R => ((Fin.cons w q.1 : Fin (p + 1) → ℂ), q.2)) := by
    intro w
    have hm : Measurable (fun q : (Fin p → ℂ) × R =>
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm (w, q.1), q.2)) := by
      first
      | exact ((MeasurableEquiv.measurable _).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
      | exact ((MeasurableEquiv.measurable _).comp (measurable_const.prod_mk measurable_fst)).prod_mk measurable_snd
    simpa only [cons_symm] using hm
  calc ∫⁻ z, G z = ∫⁻ x : Fin (p + 1) → ℂ, ∫⁻ r : R, G (x, r) := MeasureTheory.lintegral_prod _ hG.aemeasurable
    _ = ∫⁻ y : ℂ × (Fin p → ℂ), (∫⁻ r : R, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm y, r))
          ∂((volume : Measure ℂ).prod (volume : Measure (Fin p → ℂ))) := (hpi.lintegral_comp hF).symm
    _ = ∫⁻ w : ℂ, ∫⁻ q : Fin p → ℂ, ∫⁻ r : R, G (Fin.cons w q, r) := by
          rw [MeasureTheory.lintegral_prod (fun y : ℂ × (Fin p → ℂ) =>
            ∫⁻ r : R, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm y, r))
            (hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
          simp only [cons_symm]
    _ = ∫⁻ w : ℂ, ∫⁻ q : (Fin p → ℂ) × R, G (Fin.cons w q.1, q.2) := by
          refine MeasureTheory.lintegral_congr fun w => ?_
          exact (MeasureTheory.lintegral_prod (fun q : (Fin p → ℂ) × R => G (Fin.cons w q.1, q.2))
            (hG.comp (hcons w)).aemeasurable).symm

/- English proof (translation)
Rewrite using `[split_cons G hG]`. Apply `MeasureTheory.lintegral_lintegral_swap` to reduce the goal to its premises. Apply `Measurable.aemeasurable` to reduce the goal to its premises. Establish `hm : Measurable (fun x : ℂ × ((Fin p → ℂ) × R) => ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm (x.1, x.2.1), x.2.2))` using `by first`. Consider the case `exact ((MeasurableEquiv.measurable _).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)`.

Consider the case `exact ((MeasurableEquiv.measurable _).comp (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))).prod_mk (measurable_snd.comp measurable_snd)`. Establish `h2` using `hG.comp hm`. Simplify using `only [cons_symm] at h2`. Conclude with `h2`.
-/
lemma split_cons' {p : ℕ} {R : Type*} [MeasureSpace R] [SFinite (volume : Measure R)]
    (G : (Fin (p + 1) → ℂ) × R → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G z = ∫⁻ q : (Fin p → ℂ) × R, ∫⁻ w : ℂ, G (Fin.cons w q.1, q.2) := by
  rw [split_cons G hG]
  apply MeasureTheory.lintegral_lintegral_swap
  apply Measurable.aemeasurable
  have hm : Measurable (fun x : ℂ × ((Fin p → ℂ) × R) =>
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm (x.1, x.2.1), x.2.2)) := by
    first
    | exact ((MeasurableEquiv.measurable _).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)
    | exact ((MeasurableEquiv.measurable _).comp (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))).prod_mk
        (measurable_snd.comp measurable_snd)
  have h2 := hG.comp hm
  simp only [cons_symm] at h2
  exact h2

def sclL (p m : ℕ) (t : ℝ) : Xp p m →ₗ[ℝ] Xp p m :=
  (t • LinearMap.id).prodMap ((t • LinearMap.id).prodMap ((t • LinearMap.id).prodMap ((t ^ 2) • LinearMap.id)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma sclL_apply (p m : ℕ) (t : ℝ) (x : Xp p m) :
    sclL p m t x = (t • x.1, t • x.2.1, t • x.2.2.1, t ^ 2 * x.2.2.2) := rfl

/- English proof (translation)
Unfold `sclL`. Rewrite using `[LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_prodMap]`. Simplify using `only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma det_sclL (p m : ℕ) (t : ℝ) : LinearMap.det (sclL p m t) = t ^ (4 * p + 2 * m + 2) := by
  unfold sclL
  rw [LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_prodMap]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self]
  ring

/- English proof (translation)
Establish `hdet : LinearMap.det (sclL p m t) ≠ 0`. Rewrite using `[det_sclL]`. Conclude with `pow_ne_zero _ ht.ne'`. Establish `hmap` using `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Xp p m)) hdet`. Establish `htp : 0 < t ^ (4 * p + 2 * m + 2)` using `pow_pos ht _`.

Rewrite using `[← MeasureTheory.lintegral_map hG (LinearMap.continuous_of_finiteDimensional (sclL p m t)).measurable, hmap, MeasureTheory.lintegral_smul_measure, det_sclL, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul htp.le, abs_of_pos (inv_pos.mpr htp), mul_inv_cancel₀ htp.ne', ENNReal.ofRea …`.
-/
lemma lint_scl {p m : ℕ} {G : Xp p m → ℝ≥0∞} (hG : Measurable G) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, G x = ENNReal.ofReal (t ^ (4 * p + 2 * m + 2)) * ∫⁻ x, G (sclL p m t x) := by
  have hdet : LinearMap.det (sclL p m t) ≠ 0 := by
    rw [det_sclL]
    exact pow_ne_zero _ ht.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Xp p m)) hdet
  have htp : 0 < t ^ (4 * p + 2 * m + 2) := pow_pos ht _
  rw [← MeasureTheory.lintegral_map hG (LinearMap.continuous_of_finiteDimensional (sclL p m t)).measurable, hmap,
    MeasureTheory.lintegral_smul_measure, det_sclL, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul htp.le,
    abs_of_pos (inv_pos.mpr htp), mul_inv_cancel₀ htp.ne', ENNReal.ofReal_one, one_mul]

/- English proof (translation)
Use `set u := x.2.2.1 with hu`. Use `set β := x.2.2.2 with hβ`. Use `set S : ℝ := ∑ i, ‖u i‖ ^ 2 with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `ha : ‖u‖ ^ 2 ≤ S`.

Establish `h1 : ‖u‖ ≤ Real.sqrt S`. Rewrite using `[pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]`. Introduce `i`. Rewrite using `[Real.le_sqrt (norm_nonneg _) hS0]`. Conclude with `Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL : ∀ l : Fin 1, Lsq x l = 1`. Introduce `l`. Simplify using `[Lsq]`. Establish `hrho : rhoSq x 0 = 1 + S`.

Simplify using `[rhoSq, hL, hS, hu]`. Establish `hbco : ‖bco x 0‖ ^ 2 = (S / 2) ^ 2 + β ^ 2`. Establish `h1 : bco x 0 = ((-S / 2 : ℝ) : ℂ) + (β : ℂ) * Complex.I`. Simplify using `[bco, hS, hu, hβ]`. Rewrite using `[h1, Complex.sq_norm, Complex.normSq_add_mul_I]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < (1 + S / 2) ^ 2 + β ^ 2` using `by positivity`. Establish `hAq : de x 0 = Real.sqrt ((1 + S / 2) ^ 2 + β ^ 2)`. Unfold `de`. Rewrite using `[hL, hrho, hbco]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hs0 : s0N 0 m 0 = (m : ℝ) + 1` using `by simp [s0N]`. Rewrite using `[hAq, hs0, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]`. Establish `hsplit : (1 / 2 : ℝ) * -((m : ℝ) + 1 + v) = -((m : ℝ) + v / 2) / 2 + -(1 + v / 2) / 2` using `by ring`.

Rewrite using `[hsplit, Real.rpow_add hpos]`. Establish `he1 : 0 ≤ (m : ℝ) + v / 2` using `by positivity`. Establish `hb1 : ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2) ≤ 2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2)`. Establish `hh : (1 + ‖u‖ ^ 2) / 2 ≤ 1 + S / 2` using `by linarith`. Establish `h0 : 0 ≤ (1 + ‖u‖ ^ 2) / 2` using `by positivity`.

Establish `hq : ((1 + ‖u‖ ^ 2) / 2) ^ 2 ≤ (1 + S / 2) ^ 2 + β ^ 2`. Use polynomial arithmetic with `[mul_le_mul hh hh h0 (by linarith), sq_nonneg β]`. Establish `hq0 : 0 < ((1 + ‖u‖ ^ 2) / 2) ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hy : ((1 + ‖u‖ ^ 2) / 2) ^ 2 = ((1 + ‖u‖ ^ 2) / 2) ^ (2 : ℝ)` using `(Real.rpow_two _).symm`.

Rewrite using `[hy, ← Real.rpow_mul h0, Real.div_rpow (by positivity) (by norm_num)]`. Rewrite using `[show (2 : ℝ) * (-((m : ℝ) + v / 2) / 2) = -((m : ℝ) + v / 2) by ring, show -(2 * ((m : ℝ) + v / 2)) / 2 = -((m : ℝ) + v / 2) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb2 : ((1 + S / 2) ^ 2 + β ^ 2) ^ (-(1 + v / 2) / 2) ≤ (1 + ‖β‖ ^ 2) ^ (-(1 + v / 2) / 2)`. Establish `hq : 1 + ‖β‖ ^ 2 ≤ (1 + S / 2) ^ 2 + β ^ 2`.

Rewrite using `[Real.norm_eq_abs, sq_abs]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma base_pt (m : ℕ) (v : ℝ) (hv : 0 < v) (x : Xp 0 m) :
    de x 0 ^ (-(s0N 0 m 0 + v)) ≤ 2 ^ (m + v / 2 : ℝ) *
      ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * (m + v / 2 : ℝ)) / 2) * (1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + v / 2) / 2)) := by
  set u := x.2.2.1 with hu
  set β := x.2.2.2 with hβ
  set S : ℝ := ∑ i, ‖u i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have ha : ‖u‖ ^ 2 ≤ S := by
    have h1 : ‖u‖ ≤ Real.sqrt S := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      rw [Real.le_sqrt (norm_nonneg _) hS0]
      exact Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)
    calc ‖u‖ ^ 2 ≤ (Real.sqrt S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = S := Real.sq_sqrt hS0
  have hL : ∀ l : Fin 1, Lsq x l = 1 := by
    intro l
    simp [Lsq]
  have hrho : rhoSq x 0 = 1 + S := by
    simp [rhoSq, hL, hS, hu]
  have hbco : ‖bco x 0‖ ^ 2 = (S / 2) ^ 2 + β ^ 2 := by
    have h1 : bco x 0 = ((-S / 2 : ℝ) : ℂ) + (β : ℂ) * Complex.I := by
      simp [bco, hS, hu, hβ]
    rw [h1, Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have hpos : 0 < (1 + S / 2) ^ 2 + β ^ 2 := by positivity
  have hAq : de x 0 = Real.sqrt ((1 + S / 2) ^ 2 + β ^ 2) := by
    unfold de
    rw [hL, hrho, hbco]
    congr 1
    ring
  have hs0 : s0N 0 m 0 = (m : ℝ) + 1 := by simp [s0N]
  rw [hAq, hs0, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]
  have hsplit : (1 / 2 : ℝ) * -((m : ℝ) + 1 + v) = -((m : ℝ) + v / 2) / 2 + -(1 + v / 2) / 2 := by ring
  rw [hsplit, Real.rpow_add hpos]
  have he1 : 0 ≤ (m : ℝ) + v / 2 := by positivity
  have hb1 : ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2) ≤
      2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2) := by
    have hh : (1 + ‖u‖ ^ 2) / 2 ≤ 1 + S / 2 := by linarith
    have h0 : 0 ≤ (1 + ‖u‖ ^ 2) / 2 := by positivity
    have hq : ((1 + ‖u‖ ^ 2) / 2) ^ 2 ≤ (1 + S / 2) ^ 2 + β ^ 2 := by
      nlinarith [mul_le_mul hh hh h0 (by linarith), sq_nonneg β]
    have hq0 : 0 < ((1 + ‖u‖ ^ 2) / 2) ^ 2 := by positivity
    calc ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2)
        ≤ (((1 + ‖u‖ ^ 2) / 2) ^ 2) ^ (-((m : ℝ) + v / 2) / 2) :=
          Real.rpow_le_rpow_of_nonpos hq0 hq (by linarith)
      _ = 2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2) := by
          have hy : ((1 + ‖u‖ ^ 2) / 2) ^ 2 = ((1 + ‖u‖ ^ 2) / 2) ^ (2 : ℝ) := (Real.rpow_two _).symm
          rw [hy, ← Real.rpow_mul h0, Real.div_rpow (by positivity) (by norm_num)]
          rw [show (2 : ℝ) * (-((m : ℝ) + v / 2) / 2) = -((m : ℝ) + v / 2) by ring,
            show -(2 * ((m : ℝ) + v / 2)) / 2 = -((m : ℝ) + v / 2) by ring,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
          ring
  have hb2 : ((1 + S / 2) ^ 2 + β ^ 2) ^ (-(1 + v / 2) / 2) ≤ (1 + ‖β‖ ^ 2) ^ (-(1 + v / 2) / 2) := by
    have hq : 1 + ‖β‖ ^ 2 ≤ (1 + S / 2) ^ 2 + β ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith)
  calc ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2) * ((1 + S / 2) ^ 2 + β ^ 2) ^ (-(1 + v / 2) / 2)
      ≤ (2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2)) *
          (1 + ‖β‖ ^ 2) ^ (-(1 + v / 2) / 2) :=
        mul_le_mul hb1 hb2 (Real.rpow_nonneg hpos.le _) (by positivity)
    _ = _ := by ring

/- English proof (translation)
Use `first`. Consider the case `simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]`. Consider the case `(rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]; simp)`. Consider the case `simp`.
-/
lemma volume_univ_fin_zero : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
  first
  | simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  | (rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]; simp)
  | simp

/- English proof (translation)
Establish `hv` using `hν`. Establish `hf1 : MeasureTheory.Integrable (fun u : Fin m → ℂ => (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2))`. Apply `integrable_rpow_neg_one_add_norm_sq` to reduce the goal to its premises. Simplify using `only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf2 : MeasureTheory.Integrable (fun b : ℝ => (1 + ‖b‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))`. Apply `integrable_rpow_neg_one_add_norm_sq` to reduce the goal to its premises. Rewrite using `[Module.finrank_self]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm1 : Measurable fun u : Fin m → ℂ => ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2))` using `by first`. Consider the case `fun_prop`. Consider the case `measurability`. Establish `hm2 : Measurable fun b : ℝ => ENNReal.ofReal ((1 + ‖b‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))` using `by first`.

Consider the case `fun_prop`. Consider the case `measurability`. Establish `hprod : ∫⁻ y : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖y.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖y.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) < ∞`. Rewrite using `[MeasureTheory.Measure.volume_eq_prod, MeasureTheory.lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]`. Conclude with `ENNReal.mul_lt_top hf1.lintegral_lt_top hf2.lintegral_lt_top`.

Establish `hpeel : ∀ {β : Type} [MeasureSpace β] [SFinite (volume : Measure β)] (g : β → ℝ≥0∞), Measurable g → ∫⁻ x : (Fin 0 → ℂ) × β, g x.2 = ∫⁻ y, g y`. Introduce `β _ _ g hg`. Rewrite using `[MeasureTheory.Measure.volume_eq_prod, MeasureTheory.lintegral_prod (fun x : (Fin 0 → ℂ) × β => g x.2) (hg.comp measurable_snd).aemeasurable]`. Simplify using `only [MeasureTheory.lintegral_const, volume_univ_fin_zero, mul_one]`. Establish `hbound : CHInt 0 m ν ≤ ∫⁻ x : Xp 0 m, ENNReal.ofReal (2 ^ ((m : ℝ) + ν 0 / 2)) * (ENNReal.ofReal ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)))`.

Unfold `CHInt`. Use `MeasureTheory.lintegral_mono fun x => ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_one, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x.2.2.1‖ ^ 2) _), ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ ((m : ℝ) + ν 0 / 2))]`. Conclude with `ENNReal.ofReal_le_ofReal (base_pt m (ν 0) hν x)`. Use `lt_of_le_of_lt hbound ?_` and prove the remaining obligations.

Rewrite using `[MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_` and prove the remaining obligations. Establish `hg1 : Measurable fun z : (Fin m → ℂ) × ℝ => ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))` using `(hm1.comp measurable_fst).mul (hm2.comp measurable_snd)`. Establish `e1 : ∫⁻ x : Xp 0 m, ENNReal.ofReal ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) = ∫⁻ y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ), ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofRe …` using `hpeel (fun y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ) => ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) (hg1.comp measurable_snd)`. Establish `e2 : ∫⁻ y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ), ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) = ∫⁻ z : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.o …` using `hpeel (fun z : (Fin m → ℂ) × ℝ => ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) * ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) hg1`.

Rewrite using `[e1, e2]`. Conclude with `hprod`.
-/
lemma ch_base (m : ℕ) (ν : Fin 1 → ℝ) (hν : 0 < ν 0) : CHInt 0 m ν < ∞ := by
  have hv := hν
  have hf1 : MeasureTheory.Integrable
      (fun u : Fin m → ℂ => (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    push_cast
    linarith
  have hf2 : MeasureTheory.Integrable (fun b : ℝ => (1 + ‖b‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [Module.finrank_self]
    push_cast
    linarith
  have hm1 : Measurable fun u : Fin m → ℂ => ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) := by
    first
    | fun_prop
    | measurability
  have hm2 : Measurable fun b : ℝ => ENNReal.ofReal ((1 + ‖b‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) := by
    first
    | fun_prop
    | measurability
  have hprod : ∫⁻ y : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖y.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
      ENNReal.ofReal ((1 + ‖y.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) < ∞ := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
    exact ENNReal.mul_lt_top hf1.lintegral_lt_top hf2.lintegral_lt_top
  have hpeel : ∀ {β : Type} [MeasureSpace β] [SFinite (volume : Measure β)] (g : β → ℝ≥0∞), Measurable g →
      ∫⁻ x : (Fin 0 → ℂ) × β, g x.2 = ∫⁻ y, g y := by
    intro β _ _ g hg
    rw [MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.lintegral_prod (fun x : (Fin 0 → ℂ) × β => g x.2) (hg.comp measurable_snd).aemeasurable]
    simp only [MeasureTheory.lintegral_const, volume_univ_fin_zero, mul_one]
  have hbound : CHInt 0 m ν ≤ ∫⁻ x : Xp 0 m, ENNReal.ofReal (2 ^ ((m : ℝ) + ν 0 / 2)) *
      (ENNReal.ofReal ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) := by
    unfold CHInt
    refine MeasureTheory.lintegral_mono fun x => ?_
    rw [Fin.prod_univ_one,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x.2.2.1‖ ^ 2) _),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ ((m : ℝ) + ν 0 / 2))]
    exact ENNReal.ofReal_le_ofReal (base_pt m (ν 0) hν x)
  refine lt_of_le_of_lt hbound ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hg1 : Measurable fun z : (Fin m → ℂ) × ℝ => ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
      ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) :=
    (hm1.comp measurable_fst).mul (hm2.comp measurable_snd)
  have e1 : ∫⁻ x : Xp 0 m, ENNReal.ofReal ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
      ENNReal.ofReal ((1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) =
      ∫⁻ y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ), ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) :=
    hpeel (fun y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ) =>
      ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) (hg1.comp measurable_snd)
  have e2 : ∫⁻ y : (Fin 0 → ℂ) × ((Fin m → ℂ) × ℝ), ENNReal.ofReal ((1 + ‖y.2.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖y.2.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) =
      ∫⁻ z : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2)) :=
    hpeel (fun z : (Fin m → ℂ) × ℝ => ENNReal.ofReal ((1 + ‖z.1‖ ^ 2) ^ (-(2 * ((m : ℝ) + ν 0 / 2)) / 2)) *
        ENNReal.ofReal ((1 + ‖z.2‖ ^ 2) ^ (-(1 + ν 0 / 2) / 2))) hg1
  rw [e1, e2]
  exact hprod

end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
