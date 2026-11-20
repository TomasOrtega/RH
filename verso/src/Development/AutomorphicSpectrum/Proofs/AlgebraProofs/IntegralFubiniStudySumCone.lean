import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSumStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStableStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FubiniStudyLogLeLogNormStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConeBallLogGapIntegralStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

/- English proof (translation)
Establish `hfin : (fibrePts S π).Finite` using `Set.finite_of_encard_eq_coe hc`. Establish `hcard : hfin.toFinset.card = δ`. Establish `h1` using `hfin.encard_eq_coe_toFinset_card`. Rewrite `h1` using `[hc]`. Conclude with `h1.symm` after adjusting the coercions.

Establish `hne0 : ∀ y ∈ fibrePts S π, y ≠ 0`. Introduce and unpack `y ⟨-, hy⟩ rfl`. Establish `h2` using `congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) hy`. Simplify using `[linProj, firstCoordVec] at h2`. Establish `hsum : ∀ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j ≠ 0`.

Introduce `y hy h0`. Establish `htop : logGap h u y = ⊤` using `by simp [logGap, hne0 y hy, h0]`. Establish `hle : logGap h u y ≤ ∑' z : fibrePts S π, logGap h u z` using `ENNReal.le_tsum (f := fun z : fibrePts S π => logGap h u z) ⟨y, hy⟩`. Rewrite `hle` using `[htop]`. Conclude with `absurd hs (not_lt.2 hle)`.

Establish `hval : ∀ y ∈ fibrePts S π, logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y))`. Introduce `y hy`. Simplify using `[logGap, hne0 y hy, hsum y hy]`. Establish `hnn : ∀ y ∈ fibrePts S π, 0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y)` using `fun y hy => sub_nonneg.2 (GlobalTheory.T.fubini_study_log_le_log_norm n h u y (hne0 y hy) (hsum y hy))`. Use `haveI : Fintype (fibrePts S π) := hfin.fintype`.

Establish `htsum : ∑' z : fibrePts S π, logGap h u z = ∑ y ∈ hfin.toFinset, logGap h u y`. Rewrite using `[tsum_fintype]`. Conclude with `(Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) (logGap h u)).symm`. Rewrite using `[htsum, ENNReal.toReal_sum (fun y hy => by`. Rewrite using `[hval y (hfin.mem_toFinset.1 hy)]`.

Conclude with `ENNReal.ofReal_ne_top)]`. Rewrite using `[Finset.sum_congr rfl (fun y hy => by`. Rewrite using `[hval y (hfin.mem_toFinset.1 hy), ENNReal.toReal_ofReal (hnn y (hfin.mem_toFinset.1 hy))])]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, fsSum, finsum_mem_eq_finite_toFinset_sum _ hfin]`.
-/
theorem fubini_study_sum_crofton {n e δ : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hc : (fibrePts S π).encard = δ)
    (hs : ∑' y : fibrePts S π, logGap h u y < ⊤) :
    (∑' y : fibrePts S π, logGap h u y).toReal = δ * Real.log (h.norm u) - fsSum h u S π := by
  have hfin : (fibrePts S π).Finite := Set.finite_of_encard_eq_coe hc
  have hcard : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hc] at h1
    exact_mod_cast h1.symm
  have hne0 : ∀ y ∈ fibrePts S π, y ≠ 0 := by
    rintro y ⟨-, hy⟩ rfl
    have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) hy
    simp [linProj, firstCoordVec] at h2
  have hsum : ∀ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j ≠ 0 := by
    intro y hy h0
    have htop : logGap h u y = ⊤ := by simp [logGap, hne0 y hy, h0]
    have hle : logGap h u y ≤ ∑' z : fibrePts S π, logGap h u z :=
      ENNReal.le_tsum (f := fun z : fibrePts S π => logGap h u z) ⟨y, hy⟩
    rw [htop] at hle
    exact absurd hs (not_lt.2 hle)
  have hval : ∀ y ∈ fibrePts S π,
      logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y)) := by
    intro y hy
    simp [logGap, hne0 y hy, hsum y hy]
  have hnn : ∀ y ∈ fibrePts S π, 0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y) := fun y hy =>
    sub_nonneg.2 (GlobalTheory.T.fubini_study_log_le_log_norm n h u y (hne0 y hy) (hsum y hy))
  haveI : Fintype (fibrePts S π) := hfin.fintype
  have htsum : ∑' z : fibrePts S π, logGap h u z = ∑ y ∈ hfin.toFinset, logGap h u y := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) (logGap h u)).symm
  rw [htsum, ENNReal.toReal_sum (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy)]
      exact ENNReal.ofReal_ne_top)]
  rw [Finset.sum_congr rfl (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy), ENNReal.toReal_ofReal (hnn y (hfin.mem_toFinset.1 hy))])]
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, fsSum,
    finsum_mem_eq_finite_toFinset_sum _ hfin]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton

/- English proof (translation)
Use `haveI : Fintype (fibrePts S π) := hfin.fintype`. Rewrite using `[tsum_fintype]`. Conclude with `(Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) g).symm`.
-/
private theorem tsum_fibre_pts_eq_sum {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hfin : (fibrePts S π).Finite) (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    ∑' y : fibrePts S π, g y = ∑ y ∈ hfin.toFinset, g y := by
  haveI : Fintype (fibrePts S π) := hfin.fintype
  rw [tsum_fintype]
  exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) g).symm

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨-, h0⟩` from `hy`. Establish `h2` using `congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) h0`. Simplify using `[linProj, firstCoordVec] at h2`.
-/
private theorem ne_zero_of_mem_fibre_pts {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ fibrePts S π) : y ≠ 0 := by
  rintro rfl
  obtain ⟨-, h0⟩ := hy
  have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) h0
  simp [linProj, firstCoordVec] at h2

/- English proof (translation)
Introduce `n e δ h W f u hW hf hδ hu`. Take `⟨hLGm, hLGo⟩` from `GlobalTheory.T.log_gap_measurable_scale_stable n h u`. Take `⟨hGm, hGeq⟩` from `GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ (logGap h u) hLGm hLGo`. Take `⟨hL, hLr⟩` from `GlobalTheory.T.cone_ball_log_gap_integral n e h W f u hW hf hu`. Take `⟨hμ0, hμt⟩` from `GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n`.

Take `⟨hpm0, hpmt⟩ : 0 < planeMass n e ∧ planeMass n e < ⊤` from `GroundTheory.Heights₂.Heights.coordBall_mass (chowGroups_le hW hf hδ)`. Establish `hac : gaussM (e + 1) n ≪ (volume : Measure (Fin (e + 1) → Fin n → ℂ))` using `withDensity_absolutelyContinuous _ _`. Establish `hcnt : ∀ᵐ π ∂(gaussM (e + 1) n), (fibrePts (coneSet h W) π).encard = δ` using `hac.ae_le (GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ)`. Establish `hd : (0 : ℝ) < ((2 * (e + 1) : ℕ) : ℝ)` using `by positivity`. Use `haveI := MeasureTheory.Measure.nullSingletonClass_hausdorff (EuclideanSpace ℂ (Fin n)) hd`.

Establish `hφm : Measurable (({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)))` using `measurable_const.indicator (measurableSet_singleton 0).compl`. Establish `hφo : ∀ s : ℝ≥0∞, IsOpen {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} ∧ IsScaleStable {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y}`. Introduce `s`. Distinguish the cases in `hs1 : s < 1`. Establish `hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} = {0}ᶜ`.

Use extensionality with `y`. Distinguish the cases in `hy : y = 0`. Simplify using `[Set.indicator_apply, hy]`. Simplify using `[Set.indicator_apply, hy, hs1]`. Rewrite using `[hset]`.

Conclude with `⟨isOpen_compl_singleton, fun y hy t ht => by simpa [ht] using hy⟩`. Establish `hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} = ∅`. Use extensionality with `y`. Distinguish the cases in `hy : y = 0`. Simplify using `[Set.indicator_apply, hy]`.

Simplify using `[Set.indicator_apply, hy, hs1]`. Rewrite using `[hset]`. Conclude with `⟨isOpen_empty, fun y hy => hy.elim⟩`. Take `⟨-, hCeq⟩` from `GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ _ hφm hφo`. Establish `hae1 : ∀ᵐ π ∂(gaussM (e + 1) n), ∑' y : fibrePts (coneSet h W) π, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = δ` using `by filter_upwards [hcnt] with π hπ`.

Establish `hfin : (fibrePts (coneSet h W) π).Finite` using `Set.finite_of_encard_eq_coe hπ`. Establish `hcard : hfin.toFinset.card = δ`. Establish `h1` using `hfin.encard_eq_coe_toFinset_card`. Rewrite `h1` using `[hπ]`. Conclude with `h1.symm` after adjusting the coercions.

Establish `h1 : ∀ y ∈ hfin.toFinset, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = 1` using `fun y hy => Set.indicator_of_mem (ne_zero_of_mem_fibre_pts _ π y (hfin.mem_toFinset.1 hy)) _`. Rewrite using `[tsum_fibre_pts_eq_sum _ π hfin, Finset.sum_congr rfl h1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]`. Establish `hball : ∫⁻ y in coneBall h W, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) = Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W)`. Rewrite using `[lintegral_indicator_const (measurableSet_singleton 0).compl, one_mul, Measure.restrict_apply (measurableSet_singleton 0).compl, Set.inter_comm, ← Set.sdiff_eq, measure_sdiff_null (measure_singleton 0)]`. Rewrite `hCeq` using `[lintegral_congr_ae hae1, lintegral_const, hball]`.

Establish `hHc : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) = δ * planeMass n e`. Establish `h2 : gaussM (e + 1) n Set.univ * (δ * planeMass n e) = gaussM (e + 1) n Set.univ * Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W)`. Rewrite using `[← hCeq]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `((ENNReal.mul_right_inj hμ0.ne' hμt.ne).1 h2).symm`.

Establish `hGfin : ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, logGap h u y ∂(gaussM (e + 1) n) ≠ ⊤`. Introduce `htop`. Rewrite `hGeq` using `[htop, ENNReal.mul_top hpm0.ne']`. Conclude with `ENNReal.mul_ne_top hμt.ne hL.ne hGeq.symm`. Establish `hGae` using `ae_lt_top hGm hGfin`.

Establish `hfs : ∀ᵐ π ∂(gaussM (e + 1) n), fsSum h u (coneSet h W) π = δ * Real.log (h.norm u) - (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal` using `by filter_upwards [hcnt, hGae] with π h1 h2`. Rewrite using `[fubini_study_sum_crofton h u _ π h1 h2]`. Expand and normalize the polynomial expressions, which then agree. Use `haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hμt⟩`. Establish `hGint` using `integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfin`.

Establish `hint : Integrable (fun π => (δ : ℝ) * Real.log (h.norm u) - (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal) (gaussM (e + 1) n)` using `(integrable_const _).sub hGint`. Use `⟨hint.congr (hfs.mono fun π hπ => hπ.symm), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hfs, integral_sub (integrable_const _) hGint, integral_const, integral_toReal hGm.aemeasurable hGae, measureReal_def, smul_eq_mul]`. Establish `hX` using `congrArg ENNReal.toReal hGeq`. Rewrite `hX` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, hLr, hHc, ENNReal.toReal_mul, ENNReal.toReal_natCast]`.

Establish `hpmr : 0 < (planeMass n e).toReal` using `ENNReal.toReal_pos hpm0.ne' hpmt.ne`. Establish `hci : coneIntegral h W e (fsLog h u) = (∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / (planeMass n e).toReal` using `rfl`. Rewrite using `[hci]`. Establish `alg : ∀ a p X lg d I : ℝ, p ≠ 0 → p * X = a * (lg * (d * p) - I) → a * (d * lg) - X = a * (I / p)`. Introduce `a p X lg d I hp hX'`.

Establish `hX'' : X = a * (lg * (d * p) - I) / p`. Rewrite using `[eq_div_iff hp, mul_comm]`. Conclude with `hX'`. Rewrite using `[hX'']`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Conclude with `alg _ _ _ _ _ _ hpmr.ne' hX`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  intro n e δ h W f u hW hf hδ hu
  obtain ⟨hLGm, hLGo⟩ := GlobalTheory.T.log_gap_measurable_scale_stable n h u
  obtain ⟨hGm, hGeq⟩ := GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ (logGap h u) hLGm hLGo
  obtain ⟨hL, hLr⟩ := GlobalTheory.T.cone_ball_log_gap_integral n e h W f u hW hf hu
  obtain ⟨hμ0, hμt⟩ := GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n
  obtain ⟨hpm0, hpmt⟩ : 0 < planeMass n e ∧ planeMass n e < ⊤ :=
    GroundTheory.Heights₂.Heights.coordBall_mass (chowGroups_le hW hf hδ)
  have hac : gaussM (e + 1) n ≪ (volume : Measure (Fin (e + 1) → Fin n → ℂ)) :=
    withDensity_absolutelyContinuous _ _
  have hcnt : ∀ᵐ π ∂(gaussM (e + 1) n), (fibrePts (coneSet h W) π).encard = δ :=
    hac.ae_le (GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ)
  have hd : (0 : ℝ) < ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  haveI := MeasureTheory.Measure.nullSingletonClass_hausdorff (EuclideanSpace ℂ (Fin n)) hd
  have hφm : Measurable (({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_singleton 0).compl
  have hφo : ∀ s : ℝ≥0∞,
      IsOpen {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} ∧
      IsScaleStable {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} := by
    intro s
    by_cases hs1 : s < 1
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          {0}ᶜ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_compl_singleton, fun y hy t ht => by simpa [ht] using hy⟩
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          ∅ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  obtain ⟨-, hCeq⟩ := GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ _ hφm hφo
  have hae1 : ∀ᵐ π ∂(gaussM (e + 1) n), ∑' y : fibrePts (coneSet h W) π,
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = δ := by
    filter_upwards [hcnt] with π hπ
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hπ
    have hcard : hfin.toFinset.card = δ := by
      have h1 := hfin.encard_eq_coe_toFinset_card
      rw [hπ] at h1
      exact_mod_cast h1.symm
    have h1 : ∀ y ∈ hfin.toFinset,
        ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = 1 := fun y hy =>
      Set.indicator_of_mem (ne_zero_of_mem_fibre_pts _ π y (hfin.mem_toFinset.1 hy)) _
    rw [tsum_fibre_pts_eq_sum _ π hfin, Finset.sum_congr rfl h1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  have hball : ∫⁻ y in coneBall h W, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
    rw [lintegral_indicator_const (measurableSet_singleton 0).compl, one_mul,
      Measure.restrict_apply (measurableSet_singleton 0).compl, Set.inter_comm, ← Set.sdiff_eq,
      measure_sdiff_null (measure_singleton 0)]
  rw [lintegral_congr_ae hae1, lintegral_const, hball] at hCeq
  have hHc : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) = δ * planeMass n e := by
    have h2 : gaussM (e + 1) n Set.univ * (δ * planeMass n e) =
        gaussM (e + 1) n Set.univ * Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
      rw [← hCeq]
      ring
    exact ((ENNReal.mul_right_inj hμ0.ne' hμt.ne).1 h2).symm
  have hGfin : ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, logGap h u y ∂(gaussM (e + 1) n) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hpm0.ne'] at hGeq
    exact ENNReal.mul_ne_top hμt.ne hL.ne hGeq.symm
  have hGae := ae_lt_top hGm hGfin
  have hfs : ∀ᵐ π ∂(gaussM (e + 1) n), fsSum h u (coneSet h W) π =
      δ * Real.log (h.norm u) - (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal := by
    filter_upwards [hcnt, hGae] with π h1 h2
    rw [fubini_study_sum_crofton h u _ π h1 h2]
    ring
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hμt⟩
  have hGint := integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfin
  have hint : Integrable (fun π => (δ : ℝ) * Real.log (h.norm u) -
      (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal) (gaussM (e + 1) n) :=
    (integrable_const _).sub hGint
  refine ⟨hint.congr (hfs.mono fun π hπ => hπ.symm), ?_⟩
  rw [integral_congr_ae hfs, integral_sub (integrable_const _) hGint, integral_const,
    integral_toReal hGm.aemeasurable hGae, measureReal_def, smul_eq_mul]
  have hX := congrArg ENNReal.toReal hGeq
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hLr, hHc, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hX
  have hpmr : 0 < (planeMass n e).toReal := ENNReal.toReal_pos hpm0.ne' hpmt.ne
  have hci : coneIntegral h W e (fsLog h u) = (∫ y in coneBall h W, fsLog h u (h.pointOf y)
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / (planeMass n e).toReal := rfl
  rw [hci]
  have alg : ∀ a p X lg d I : ℝ, p ≠ 0 → p * X = a * (lg * (d * p) - I) →
      a * (d * lg) - X = a * (I / p) := by
    intro a p X lg d I hp hX'
    have hX'' : X = a * (lg * (d * p) - I) / p := by
      rw [eq_div_iff hp, mul_comm]
      exact hX'
    rw [hX'']
    field_simp
    ring
  exact alg _ _ _ _ _ _ hpmr.ne' hX
