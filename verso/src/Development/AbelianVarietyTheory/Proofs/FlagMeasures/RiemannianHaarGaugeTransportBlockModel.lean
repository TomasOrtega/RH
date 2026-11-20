import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot

/- English proof (translation)
Establish `h` using `hf.umat_equiv (hf.equiv.symm k)`. Rewrite `h` using `[ContinuousMulEquiv.apply_symm_apply]`. Establish `h' : Formalism.MainNotions.S.uMat k - 1 = Matrix.reindex f f (UpqT.mat (hf.equiv.symm k) - 1)`. Rewrite using `[show Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.umat k from rfl, h]`. Use extensionality with `i j`.

Simplify using `[Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]`. Unfold `hsDist Formalism.REAL.hs`. Rewrite using `[h']`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply]`. Use `symm`.

Rewrite using `[← f.sum_comp]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← f.sum_comp]`. Simplify using the standard rewrite rules.
-/
theorem hsDist_equiv_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : hsDist (hf.equiv.symm k) = Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  have h' : Formalism.MainNotions.S.uMat k - 1 = Matrix.reindex f f (UpqT.mat (hf.equiv.symm k) - 1) := by
    rw [show Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.umat k from rfl, h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  unfold hsDist Formalism.REAL.hs
  rw [h']
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  symm
  rw [← f.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.sum_comp]
  simp

/- English proof (translation)
Establish `hV : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal` using `ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne`. Assume the negation of the conclusion as `hneg'`. Establish `hneg : c ≤ 0` using `not_lt.1 hneg'`. Establish `hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0` using `by filter_upwards [self_mem_nhdsWithin] with r hr`. Establish `hr' : (0 : ℝ) < r` using `hr`.

Conclude with `div_nonpos_iff.2 (Or.inr ⟨mul_nonpos_iff.2 (Or.inr ⟨hneg, ENNReal.toReal_nonneg⟩), (pow_pos hr' _).le⟩)`. Use `le_of_tendsto hc hle` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c) :
    0 < c := by
  have hV : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hneg'
  have hneg : c ≤ 0 := not_lt.1 hneg'
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2)
        ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    exact div_nonpos_iff.2 (Or.inr ⟨mul_nonpos_iff.2 (Or.inr ⟨hneg, ENNReal.toReal_nonneg⟩),
      (pow_pos hr' _).le⟩)
  have := le_of_tendsto hc hle
  linarith

/- English proof (translation)
Use `set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef`. Use `set A : ℝ → ℝ≥0∞ := fun r => Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r} with hAdef`. Use `set B : ℝ → ℝ≥0∞ := fun r => Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2} with hBdef`. Establish `hV : 0 < V` using `ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne`. Establish `hc' : Tendsto (fun r => c * (A r).toReal / r ^ (n ^ 2)) (𝓝[>] 0) (𝓝 V)` using `hc`.

Establish `hBA : ∀ r : ℝ, 0 < r → B r ≤ A r`. Introduce `r hr`. Apply `measure_mono` to reduce the goal to its premises. Introduce `g hg`. Conclude with `((Real.sqrt_lt' hr).2 hg).le`.

Establish `hAB : ∀ r s : ℝ, 0 < r → s < r → A s ≤ B r`. Introduce `r s hr hs`. Apply `measure_mono` to reduce the goal to its premises. Introduce `g hg`. Conclude with `(Real.sqrt_lt' hr).1 (lt_of_le_of_lt hg hs)`.

Establish `hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), A r ≠ ⊤` using `by filter_upwards [hc'.eventually (lt_mem_nhds hV)] with r hr htop`. Rewrite `hr` using `[htop]`. Simplify using `at hr`. Establish `h1 : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝[>] 0) (𝓝 1)`. Establish `: Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝 0) (𝓝 ((1 - 0) ^ (n ^ 2)))` using `((continuous_const.sub continuous_id).pow _).tendsto 0`.

Simplify using `using this.mono_left nhdsWithin_le_nhds`. Establish `h2 : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝[>] 0) (𝓝[>] 0)`. Apply `tendsto_nhdsWithin_iff.2` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Establish `: Tendsto (fun r : ℝ => (1 - r) * r) (𝓝 0) (𝓝 ((1 - 0) * 0))` using `((continuous_const.sub continuous_id).mul continuous_id).tendsto 0`.

Simplify using `using this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr`. Conclude with `mul_pos (by linarith [hr.2]) hr.1`. Establish `hlow : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2) * (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2))) (𝓝[>] 0) (𝓝 V)`. Simplify using `using h1.mul (hc'.comp h2)`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hc' ?_ ?_` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hfin] with r hr hAr`. Establish `hr0 : 0 < r` using `hr.1`. Establish `h1r : 0 < 1 - r` using `by linarith [hr.2]`. Establish `hBfin : B r ≠ ⊤` using `ne_top_of_le_ne_top hAr (hBA r hr0)`.

Establish `hle : (A ((1 - r) * r)).toReal ≤ (B r).toReal` using `ENNReal.toReal_mono hBfin (hAB r _ hr0 (by nlinarith))`. Establish `hne1 : (1 - r) ^ (n ^ 2) ≠ 0` using `pow_ne_zero _ h1r.ne'`. Establish `hne2 : r ^ (n ^ 2) ≠ 0` using `pow_ne_zero _ hr0.ne'`. Establish `heq : (1 - r) ^ (n ^ 2) * (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2)) = c * (A ((1 - r) * r)).toReal / r ^ (n ^ 2)`. Rewrite using `[mul_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`. Conclude with `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hc0.le) (pow_pos hr0 _).le`. Use `filter_upwards [self_mem_nhdsWithin, hfin] with r hr hAr`. Establish `hr0 : (0 : ℝ) < r` using `hr`.

Conclude with `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hAr (hBA r hr0)) hc0.le) (pow_pos hr0 _).le`.
-/
private theorem tendsto_gauge_ratio_volume_ball {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c)
    (hc0 : 0 < c) :
    Tendsto (fun r : ℝ =>
        c * (Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2}).toReal / r ^ (n ^ 2))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  set A : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r} with hAdef
  set B : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2} with hBdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hc' : Tendsto (fun r => c * (A r).toReal / r ^ (n ^ 2)) (𝓝[>] 0) (𝓝 V) := hc
  have hBA : ∀ r : ℝ, 0 < r → B r ≤ A r := by
    intro r hr
    apply measure_mono
    intro g hg
    exact ((Real.sqrt_lt' hr).2 hg).le
  have hAB : ∀ r s : ℝ, 0 < r → s < r → A s ≤ B r := by
    intro r s hr hs
    apply measure_mono
    intro g hg
    exact (Real.sqrt_lt' hr).1 (lt_of_le_of_lt hg hs)
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), A r ≠ ⊤ := by
    filter_upwards [hc'.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have h1 : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝 0) (𝓝 ((1 - 0) ^ (n ^ 2))) :=
      ((continuous_const.sub continuous_id).pow _).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝 0) (𝓝 ((1 - 0) * 0)) :=
        ((continuous_const.sub continuous_id).mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact mul_pos (by linarith [hr.2]) hr.1
  have hlow : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2) *
      (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2))) (𝓝[>] 0) (𝓝 V) := by
    simpa using h1.mul (hc'.comp h2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hc' ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hfin] with r hr hAr
    have hr0 : 0 < r := hr.1
    have h1r : 0 < 1 - r := by linarith [hr.2]
    have hBfin : B r ≠ ⊤ := ne_top_of_le_ne_top hAr (hBA r hr0)
    have hle : (A ((1 - r) * r)).toReal ≤ (B r).toReal :=
      ENNReal.toReal_mono hBfin (hAB r _ hr0 (by nlinarith))
    have hne1 : (1 - r) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ h1r.ne'
    have hne2 : r ^ (n ^ 2) ≠ 0 := pow_ne_zero _ hr0.ne'
    have heq : (1 - r) ^ (n ^ 2) * (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2)) =
        c * (A ((1 - r) * r)).toReal / r ^ (n ^ 2) := by
      rw [mul_pow]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hc0.le) (pow_pos hr0 _).le
  · filter_upwards [self_mem_nhdsWithin, hfin] with r hr hAr
    have hr0 : (0 : ℝ) < r := hr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hAr (hBA r hr0)) hc0.le) (pow_pos hr0 _).le

/- English proof (translation)
Introduce `n ε c P Q f hf hc`. Establish `hc0 : 0 < c` using `pos_of_isGauge' hc`. Use `⟨hc0, ?_⟩` and prove the remaining obligations. Establish `: BorelSpace (UpqT P Q)` using `⟨rfl⟩`. Establish `hPQ : P + Q = n` using `Sorts.add_eq f`.

Establish `hVfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Use `set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef`. Establish `hV : 0 < V` using `ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' hVfin`. Establish `hlim` using `tendsto_gauge_ratio_volume_ball hc hc0`. Establish `key : ∀ r : ℝ, ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) {g | hsDist g < r ^ 2} = ENNReal.ofReal c * Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2}`.

Introduce `r`. Rewrite using `[Measure.map_apply (show Measurable (hf.equiv.symm : Formalism.REAL.UJ ε → UpqT P Q) from hf.equiv.symm.continuous.measurable) (measurableSet_lt continuous_hsDist.measurable measurable_const), Measure.smul_apply, smul_eq_mul]`. Use `congr 2`. Use extensionality with `k`. Simplify using `[hsDist_equiv_symm hf k]`.

Establish `hBfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} ≠ ⊤` using `by filter_upwards [hlim.eventually (lt_mem_nhds hV)] with r hr htop`. Rewrite `hr` using `[htop]`. Simplify using `at hr`. Establish `hlim' : Tendsto (fun r : ℝ => ENNReal.ofReal (c * (Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2}).toReal / r ^ (n ^ 2) / V)) (𝓝[>] 0) (𝓝 1)`. Use `ENNReal.tendsto_ofReal (hlim.div_const V)` as an intermediate fact.

Rewrite `this` using `[div_self hV.ne', ENNReal.ofReal_one]`. Then use the resulting hypothesis. Unfold `HasEuclDensity`. Use `hlim'.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, hBfin] with r hr hB`. Establish `hr0 : (0 : ℝ) < r` using `hr`.

Establish `hball : ballVol ((P + Q) ^ 2) r = ENNReal.ofReal (r ^ (n ^ 2)) * ENNReal.ofReal V`. Use `ballVol_mul ((P + Q) ^ 2) r 1 hr0 one_pos` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this, hPQ, hVdef, ENNReal.ofReal_toReal hVfin]`. Both sides reduce to the same expression.

Rewrite using `[key r, hball, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), div_div, ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr0 _) hV), ENNReal.ofReal_mul hc0.le, ENNReal.ofReal_toReal hB]`.
-/
theorem gauge_transport : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  intro n ε c P Q f hf hc
  have hc0 : 0 < c := pos_of_isGauge' hc
  refine ⟨hc0, ?_⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have hPQ : P + Q = n := Sorts.add_eq f
  have hVfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' hVfin
  have hlim := tendsto_gauge_ratio_volume_ball hc hc0
  have key : ∀ r : ℝ, ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) {g | hsDist g < r ^ 2} =
      ENNReal.ofReal c * Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} := by
    intro r
    rw [Measure.map_apply (show Measurable (hf.equiv.symm : Formalism.REAL.UJ ε → UpqT P Q) from
        hf.equiv.symm.continuous.measurable)
      (measurableSet_lt continuous_hsDist.measurable measurable_const), Measure.smul_apply, smul_eq_mul]
    congr 2
    ext k
    simp [hsDist_equiv_symm hf k]
  have hBfin : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} ≠ ⊤ := by
    filter_upwards [hlim.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have hlim' : Tendsto (fun r : ℝ => ENNReal.ofReal
      (c * (Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2}).toReal / r ^ (n ^ 2) / V))
      (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (hlim.div_const V)
    rwa [div_self hV.ne', ENNReal.ofReal_one] at this
  unfold HasEuclDensity
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hBfin] with r hr hB
  have hr0 : (0 : ℝ) < r := hr
  have hball : ballVol ((P + Q) ^ 2) r = ENNReal.ofReal (r ^ (n ^ 2)) * ENNReal.ofReal V := by
    have := ballVol_mul ((P + Q) ^ 2) r 1 hr0 one_pos
    rw [mul_one] at this
    rw [this, hPQ, hVdef, ENNReal.ofReal_toReal hVfin]
    rfl
  rw [key r, hball, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), div_div,
    ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr0 _) hV), ENNReal.ofReal_mul hc0.le,
    ENNReal.ofReal_toReal hB]

end GlobalTheory.GaugeQuot
