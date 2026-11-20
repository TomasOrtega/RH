import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ReMulOfPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField

noncomputable section

namespace TopDualMetricChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

/- English proof (translation)
Consider the cases of `A`. Consider the cases of `B`. Consider the cases of `ha`. Consider the cases of `hh`. Both sides reduce to the same expression.
-/
theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

/- English proof (translation)
Establish `h0 : (fun t => z ⟨(), t⟩) = 0`. Use function extensionality and compare the values at `t`. Assume the negation of the conclusion as `h`. Conclude with `hz fun _ => ⟨t, h⟩`. Use `show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = 0`.

Rewrite using `[h0]`. Simplify using `[dualNormSq, ← Pi.zero_def]`.
-/
theorem dualLine_h_zero (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : ¬ ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0) : (dualLine F b hb).h z = 0 := by
  have h0 : (fun t => z ⟨(), t⟩) = 0 := by
    funext t; by_contra h; exact hz fun _ => ⟨t, h⟩
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = 0
  rw [h0]
  simp [dualNormSq, ← Pi.zero_def]

def weight (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : ((Σ _ : Unit, T) → ℂ) → ℝ :=
  fun z => Real.log ((dualLine F.withStdMetric b hb).h z) - Real.log ((dualLine F b hb).h z)

/- English proof (translation)
Introduce `c z hc`. Distinguish the cases in `hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0`. Simplify using `only [weight]`. Rewrite using `[(dualLine F.withStdMetric b hb).smul c z hc, (dualLine F b hb).smul c z hc]`. Establish `ha : (dualLine F.withStdMetric b hb).a = (dualLine F b hb).a` using `rfl`.

Establish `hs : 0 < ∏ k, ‖c k‖ ^ (dualLine F b hb).a k` using `Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _`. Rewrite using `[ha, Real.log_mul hs.ne' ((dualLine F.withStdMetric b hb).pos z hz).ne', Real.log_mul hs.ne' ((dualLine F b hb).pos z hz).ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `hz0 : ∀ p, z p = 0`. Introduce and unpack `⟨k, t⟩`.

Assume the negation of the conclusion as `h`. Conclude with `hz fun _ => ⟨t, h⟩`. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `[hz0 p]`.
-/
theorem weight_hom (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ∀ (c : Unit → ℂ) z, (∀ k, c k ≠ 0) → weight F b hb (fun p => c p.1 * z p) = weight F b hb z := by
  intro c z hc
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · simp only [weight]
    rw [(dualLine F.withStdMetric b hb).smul c z hc, (dualLine F b hb).smul c z hc]
    have ha : (dualLine F.withStdMetric b hb).a = (dualLine F b hb).a := rfl
    have hs : 0 < ∏ k, ‖c k‖ ^ (dualLine F b hb).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
    rw [ha, Real.log_mul hs.ne' ((dualLine F.withStdMetric b hb).pos z hz).ne',
      Real.log_mul hs.ne' ((dualLine F b hb).pos z hz).ne']
    ring
  · have hz0 : ∀ p, z p = 0 := by
      rintro ⟨k, t⟩; by_contra h; exact hz fun _ => ⟨t, h⟩
    congr 1; funext p; simp [hz0 p]

/- English proof (translation)
The claim follows from `((DualLineSemipositive.proof K i F.withStdMetric T b hb).1.log fun z hz => ((dualLine F.withStdMetric b hb).pos z hz).ne').sub ((DualLineSemipositive.proof K i F T b hb).1.log fun z hz => ((dualLine F b hb).pos z hz).ne')`.
-/
theorem weight_smooth (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : SmoothFn (weight F b hb) :=
  ((DualLineSemipositive.proof K i F.withStdMetric T b hb).1.log fun z hz =>
      ((dualLine F.withStdMetric b hb).pos z hz).ne').sub
    ((DualLineSemipositive.proof K i F T b hb).1.log fun z hz => ((dualLine F b hb).pos z hz).ne')

/- English proof (translation)
Use `hermLine_ext (funext fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, dualLine]) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Use `show (dualLine F b hb).h z = (dualLine F.withStdMetric b hb).h z * Real.exp (-weight F b hb z)`. Distinguish the cases in `hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0`. Establish `h1` using `(dualLine F.withStdMetric b hb).pos z hz`.

Establish `h2` using `(dualLine F b hb).pos z hz`. Rewrite using `[weight, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[dualLine_h_zero F b hb z hz, dualLine_h_zero F.withStdMetric b hb z hz, zero_mul]`.
-/
theorem dualLine_eq_tensor (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    dualLine F b hb = (dualLine F.withStdMetric b hb).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (weight F b hb) (weight_hom F b hb)) := by
  refine hermLine_ext (funext fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, dualLine]) ?_
  funext z
  show (dualLine F b hb).h z = (dualLine F.withStdMetric b hb).h z * Real.exp (-weight F b hb z)
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · have h1 := (dualLine F.withStdMetric b hb).pos z hz
    have h2 := (dualLine F b hb).pos z hz
    rw [weight, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
  · rw [dualLine_h_zero F b hb z hz, dualLine_h_zero F.withStdMetric b hb z hz, zero_mul]

/- English proof (translation)
Establish `hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w`. Introduce `Ψ y w`. Unfold `sheetDensity`. Apply the tactic sequence `split_ifs <;> simp [neg_mul]`. Unfold `ptsIntegral ptsIntegralAt`.

Use `split_ifs`. Rewrite using `[← MeasureTheory.integral_neg]`. Simplify using `only [hs, finsum_neg_distrib]`. Simplify using the standard rewrite rules.
-/
theorem ptsIntegral_neg {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => -g z) = -ptsIntegral P φ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp [neg_mul]
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · rw [← MeasureTheory.integral_neg]
    simp only [hs, finsum_neg_distrib]
  · simp

/- English proof (translation)
Simplify using `only [HermLattice.degree, subDegree, HermLattice.withStdMetric, IndefiniteRowSideFullHecke.Kernels.gramAt_single, Matrix.det_one, Complex.one_re, Real.log_one, Finset.sum_const_zero, mul_zero, sub_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degree_withStdMetric_sub (F : HermLattice K i) :
    F.withStdMetric.degree - F.degree = 1 / 2 * ∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re := by
  simp only [HermLattice.degree, subDegree, HermLattice.withStdMetric, IndefiniteRowSideFullHecke.Kernels.gramAt_single,
    Matrix.det_one, Complex.one_re, Real.log_one, Finset.sum_const_zero, mul_zero, sub_zero]
  ring

end TopDualMetricChange

open TopDualMetricChange in

/- English proof (translation)
Introduce `K _ _ i F T _ _ b hb II hi hII`. Take `⟨n, rfl⟩ : ∃ n, i = n + 1` from `⟨i - 1, by omega⟩`. Establish `hP : IsArithVar (dualIdeal b) (n + 1)` using `DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi`. Establish `hT` using `hTel Unit (dualBlocks T) (II Unit (dualBlocks T)) (hII Unit (dualBlocks T)) (dualIdeal b) n (dualLine F.withStdMetric b hb) (weight F b hb) (weight_hom F b hb) hP (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1 (weight_smooth F b hb)`. Rewrite `hT` using `[← dualLine_eq_tensor F b hb]`.

Establish `hw : weight F b hb = fun z => -(Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z))`. Use function extensionality and compare the values at `z`. Simplify using `only [weight]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hT` using `[hw]`.

Simplify using `only [ptsIntegral_neg, Finset.sum_neg_distrib, neg_neg] at hT`. Establish `hE : ∑ k ∈ Finset.range (n + 1), ptsIntegral (dualIdeal b) (pot fun j : Fin n => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb) (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) = 1 / 2 * (∑ σ : K →+* ℂ, Real.log …` using `hEnergy K (n + 1) F T b hb hi`. Rewrite using `[degree_withStdMetric_sub F]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem DualTopMetricChange.proof (hTel : TelescopeStatement) (hEnergy : DualMetricEnergy.Statement) :
    DualTopMetricChange.Statement := by
  intro K _ _ i F T _ _ b hb II hi hII
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hP : IsArithVar (dualIdeal b) (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi
  have hT := hTel Unit (dualBlocks T) (II Unit (dualBlocks T)) (hII Unit (dualBlocks T)) (dualIdeal b) n
    (dualLine F.withStdMetric b hb) (weight F b hb) (weight_hom F b hb) hP
    (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1 (weight_smooth F b hb)
  rw [← dualLine_eq_tensor F b hb] at hT
  have hw : weight F b hb = fun z =>
      -(Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) := by
    funext z; simp only [weight]; ring
  rw [hw] at hT
  simp only [ptsIntegral_neg, Finset.sum_neg_distrib, neg_neg] at hT
  have hE : ∑ k ∈ Finset.range (n + 1),
      ptsIntegral (dualIdeal b)
        (pot fun j : Fin n => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (n + 1 - 1)) (fsMulti (plBlocks 1 1 (n + 1 - 1))) (1 * 1 * (n + 1 - 1)) :=
    hEnergy K (n + 1) F T b hb hi
  rw [degree_withStdMetric_sub F]
  linarith

end

end GroundTheory.Heights₂.Heights
