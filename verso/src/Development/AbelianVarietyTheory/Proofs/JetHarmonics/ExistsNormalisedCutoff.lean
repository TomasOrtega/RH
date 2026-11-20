import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPosStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory
namespace QuotCutoff

def mulM {m : ℕ} (a b : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a * Matrix.of b) i j

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [mulM, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
lemma continuous_mulM {m : ℕ} : Continuous (fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
The claim follows from `Matrix.mul_assoc (Matrix.of a) (Matrix.of b) (Matrix.of c)`.
-/
lemma mulM_assoc {m : ℕ} (a b c : PI.MtM m) : mulM (mulM a b) c = mulM a (mulM b c) :=
  Matrix.mul_assoc (Matrix.of a) (Matrix.of b) (Matrix.of c)

/- English proof (translation)
The claim follows from `continuous_mulM.comp (continuous_id.prodMk continuous_const)`.
-/
lemma continuous_mulM_left {m : ℕ} (x : PI.MtM m) : Continuous (fun s => mulM s x) :=
  continuous_mulM.comp (continuous_id.prodMk continuous_const)

def invM {m : ℕ} (a : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a)⁻¹ i j

/- English proof (translation)
Establish `hu : IsUnit (Matrix.of a).det` using `Matrix.isUnit_det_of_right_inverse h`. Establish `h1 : ContinuousAt Ring.inverse (Matrix.of a).det`. Take `⟨u, hu⟩` from `hu`. Rewrite using `[← hu]`. Conclude with `NormedRing.inverse_continuousAt u`.

Conclude with `continuousAt_matrix_inv (Matrix.of a) h1`.
-/
lemma continuousAt_invM {m : ℕ} (a : PI.MtM m) (h : Matrix.of a * (Matrix.of a)⁻¹ = 1) :
    ContinuousAt invM a := by
  have hu : IsUnit (Matrix.of a).det := Matrix.isUnit_det_of_right_inverse h
  have h1 : ContinuousAt Ring.inverse (Matrix.of a).det := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact continuousAt_matrix_inv (Matrix.of a) h1

def piece {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (j : ℕ) : Set (PI.MtM m) :=
  {x | Matrix.of x ∈ G} ∩ Metric.closedBall 0 (j : ℝ)

/- English proof (translation)
The claim follows from `hG`.
-/
lemma isClosed_of {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) :
    IsClosed {x : PI.MtM m | Matrix.of x ∈ G} := hG

/- English proof (translation)
The claim follows from `(isCompact_closedBall _ _).inter_left (isClosed_of hG)`.
-/
lemma isCompact_piece {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) (j : ℕ) :
    IsCompact (piece G j) :=
  (isCompact_closedBall _ _).inter_left (isClosed_of hG)

/- English proof (translation)
Establish `hC` using `isCompact_piece hG.1 j`. Use `set K : Set (PI.MtM m) := (fun p : PI.MtM m × PI.MtM m => mulM p.1 (invM p.2)) '' (piece G j ×ˢ piece G j) with hK`. Establish `hKc : IsCompact K`. Use `(hC.prod hC).image_of_continuousOn ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ ⟨-, hb⟩`.

Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Establish `h1 : ContinuousAt (fun p : PI.MtM m × PI.MtM m => invM p.2) (a, b)` using `ContinuousAt.comp (g := invM) (f := fun p : PI.MtM m × PI.MtM m => p.2) (x := (a, b)) (continuousAt_invM b (hG.2.2.2 (Matrix.of b) hb.1).2) continuousAt_snd`. Conclude with `ContinuousAt.comp (g := fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2) (f := fun p : PI.MtM m × PI.MtM m => (p.1, invM p.2)) continuous_mulM.continuousAt (continuousAt_fst.prodMk h1)`. Establish `hKS : IsCompact (K ∩ {x | Matrix.of x ∈ S})` using `hKc.inter_right (isClosed_of hS.1)`. Use `⟨μ (K ∩ {x | Matrix.of x ∈ S}), (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.1 _ hKS (fun x hx => hx.2), fun x => ?_⟩` and prove the remaining obligations.

Establish `hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S` using `hμ.2.2.1`. Establish `hA : MeasurableSet ((fun s => mulM s x) ⁻¹' piece G j)` using `(hC.isClosed.preimage (continuous_mulM_left x)).measurableSet`. Distinguish the cases in `h : ∃ s₀ : PI.MtM m, Matrix.of s₀ ∈ S ∧ mulM s₀ x ∈ piece G j`. Take `⟨s₀, hs₀, hx⟩` from `h`. Establish `h1 : μ.map (fun s => mulM s s₀) = μ` using `hR _ hs₀`.

Rewrite using `[← h1, Measure.map_apply (continuous_mulM_left s₀).measurable hA, h1]`. Use `measure_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with t ht hti`. Use `⟨⟨(mulM t (mulM s₀ x), mulM s₀ x), ⟨?_, hx⟩, ?_⟩, ht⟩` and prove the remaining obligations. Rewrite using `[← mulM_assoc]`.

Conclude with `hti`. Establish `h2` using `(hG.2.2.2 (Matrix.of (mulM s₀ x)) hx.1).2`. Express the relevant statement in the definitionally equal form `Matrix.of t * Matrix.of (mulM s₀ x) * (Matrix.of (mulM s₀ x))⁻¹ = Matrix.of t`. Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`. Use `measure_mono_ae ?_ filter_upwards [hae] with t ht hti` and prove the remaining obligations.

Conclude with `absurd ⟨t, ht, hti⟩ h`.
-/
lemma exists_bound {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) (j : ℕ) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ x : PI.MtM m, μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ c := by
  have hC := isCompact_piece hG.1 j
  set K : Set (PI.MtM m) :=
    (fun p : PI.MtM m × PI.MtM m => mulM p.1 (invM p.2)) '' (piece G j ×ˢ piece G j) with hK
  have hKc : IsCompact K := by
    refine (hC.prod hC).image_of_continuousOn ?_
    rintro ⟨a, b⟩ ⟨-, hb⟩
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun p : PI.MtM m × PI.MtM m => invM p.2) (a, b) :=
      ContinuousAt.comp (g := invM) (f := fun p : PI.MtM m × PI.MtM m => p.2) (x := (a, b))
        (continuousAt_invM b (hG.2.2.2 (Matrix.of b) hb.1).2) continuousAt_snd
    exact ContinuousAt.comp (g := fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2)
      (f := fun p : PI.MtM m × PI.MtM m => (p.1, invM p.2))
      continuous_mulM.continuousAt (continuousAt_fst.prodMk h1)
  have hKS : IsCompact (K ∩ {x | Matrix.of x ∈ S}) := hKc.inter_right (isClosed_of hS.1)
  refine ⟨μ (K ∩ {x | Matrix.of x ∈ S}),
    (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.1 _ hKS (fun x hx => hx.2), fun x => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hA : MeasurableSet ((fun s => mulM s x) ⁻¹' piece G j) :=
    (hC.isClosed.preimage (continuous_mulM_left x)).measurableSet
  by_cases h : ∃ s₀ : PI.MtM m, Matrix.of s₀ ∈ S ∧ mulM s₀ x ∈ piece G j
  · obtain ⟨s₀, hs₀, hx⟩ := h
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    rw [← h1, Measure.map_apply (continuous_mulM_left s₀).measurable hA, h1]
    refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    refine ⟨⟨(mulM t (mulM s₀ x), mulM s₀ x), ⟨?_, hx⟩, ?_⟩, ht⟩
    · rw [← mulM_assoc]; exact hti
    · have h2 := (hG.2.2.2 (Matrix.of (mulM s₀ x)) hx.1).2
      change Matrix.of t * Matrix.of (mulM s₀ x) * (Matrix.of (mulM s₀ x))⁻¹ = Matrix.of t
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  · refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    exact absurd ⟨t, ht, hti⟩ h

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_nat_gt ‖x‖`. Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S` using `hμ.2.2.1`. Establish `hU : IsOpen ((fun s => mulM s x) ⁻¹' Metric.ball 0 (j : ℝ))` using `Metric.isOpen_ball.preimage (continuous_mulM_left x)`. Establish `h1 : mulM (Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)) x = x` using `Matrix.one_mul (Matrix.of x)`.

Use `(GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.2 _ hU ⟨Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ), by` as an intermediate fact. Rewrite using `[Set.mem_preimage, h1]`. Simplify using `using hj, hS.2.1⟩`. Use `this.trans_le (measure_mono_ae ?_)` and prove the remaining obligations. Use `filter_upwards [hae] with t ht hti`.

Conclude with `⟨hG.2.2.1 _ (hSG ht) _ hx, Metric.ball_subset_closedBall hti⟩`.
-/
lemma exists_pos {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (x : PI.MtM m) (hx : Matrix.of x ∈ G) :
    ∃ j : ℕ, 0 < μ ((fun s => mulM s x) ⁻¹' piece G j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
  refine ⟨j, ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hU : IsOpen ((fun s => mulM s x) ⁻¹' Metric.ball 0 (j : ℝ)) :=
    Metric.isOpen_ball.preimage (continuous_mulM_left x)
  have h1 : mulM (Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)) x = x :=
    Matrix.one_mul (Matrix.of x)
  have := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.2 _ hU
    ⟨Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ), by
      rw [Set.mem_preimage, h1]; simpa using hj, hS.2.1⟩
  refine this.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with t ht hti
  exact ⟨hG.2.2.1 _ (hSG ht) _ hx, Metric.ball_subset_closedBall hti⟩

/- English proof (translation)
Use `choose c hc hb using exists_bound hG hS hμ hR`. Establish `hP : ∀ j, MeasurableSet (piece G j)` using `fun j => (isCompact_piece hG.1 j).measurableSet`. Use `set w : ℕ → ℝ≥0∞ := fun j => (2⁻¹ : ℝ≥0∞) ^ j * (1 + c j)⁻¹ with hw`. Establish `hmeas : ∀ j, Measurable ((piece G j).indicator (fun _ => w j))` using `fun j => measurable_const.indicator (hP j)`. Establish `hI : ∀ x : PI.MtM m, ∫⁻ s, (∑' j, (piece G j).indicator (fun _ => w j) (mulM s x)) ∂μ = ∑' j, w j * μ ((fun s => mulM s x) ⁻¹' piece G j)`.

Introduce `x`. Rewrite using `[lintegral_tsum (f := fun j s => (piece G j).indicator (fun _ => w j) (mulM s x)) (fun j => ((hmeas j).comp (continuous_mulM_left x).measurable).aemeasurable)]`. Use `congr 1`. Use extensionality with `j`. Rewrite using `[← lintegral_indicator_const ((continuous_mulM_left x).measurable (hP j))]`.

Both sides reduce to the same expression. Use `⟨fun y => ∑' j, (piece G j).indicator (fun _ => w j) y, Measurable.ennreal_tsum hmeas, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hI x]`. Prove the components needed by the constructor for the conclusion. Take `⟨j, hj⟩` from `exists_pos hG hS hSG hμ x hx`.

Introduce `h`. Rewrite `h` using `[ENNReal.tsum_eq_zero]`. Establish `hwj : w j ≠ 0`. Use `mul_ne_zero (pow_ne_zero _ (by simp)) ?_` and prove the remaining obligations. Rewrite using `[ENNReal.inv_ne_zero]`.

Conclude with `ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, (hc j).ne⟩`. Conclude with `mul_ne_zero hwj hj.ne' (h j)`. Use `ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) ?_ (ENNReal.tsum_le_tsum fun j => ?_)` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_geometric]`. Simplify using the standard rewrite rules.

Establish `h1 : (1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(hb j x).trans le_add_self`. Use `_ ≤ 1 := ENNReal.inv_mul_le_one _`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma exists_precutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) :
    ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (mulM s x) ∂μ ≠ 0 ∧ ∫⁻ s, φ (mulM s x) ∂μ ≠ ⊤ := by
  choose c hc hb using exists_bound hG hS hμ hR
  have hP : ∀ j, MeasurableSet (piece G j) := fun j => (isCompact_piece hG.1 j).measurableSet
  set w : ℕ → ℝ≥0∞ := fun j => (2⁻¹ : ℝ≥0∞) ^ j * (1 + c j)⁻¹ with hw
  have hmeas : ∀ j, Measurable ((piece G j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hP j)
  have hI : ∀ x : PI.MtM m, ∫⁻ s, (∑' j, (piece G j).indicator (fun _ => w j) (mulM s x)) ∂μ
      = ∑' j, w j * μ ((fun s => mulM s x) ⁻¹' piece G j) := by
    intro x
    rw [lintegral_tsum (f := fun j s => (piece G j).indicator (fun _ => w j) (mulM s x))
      (fun j => ((hmeas j).comp (continuous_mulM_left x).measurable).aemeasurable)]
    congr 1
    ext j
    rw [← lintegral_indicator_const ((continuous_mulM_left x).measurable (hP j))]
    rfl
  refine ⟨fun y => ∑' j, (piece G j).indicator (fun _ => w j) y,
    Measurable.ennreal_tsum hmeas, fun x hx => ?_⟩
  rw [hI x]
  constructor
  · obtain ⟨j, hj⟩ := exists_pos hG hS hSG hμ x hx
    intro h
    rw [ENNReal.tsum_eq_zero] at h
    have hwj : w j ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (by simp)) ?_
      rw [ENNReal.inv_ne_zero]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, (hc j).ne⟩
    exact mul_ne_zero hwj hj.ne' (h j)
  · refine ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) ?_
      (ENNReal.tsum_le_tsum fun j => ?_)
    · rw [ENNReal.tsum_geometric]
      simp
    · have h1 : (1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ 1 := by
        calc _ ≤ (1 + c j)⁻¹ * (1 + c j) := by
              gcongr
              exact (hb j x).trans le_add_self
          _ ≤ 1 := ENNReal.inv_mul_le_one _
      calc w j * _ = (2⁻¹ : ℝ≥0∞) ^ j * ((1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j)) :=
            mul_assoc _ _ _
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ j * 1 := by gcongr
        _ = _ := mul_one _

end QuotCutoff

open QuotCutoff in

/- English proof (translation)
Introduce `m G S μ hG hS hSG hμ hR`. Take `⟨φ, hφ, hI⟩` from `exists_precutoff hG hS hSG hμ hR`. Use `haveI := hμ.1`. Use `set I : PI.MtM m → ℝ≥0∞ := fun x => ∫⁻ s, φ (mulM s x) ∂μ with hIdef`. Establish `hIm : Measurable I` using `Measurable.lintegral_prod_left' (f := fun p : PI.MtM m × PI.MtM m => φ (mulM p.1 p.2)) (hφ.comp continuous_mulM.measurable)`.

Establish `hinv : ∀ s₀ x : PI.MtM m, Matrix.of s₀ ∈ S → I (mulM s₀ x) = I x`. Introduce `s₀ x hs₀`. Establish `h1 : μ.map (fun s => mulM s s₀) = μ` using `hR _ hs₀`. Establish `h2` using `lintegral_map (μ := μ) (f := fun s => φ (mulM s x)) (hφ.comp (continuous_mulM_left x).measurable) (continuous_mulM_left s₀).measurable`. Rewrite `h2` using `[h1]`.

Simplify using `only [hIdef]`. Rewrite using `[h2]`. Simplify using `only [mulM_assoc]`. Use `⟨fun y => φ y * (I y)⁻¹, hφ.mul hIm.inv, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S` using `hμ.2.2.1`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with s hs`. Rewrite using `[hinv s x hs]`. Use `_ = I x * (I x)⁻¹ := lintegral_mul_const _ (hφ.comp (continuous_mulM_left x).measurable)`.

Use `_ = 1 := ENNReal.mul_inv_cancel (hI x hx).1 (hI x hx).2`.
-/
theorem exists_normalised_cutoff : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G → ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
  intro m G S μ hG hS hSG hμ hR
  obtain ⟨φ, hφ, hI⟩ := exists_precutoff hG hS hSG hμ hR
  haveI := hμ.1
  set I : PI.MtM m → ℝ≥0∞ := fun x => ∫⁻ s, φ (mulM s x) ∂μ with hIdef
  have hIm : Measurable I :=
    Measurable.lintegral_prod_left' (f := fun p : PI.MtM m × PI.MtM m => φ (mulM p.1 p.2))
      (hφ.comp continuous_mulM.measurable)
  have hinv : ∀ s₀ x : PI.MtM m, Matrix.of s₀ ∈ S → I (mulM s₀ x) = I x := by
    intro s₀ x hs₀
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    have h2 := lintegral_map (μ := μ) (f := fun s => φ (mulM s x))
      (hφ.comp (continuous_mulM_left x).measurable) (continuous_mulM_left s₀).measurable
    rw [h1] at h2
    simp only [hIdef]
    rw [h2]
    simp only [mulM_assoc]
  refine ⟨fun y => φ y * (I y)⁻¹, hφ.mul hIm.inv, fun x hx => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  calc ∫⁻ s, φ (mulM s x) * (I (mulM s x))⁻¹ ∂μ = ∫⁻ s, φ (mulM s x) * (I x)⁻¹ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        rw [hinv s x hs]
    _ = I x * (I x)⁻¹ := lintegral_mul_const _ (hφ.comp (continuous_mulM_left x).measurable)
    _ = 1 := ENNReal.mul_inv_cancel (hI x hx).1 (hI x hx).2

end GlobalTheory
