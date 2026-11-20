import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACProper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation

open MeasureTheory Topology Matrix
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def linM {k r : ℕ} (A Bb : B.Mat k r) : Mt k r →ₗ[ℝ] Mt k r :=
  ((LinearMap.mulLeft ℝ A).comp (LinearMap.mulRight ℝ Bb) : B.Mat k r →ₗ[ℝ] B.Mat k r)

/- English proof (translation)
Use `show A * ((Matrix.of v : B.Mat k r) * Bb) = _`. Rewrite using `[Matrix.mul_assoc]`.
-/
theorem linM_apply {k r : ℕ} (A Bb : B.Mat k r) (v : Mt k r) :
    (Matrix.of (linM A Bb v) : B.Mat k r) = A * Matrix.of v * Bb := by
  show A * ((Matrix.of v : B.Mat k r) * Bb) = _
  rw [Matrix.mul_assoc]

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D φ₀ hφ hφc hφs g₀ hg₀`. Take `⟨ε₀, hε₀, hball⟩` from `Metric.mem_nhds_iff.1 ((Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z').mem_nhds hg₀.2)`. Establish `hε : 0 < ε₀ / 2` using `by positivity`. Establish `hCb : Metric.closedBall g₀ (ε₀ / 2) ⊆ Q.OmPlus k r D.z D.z'` using `fun x hx => hball (Metric.closedBall_subset_ball (by linarith) hx)`. Establish `hC'c : IsCompact (Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r)` using `(isCompact_closedBall g₀ (ε₀ / 2)).inter_right Formalism.FourierDecayAlt.P.B5.GV_closed`.

Establish `hC'O : Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r ⊆ JF.Om k r D.z D.z'` using `fun x hx => ⟨hx.2, hCb hx.1⟩`. Take `⟨P, hPc, hPp⟩` from `hP k r Wp Wq D (tsupport φ₀) _ hφc hC'c hC'O`. Use `set Am : B.SS k r → B.Mat k r := fun p => (Hpk k r * (Matrix.of p.1.1 : B.Mat k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of p.1.2 : B.Mat k r)ᴴ * Hpk k r) with hAm`. Use `set Bm : B.SS k r → B.Mat k r := fun p => (Matrix.of p.2.2 : B.Mat k r) * Matrix.of p.2.1 with hBm`. Establish `hsgs : ∀ p, D.inSS p → ∀ g, B.sgs p g = Am p * g * Bm p`.

Introduce `p hp g`. Use `show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.1.1, Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.2.1.1]`. Simplify using `only [hAm, hBm, Matrix.mul_assoc]`. Establish `hof : Continuous (fun ν : Mt k r => (Matrix.of ν : B.Mat k r))` using `continuous_id`.

Establish `hAc : Continuous Am`. Establish `h1 : Continuous (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r))` using `hof.comp continuous_fst.fst`. Establish `h2 : Continuous (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r))` using `hof.comp continuous_fst.snd`. Conclude with `((continuous_const.mul h1.matrix_conjTranspose).mul continuous_const).mul ((continuous_const.mul h2.matrix_conjTranspose).mul continuous_const)`. Establish `hBc : Continuous Bm`.

Establish `h3 : Continuous (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r))` using `hof.comp continuous_snd.snd`. Establish `h4 : Continuous (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r))` using `hof.comp continuous_snd.fst`. Conclude with `h3.mul h4`. Establish `hcont : Continuous (fun p : B.SS k r => B.gN (Am p) * B.gN (Bm p))` using `(Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hAc).mul (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hBc)`. Take `⟨M₁, hM₁⟩` from `hPc.exists_bound_of_continuousOn hcont.continuousOn`.

Use `set L : B.SS k r → (Mt k r →L[ℝ] Mt k r) := fun p => LinearMap.toContinuousLinearMap (linM (Am p) (Bm p)) with hLdef`. Establish `hL : ∀ p (v : Mt k r), (Matrix.of (L p v) : B.Mat k r) = Am p * Matrix.of v * Bm p` using `fun p v => linM_apply (Am p) (Bm p) v`. Use `set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn`. Establish `hnn0 : 0 ≤ nn` using `by positivity`. Use `set ML : ℝ := nn * max M₁ 0 with hML`.

Establish `hML0 : 0 ≤ ML` using `mul_nonneg hnn0 (le_max_right _ _)`. Establish `hLn : ∀ p ∈ P, ‖L p‖ ≤ ML`. Introduce `p hp`. Apply `ContinuousLinearMap.opNorm_le_bound _ hML0` to reduce the goal to its premises. Introduce `v`.

Establish `e1 : ‖L p v‖ = ‖(Matrix.of (L p v) : B.Mat k r)‖` using `rfl`. Establish `e2 : ‖v‖ = ‖(Matrix.of v : B.Mat k r)‖` using `rfl`. Rewrite using `[e1, e2, hL]`. Use `set g : B.Mat k r := Matrix.of v`. Establish `hgA` using `Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Am p)`.

Establish `hgB` using `Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Bm p)`. Establish `hgg` using `Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg g`. Establish `hgn : B.gN g ≤ nn * ‖g‖` using `Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_le_of_ent g ‖g‖ (norm_nonneg _) (fun i j => Matrix.norm_entry_le_entrywise_sup_norm g)`. Establish `hAB : B.gN (Am p) * B.gN (Bm p) ≤ max M₁ 0`. Use `hM₁ p hp` as an intermediate fact.

Rewrite `this` using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgA hgB)]`. Conclude with `this.trans (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation. Use `set φ₁ : Mt k r → ℝ := fun v => φ₀ (Matrix.of v) with hφ₁def`. Establish `hφ₁ : ContDiff ℝ ∞ φ₁` using `hφ`.

Establish `hφ₁c : HasCompactSupport φ₁` using `hφc`. Establish `hK : ∀ i : ℕ, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ i φ₁ x‖ ≤ K` using `fun i => (hφ₁.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hφ₁c.iteratedFDeriv i)`. Use `choose K hKb using hK`. Use `set F : B.SS k r → Mt k r → ℝ := fun p y => P.indicator (fun p => φ₁ (L p y)) p with hF`. Establish `hFin : ∀ p ∈ P, F p = φ₁ ∘ (L p)` using `fun p hp => by`.

Use function extensionality and compare the values at `y`. Simplify using `[hF, hp]`. Establish `hFout : ∀ p ∉ P, F p = fun _ => 0` using `fun p hp => by`. Use function extensionality and compare the values at `y`. Simplify using `[hF, hp]`.

Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'` as an intermediate fact. Establish `: IsFiniteMeasureOnCompacts D.μW` using `⟨D.haarW.finite_compact⟩`. Establish `: IsFiniteMeasureOnCompacts D.μN` using `⟨D.haarN.finite_compact⟩`.

Establish `: IsFiniteMeasureOnCompacts D.μW'` using `⟨D.haarW'.finite_compact⟩`. Establish `: IsFiniteMeasureOnCompacts (D.μW.prod D.μN)` using `inferInstance`. Establish `: IsFiniteMeasureOnCompacts (D.μW'.prod D.μN)` using `inferInstance`. Establish `: IsFiniteMeasureOnCompacts D.μSS` using `by show IsFiniteMeasureOnCompacts ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) infer_instance`. Establish `hPfin : D.μSS P ≠ ⊤` using `(hPc.measure_lt_top (μ := D.μSS)).ne`.

Establish `hPm : MeasurableSet P` using `hPc.isClosed.measurableSet`. Establish `hFm : ∀ y, AEStronglyMeasurable (fun p => F p y) D.μSS`. Introduce `y`. Establish `hc : Continuous (fun p => φ₁ (L p y))`. Establish `: (fun p => φ₁ (L p y)) = fun p => φ₀ (Am p * Matrix.of y * Bm p)`.

Use function extensionality and compare the values at `p`. Simplify using `only [hφ₁def]`. Rewrite using `[hL]`. Rewrite using `[this]`. Conclude with `hφ.continuous.comp ((hAc.mul continuous_const).mul hBc)`.

Conclude with `(hc.measurable.indicator hPm).aestronglyMeasurable`. Establish `hsm : ContDiffOn ℝ ∞ (fun y => ∫ p, F p y ∂D.μSS) (Metric.ball (Matrix.of.symm g₀ : Mt k r) (ε₀ / 2))`. Rewrite using `[contDiffOn_infty]`. Introduce `N`. Use `set Kt : ℝ := (∑ i ∈ Finset.range (N + 1), |K i|) * (max ML 1) ^ N with hKt`.

Establish `hb : Integrable (P.indicator fun _ => Kt) D.μSS` using `(integrableOn_const hPfin).integrable_indicator hPm`. Use `(Formalism.FourierDecayAlt.P.Ux10.pint Metric.isOpen_ball (P.indicator fun _ => Kt) hb N ℝ F ?_ (fun y _ => hFm y) ?_).1` and prove the remaining obligations. Introduce `p`. Distinguish the cases in `hp : p ∈ P`. Rewrite using `[hFin p hp]`.

Conclude with `(hφ₁.comp (L p).contDiff).contDiffOn.of_le (mod_cast le_top)`. Rewrite using `[hFout p hp]`. Conclude with `contDiffOn_const`. Introduce `i hi y _ p`. Distinguish the cases in `hp : p ∈ P`.

Rewrite using `[hFin p hp, ContinuousLinearMap.iteratedFDeriv_comp_right (L p) hφ₁ y (mod_cast le_top)]`. Simplify using `only [Set.indicator_of_mem hp]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `h1 : ‖iteratedFDeriv ℝ i φ₁ (L p y)‖ ≤ ∑ j ∈ Finset.range (N + 1), |K j|` using `(hKb i _).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))`.

Establish `h2 : ‖L p‖ ^ i ≤ (max ML 1) ^ N` using `(pow_le_pow_left₀ (norm_nonneg _) ((hLn p hp).trans (le_max_left _ _)) i).trans (pow_le_pow_right₀ (le_max_right _ _) hi)`. Conclude with `mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Finset.sum_nonneg fun j _ => abs_nonneg _)`. Rewrite using `[hFout p hp, iteratedFDeriv_fun_zero]`. Simplify using `[Set.indicator_of_notMem hp]`. Use `⟨Metric.ball g₀ (ε₀ / 2), fun g => ∫ p, F p (Matrix.of.symm g) ∂D.μSS, Metric.isOpen_ball, Metric.mem_ball_self hε, hsm, ?_⟩` and prove the remaining obligations.

Introduce `g hg hgG`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp`. Distinguish the cases in `hpP : p ∈ P`. Establish `e : φ₁ (L p (Matrix.of.symm g)) = φ₀ (Am p * g * Bm p)`.

Simplify using `only [hφ₁def]`. Rewrite using `[hL]`. Both sides reduce to the same expression. Simplify using `only [hF, Set.indicator_of_mem hpP, e, hsgs p hp g]`. Establish `h0 : φ₀ (B.sgs p g) = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hpP (hPp p hp g ⟨Metric.ball_subset_closedBall hg, hgG⟩ (subset_tsupport _ hne))`. Simplify using `[hF, hpP, h0]`.
-/
theorem aCSmooth_of_proper (hP : ACProper) : ACSmooth := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc hφs g₀ hg₀

  obtain ⟨ε₀, hε₀, hball⟩ :=
    Metric.mem_nhds_iff.1 ((Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z').mem_nhds hg₀.2)
  have hε : 0 < ε₀ / 2 := by positivity
  have hCb : Metric.closedBall g₀ (ε₀ / 2) ⊆ Q.OmPlus k r D.z D.z' := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  have hC'c : IsCompact (Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r) :=
    (isCompact_closedBall g₀ (ε₀ / 2)).inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  have hC'O : Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r ⊆ JF.Om k r D.z D.z' := fun x hx => ⟨hx.2, hCb hx.1⟩
  obtain ⟨P, hPc, hPp⟩ := hP k r Wp Wq D (tsupport φ₀) _ hφc hC'c hC'O

  set Am : B.SS k r → B.Mat k r := fun p =>
    (Hpk k r * (Matrix.of p.1.1 : B.Mat k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of p.1.2 : B.Mat k r)ᴴ * Hpk k r)
    with hAm
  set Bm : B.SS k r → B.Mat k r := fun p => (Matrix.of p.2.2 : B.Mat k r) * Matrix.of p.2.1 with hBm
  have hsgs : ∀ p, D.inSS p → ∀ g, B.sgs p g = Am p * g * Bm p := by
    intro p hp g
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _
    rw [Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.1.1, Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.2.1.1]
    simp only [hAm, hBm, Matrix.mul_assoc]
  have hof : Continuous (fun ν : Mt k r => (Matrix.of ν : B.Mat k r)) := continuous_id
  have hAc : Continuous Am := by
    have h1 : Continuous (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)) := hof.comp continuous_fst.fst
    have h2 : Continuous (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)) := hof.comp continuous_fst.snd
    exact ((continuous_const.mul h1.matrix_conjTranspose).mul continuous_const).mul
      ((continuous_const.mul h2.matrix_conjTranspose).mul continuous_const)
  have hBc : Continuous Bm := by
    have h3 : Continuous (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) := hof.comp continuous_snd.snd
    have h4 : Continuous (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) := hof.comp continuous_snd.fst
    exact h3.mul h4
  have hcont : Continuous (fun p : B.SS k r => B.gN (Am p) * B.gN (Bm p)) :=
    (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hAc).mul (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hBc)
  obtain ⟨M₁, hM₁⟩ := hPc.exists_bound_of_continuousOn hcont.continuousOn
  set L : B.SS k r → (Mt k r →L[ℝ] Mt k r) := fun p => LinearMap.toContinuousLinearMap (linM (Am p) (Bm p))
    with hLdef
  have hL : ∀ p (v : Mt k r), (Matrix.of (L p v) : B.Mat k r) = Am p * Matrix.of v * Bm p := fun p v =>
    linM_apply (Am p) (Bm p) v
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := by positivity
  set ML : ℝ := nn * max M₁ 0 with hML
  have hML0 : 0 ≤ ML := mul_nonneg hnn0 (le_max_right _ _)
  have hLn : ∀ p ∈ P, ‖L p‖ ≤ ML := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ hML0
    intro v
    have e1 : ‖L p v‖ = ‖(Matrix.of (L p v) : B.Mat k r)‖ := rfl
    have e2 : ‖v‖ = ‖(Matrix.of v : B.Mat k r)‖ := rfl
    rw [e1, e2, hL]
    set g : B.Mat k r := Matrix.of v
    have hgA := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Am p)
    have hgB := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Bm p)
    have hgg := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg g
    have hgn : B.gN g ≤ nn * ‖g‖ :=
      Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_le_of_ent g ‖g‖ (norm_nonneg _) (fun i j => Matrix.norm_entry_le_entrywise_sup_norm g)
    have hAB : B.gN (Am p) * B.gN (Bm p) ≤ max M₁ 0 := by
      have := hM₁ p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgA hgB)] at this
      exact this.trans (le_max_left _ _)
    calc ‖Am p * g * Bm p‖ ≤ B.gN (Am p * g * Bm p) := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN _
      _ ≤ B.gN (Am p * g) * B.gN (Bm p) := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Am p) * B.gN g) * B.gN (Bm p) :=
          mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) hgB
      _ = (B.gN (Am p) * B.gN (Bm p)) * B.gN g := by ring
      _ ≤ max M₁ 0 * (nn * ‖g‖) := mul_le_mul hAB hgn hgg (le_max_right _ _)
      _ = ML * ‖g‖ := by rw [hML]; ring

  set φ₁ : Mt k r → ℝ := fun v => φ₀ (Matrix.of v) with hφ₁def
  have hφ₁ : ContDiff ℝ ∞ φ₁ := hφ
  have hφ₁c : HasCompactSupport φ₁ := hφc
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ i φ₁ x‖ ≤ K := fun i =>
    (hφ₁.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hφ₁c.iteratedFDeriv i)
  choose K hKb using hK

  set F : B.SS k r → Mt k r → ℝ := fun p y => P.indicator (fun p => φ₁ (L p y)) p with hF
  have hFin : ∀ p ∈ P, F p = φ₁ ∘ (L p) := fun p hp => by
    funext y; simp [hF, hp]
  have hFout : ∀ p ∉ P, F p = fun _ => 0 := fun p hp => by
    funext y; simp [hF, hp]

  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨D.haarW.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨D.haarN.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨D.haarW'.finite_compact⟩
  have : IsFiniteMeasureOnCompacts (D.μW.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts (D.μW'.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts D.μSS := by
    show IsFiniteMeasureOnCompacts ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
    infer_instance
  have hPfin : D.μSS P ≠ ⊤ := (hPc.measure_lt_top (μ := D.μSS)).ne
  have hPm : MeasurableSet P := hPc.isClosed.measurableSet
  have hFm : ∀ y, AEStronglyMeasurable (fun p => F p y) D.μSS := by
    intro y
    have hc : Continuous (fun p => φ₁ (L p y)) := by
      have : (fun p => φ₁ (L p y)) = fun p => φ₀ (Am p * Matrix.of y * Bm p) := by
        funext p; simp only [hφ₁def]; rw [hL]
      rw [this]
      exact hφ.continuous.comp ((hAc.mul continuous_const).mul hBc)
    exact (hc.measurable.indicator hPm).aestronglyMeasurable
  have hsm : ContDiffOn ℝ ∞ (fun y => ∫ p, F p y ∂D.μSS) (Metric.ball (Matrix.of.symm g₀ : Mt k r) (ε₀ / 2)) := by
    rw [contDiffOn_infty]
    intro N
    set Kt : ℝ := (∑ i ∈ Finset.range (N + 1), |K i|) * (max ML 1) ^ N with hKt
    have hb : Integrable (P.indicator fun _ => Kt) D.μSS :=
      (integrableOn_const hPfin).integrable_indicator hPm
    refine (Formalism.FourierDecayAlt.P.Ux10.pint Metric.isOpen_ball (P.indicator fun _ => Kt) hb N ℝ F ?_ (fun y _ => hFm y) ?_).1
    · intro p
      by_cases hp : p ∈ P
      · rw [hFin p hp]
        exact (hφ₁.comp (L p).contDiff).contDiffOn.of_le (mod_cast le_top)
      · rw [hFout p hp]; exact contDiffOn_const
    · intro i hi y _ p
      by_cases hp : p ∈ P
      · rw [hFin p hp, ContinuousLinearMap.iteratedFDeriv_comp_right (L p) hφ₁ y (mod_cast le_top)]
        simp only [Set.indicator_of_mem hp]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have h1 : ‖iteratedFDeriv ℝ i φ₁ (L p y)‖ ≤ ∑ j ∈ Finset.range (N + 1), |K j| :=
          (hKb i _).trans ((le_abs_self _).trans
            (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
        have h2 : ‖L p‖ ^ i ≤ (max ML 1) ^ N :=
          (pow_le_pow_left₀ (norm_nonneg _) ((hLn p hp).trans (le_max_left _ _)) i).trans
            (pow_le_pow_right₀ (le_max_right _ _) hi)
        exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _)
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
      · rw [hFout p hp, iteratedFDeriv_fun_zero]
        simp [Set.indicator_of_notMem hp]
  refine ⟨Metric.ball g₀ (ε₀ / 2), fun g => ∫ p, F p (Matrix.of.symm g) ∂D.μSS, Metric.isOpen_ball,
    Metric.mem_ball_self hε, hsm, ?_⟩
  intro g hg hgG
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · have e : φ₁ (L p (Matrix.of.symm g)) = φ₀ (Am p * g * Bm p) := by
      simp only [hφ₁def]; rw [hL]; rfl
    simp only [hF, Set.indicator_of_mem hpP, e, hsgs p hp g]
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPp p hp g ⟨Metric.ball_subset_closedBall hg, hgG⟩ (subset_tsupport _ hne))
    simp [hF, hpP, h0]

/- English proof (translation)
The claim follows from `aCSmooth_of_proper averaging_properness_holds`.
-/
theorem averaging_smoothness_holds : ACSmooth := aCSmooth_of_proper averaging_properness_holds

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
