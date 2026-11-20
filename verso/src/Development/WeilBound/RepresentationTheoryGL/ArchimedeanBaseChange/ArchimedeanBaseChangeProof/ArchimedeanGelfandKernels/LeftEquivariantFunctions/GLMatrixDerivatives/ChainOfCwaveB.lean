import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

def pX {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : ℝ × H → W) : ℝ × H → (H →L[ℝ] W) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inr ℝ ℝ H)

def Good {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (O : Set H) (Φ : ℝ × H → W) (T : ℝ) : Prop :=
  ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ O) ∧ ∀ t x, T < |t| → Φ (t, x) = 0

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {O : Set H}

/- English proof (translation)
Use `⟨(h.1.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)).clm_comp contDiffOn_const, fun t x ht => ?_⟩` and prove the remaining obligations. Establish `hO' : IsOpen {q : ℝ × H | T < |q.1|}` using `isOpen_lt continuous_const (continuous_abs.comp continuous_fst)`. Establish `hev : Φ =ᶠ[𝓝 (t, x)] fun _ => 0` using `Filter.eventuallyEq_of_mem (hO'.mem_nhds ht) fun q hq => h.2 q.1 q.2 hq`. Use `show (fderiv ℝ Φ (t, x)).comp _ = 0`. Rewrite using `[hev.fderiv_eq]`.

Simplify using the standard rewrite rules.
-/
theorem Good.deriv (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) : Good O (pX Φ) T := by
  refine ⟨(h.1.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)).clm_comp contDiffOn_const, fun t x ht => ?_⟩
  have hO' : IsOpen {q : ℝ × H | T < |q.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : Φ =ᶠ[𝓝 (t, x)] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hO'.mem_nhds ht) fun q hq => h.2 q.1 q.2 hq
  show (fderiv ℝ Φ (t, x)).comp _ = 0
  rw [hev.fderiv_eq]
  simp

/- English proof (translation)
The claim follows from `h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hx⟩`.
-/
theorem Good.cont_line {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Continuous fun t => Φ (t, x) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hx⟩

/- English proof (translation)
Use `(h.cont_line hx).integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_)` and prove the remaining obligations. Use `h.2 t x ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `ht (abs_le.1 (not_lt.1 hc))`.
-/
theorem Good.integrable {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Integrable (fun t => Φ (t, x)) := by
  refine (h.cont_line hx).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_)
  refine h.2 t x ?_
  by_contra hc
  exact ht (abs_le.1 (not_lt.1 hc))

/- English proof (translation)
Take `⟨ε, εpos, hε⟩` from `Metric.isOpen_iff.1 hO x₀ hx₀`. Establish `hsub : closedBall x₀ (ε / 2) ⊆ O` using `(closedBall_subset_ball (by linarith)).trans hε`. Establish `hK : IsCompact (Icc (-T) T ×ˢ closedBall x₀ (ε / 2))` using `isCompact_Icc.prod (isCompact_closedBall _ _)`. Establish `hKsub : Icc (-T) T ×ˢ closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ O` using `fun q hq => ⟨mem_univ _, hsub hq.2⟩`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn ((h.deriv hO).1.continuousOn.mono hKsub)`.

Establish `hdiff : ∀ t, ∀ x ∈ O, HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x` using `fun t x hx => ((h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => Φ (t, x)) (F' := fun x t => pX Φ (t, x)) (s := closedBall x₀ (ε / 2)) (bound := (Icc (-T) T).indicator fun _ => C) (closedBall_mem_nhds _ (by linarith)) ?_ (h.integrable hx₀) ((h.deriv hO).cont_line hx₀).aestronglyMe …` and prove the remaining obligations. Use `filter_upwards [hO.mem_nhds hx₀] with x hx using (h.cont_line hx).aestronglyMeasurable`. Use `Filter.Eventually.of_forall fun t x hx => ?_` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ Icc (-T) T`.

Rewrite using `[indicator_of_mem ht]`. Conclude with `hC (t, x) ⟨ht, hx⟩`. Rewrite using `[indicator_of_notMem ht, (h.deriv hO).2 t x ?_, norm_zero]`. Assume the negation of the conclusion as `hc`. Conclude with `ht (abs_le.1 (not_lt.1 hc))`.

Conclude with `(integrableOn_const (by simp)).integrable_indicator measurableSet_Icc`. Conclude with `Filter.Eventually.of_forall fun t x hx => hdiff t x (hsub hx)`.
-/
theorem Good.hasFDerivAt [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x₀ : H}
    (hx₀ : x₀ ∈ O) : HasFDerivAt (fun x => ∫ t, Φ (t, x)) (∫ t, pX Φ (t, x₀)) x₀ := by
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hO x₀ hx₀
  have hsub : closedBall x₀ (ε / 2) ⊆ O := (closedBall_subset_ball (by linarith)).trans hε
  have hK : IsCompact (Icc (-T) T ×ˢ closedBall x₀ (ε / 2)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : Icc (-T) T ×ˢ closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ O := fun q hq => ⟨mem_univ _, hsub hq.2⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((h.deriv hO).1.continuousOn.mono hKsub)
  have hdiff : ∀ t, ∀ x ∈ O, HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := fun t x hx =>
    ((h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => Φ (t, x)) (F' := fun x t => pX Φ (t, x)) (s := closedBall x₀ (ε / 2))
    (bound := (Icc (-T) T).indicator fun _ => C) (closedBall_mem_nhds _ (by linarith)) ?_ (h.integrable hx₀)
    ((h.deriv hO).cont_line hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hO.mem_nhds hx₀] with x hx using (h.cont_line hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t x hx => ?_
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]
      exact hC (t, x) ⟨ht, hx⟩
    · rw [indicator_of_notMem ht, (h.deriv hO).2 t x ?_, norm_zero]
      by_contra hc
      exact ht (abs_le.1 (not_lt.1 hc))
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  · exact Filter.Eventually.of_forall fun t x hx => hdiff t x (hsub hx)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `W _ _ _ Φ T h`. Conclude with `contDiffOn_zero.2 fun x hx => (h.hasFDerivAt hO hx).continuousAt.continuousWithinAt`. Consider the case `succ k ih`.

Introduce `W _ _ _ Φ T h`. Rewrite using `[show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast, contDiffOn_succ_iff_fderiv_of_isOpen hO]`. Use `⟨fun x hx => (h.hasFDerivAt hO hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩` and prove the remaining obligations. Conclude with `(ih (pX Φ) T (h.deriv hO)).congr fun x hx => (h.hasFDerivAt hO hx).fderiv`.
-/
theorem integral_good_contDiffOn (hO : IsOpen O) (k : ℕ) : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (Φ : ℝ × H → W) (T : ℝ), Good O Φ T → ContDiffOn ℝ k (fun x => ∫ t, Φ (t, x)) O := by
  induction k with
  | zero =>
    intro W _ _ _ Φ T h
    exact contDiffOn_zero.2 fun x hx => (h.hasFDerivAt hO hx).continuousAt.continuousWithinAt
  | succ k ih =>
    intro W _ _ _ Φ T h
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast, contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (h.hasFDerivAt hO hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (pX Φ) T (h.deriv hO)).congr fun x hx => (h.hasFDerivAt hO hx).fderiv

/- English proof (translation)
The claim follows from `contDiffOn_infty.2 fun k => integral_good_contDiffOn hO k Φ T h`.
-/
theorem good_smooth [CompleteSpace W] (hO : IsOpen O) (Φ : ℝ × H → W) (T : ℝ) (h : Good O Φ T) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, Φ (t, x)) O :=
  contDiffOn_infty.2 fun k => integral_good_contDiffOn hO k Φ T h

/- English proof (translation)
Rewrite using `[(h.hasFDerivAt hO hx).fderiv, ContinuousLinearMap.integral_apply (((h.deriv hO).integrable hx))]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Establish `hd : DifferentiableAt ℝ Φ (t, x)` using `(h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)`. Establish `e : HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x` using `hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)`. Use `show pX Φ (t, x) v = fderiv ℝ (fun y => Φ (t, y)) x v`.

Rewrite using `[e.fderiv]`.
-/
theorem good_fderiv_apply [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H}
    (hx : x ∈ O) (v : H) : fderiv ℝ (fun x => ∫ t, Φ (t, x)) x v = ∫ t, fderiv ℝ (fun y => Φ (t, y)) x v := by
  rw [(h.hasFDerivAt hO hx).fderiv, ContinuousLinearMap.integral_apply (((h.deriv hO).integrable hx))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hd : DifferentiableAt ℝ Φ (t, x) :=
    (h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)
  have e : HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  show pX Φ (t, x) v = fderiv ℝ (fun y => Φ (t, y)) x v
  rw [e.fderiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
