import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint

noncomputable section

namespace GlobalTheory.FibrePolar

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

/- English proof (translation)
Use `haveI : ProperSpace V := FiniteDimensional.proper_real V`. Establish `hc0 : ∀ n : Measure V, n.restrict O Oᶜ = 0` using `fun n => by`. Rewrite using `[Measure.restrict_apply hO.measurableSet.compl]`. Simplify using the standard rewrite rules. Use `measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (hc0 _) (hc0 _) ?_` and prove the remaining obligations.

Introduce `φ hφ hc hs h0`. Take `⟨hi, hg⟩` from `h.2.2 φ hφ hc (hs.trans hU)`. Take `⟨hi', hg'⟩` from `h'.2.2 φ hφ hc (hs.trans hU')`. Use `⟨(hi β trivial).restrict, ?_⟩` and prove the remaining obligations. Establish `hφm : Measurable fun v => ENNReal.ofReal (φ v)` using `ENNReal.measurable_ofReal.comp hφ.measurable`.

Establish `hφ0 : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0`. Introduce `v hv`. Rewrite using `[image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]`. Establish `hr : ∀ n : Measure V, ∫⁻ v in O, ENNReal.ofReal (φ v) ∂n = ∫⁻ v, ENNReal.ofReal (φ v) ∂n` using `fun n => setLIntegral_eq_of_support_subset fun v hv => by`. Assume the negation of the conclusion as `hvO`.

Conclude with `hv (hφ0 v hvO)`. Rewrite using `[hr, hr]`. Establish `c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) Set.univ` using `(ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb => (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm`. Establish `c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) Set.univ` using `(ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb => (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm`. Establish `hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[volume.restrict Set.univ] (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b))`.

Use `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable MeasurableSet.univ) (c'.aemeasurable MeasurableSet.univ) fun S hS _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_univ, ← IsFibreFamily_lintegral_preimage hf hO hU h _ hφm hφ0 _ hS, ← IsFibreFamily_lintegral_preimage hf hO hU' h' _ hφm hφ0 _ hS]`. Conclude with `Measure.eqOn_open_of_ae_eq hae isOpen_univ c c' trivial`.
-/
theorem restrict_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U')
    (h : IsFibreFamily μ f id U (volume : Measure ℝ) Set.univ fib)
    (h' : IsFibreFamily μ f id U' (volume : Measure ℝ) Set.univ fib') :
    (fib β).restrict O = (fib' β).restrict O := by
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hc0 : ∀ n : Measure V, n.restrict O Oᶜ = 0 := fun n => by
    rw [Measure.restrict_apply hO.measurableSet.compl]; simp
  refine measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (hc0 _) (hc0 _) ?_
  intro φ hφ hc hs h0
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (hs.trans hU)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (hs.trans hU')
  refine ⟨(hi β trivial).restrict, ?_⟩
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hφ0 : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hr : ∀ n : Measure V, ∫⁻ v in O, ENNReal.ofReal (φ v) ∂n =
      ∫⁻ v, ENNReal.ofReal (φ v) ∂n := fun n =>
    setLIntegral_eq_of_support_subset fun v hv => by
      by_contra hvO; exact hv (hφ0 v hvO)
  rw [hr, hr]
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) Set.univ :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) Set.univ :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[volume.restrict Set.univ]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable MeasurableSet.univ)
      (c'.aemeasurable MeasurableSet.univ) fun S hS _ => ?_
    rw [Measure.restrict_univ,
      ← IsFibreFamily_lintegral_preimage hf hO hU h _ hφm hφ0 _ hS,
      ← IsFibreFamily_lintegral_preimage hf hO hU' h' _ hφm hφ0 _ hS]
  exact Measure.eqOn_open_of_ae_eq hae isOpen_univ c c' trivial

variable {P Q P' Q' : ℕ}

/- English proof (translation)
Unfold `qf`. Use `fun_prop`.
-/
theorem continuous_qf : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

def glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim p.1 p.2

/- English proof (translation)
Simplify using `[glue]`.
-/
@[simp] theorem glue_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') :
    glue e p (e none) = p.1 := by simp [glue]

/- English proof (translation)
Simplify using `[glue]`.
-/
@[simp] theorem glue_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : glue e p (e (some i)) = p.2 i := by simp [glue]

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Take `⟨j, rfl⟩` from `e.surjective i`. Break down `j with _ | j` into its components or cases. Simplify using `only [glue_none]`. Use `fun_prop`.

Simplify using `only [glue_some]`. Use `fun_prop`.
-/
theorem continuous_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (glue e) := by
  refine continuous_pi fun i => ?_
  obtain ⟨j, rfl⟩ := e.surjective i
  rcases j with _ | j
  · simp only [glue_none]; fun_prop
  · simp only [glue_some]; fun_prop

/- English proof (translation)
Use `⟨(continuous_glue e).measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[volume_pi (α := fun _ : Fin P ⊕ Fin Q => ℂ)]`. Use `(Measure.pi_eq fun s hs => ?_).symm` and prove the remaining obligations. Rewrite using `[Measure.map_apply (continuous_glue e).measurable (MeasurableSet.univ_pi hs)]`. Establish `: glue e ⁻¹' Set.pi Set.univ s = s (e none) ×ˢ Set.pi Set.univ (fun i => s (e (some i)))`.

Use extensionality with `p`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]`. Rewrite using `[e.surjective.forall, Option.forall]`. Simplify using the standard rewrite rules. Rewrite using `[this, Measure.prod_prod, volume_pi_pi, ← e.prod_comp, Fintype.prod_option]`.
-/
theorem measurePreserving_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    MeasurePreserving (glue e) ((volume : Measure ℂ).prod volume) volume := by
  refine ⟨(continuous_glue e).measurable, ?_⟩
  rw [volume_pi (α := fun _ : Fin P ⊕ Fin Q => ℂ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (continuous_glue e).measurable (MeasurableSet.univ_pi hs)]
  have : glue e ⁻¹' Set.pi Set.univ s =
      s (e none) ×ˢ Set.pi Set.univ (fun i => s (e (some i))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]
    rw [e.surjective.forall, Option.forall]
    simp
  rw [this, Measure.prod_prod, volume_pi_pi, ← e.prod_comp, Fintype.prod_option]

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Simplify using `using norm_le_pi_norm (glue e p) (e (some i))`.
-/
theorem norm_le_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') :
    ‖p.2‖ ≤ ‖glue e p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa using norm_le_pi_norm (glue e p) (e (some i))

/- English proof (translation)
Rewrite using `[qf_eq_sum, qf_eq_sum, ← e.sum_comp, Fintype.sum_option]`. Simplify using `only [glue_none, glue_some, he _]`.
-/
theorem qf_glue {e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)} (he : SignCompat e)
    (p : ℂ × Sp P' Q') : qf (glue e p) = sg (e none) * Complex.normSq p.1 + qf p.2 := by
  rw [qf_eq_sum, qf_eq_sum, ← e.sum_comp, Fintype.sum_option]
  simp only [glue_none, glue_some, he _]

def pt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (a : ℝ × (ℝ × Sp P' Q')) : Sp P Q :=
  glue e ((Real.sqrt (sg (e none) * (a.1 - qf a.2.2)) : ℂ) *
    Complex.exp ((a.2.1 : ℂ) * Complex.I), a.2.2)

/- English proof (translation)
Use `@continuous_qf P' Q'` as an intermediate fact. Conclude with `(continuous_glue e).comp (by fun_prop)`.
-/
theorem continuous_pt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Continuous (pt e) := by
  have := @continuous_qf P' Q'
  exact (continuous_glue e).comp (by fun_prop)

/- English proof (translation)
Establish `: sg (e none) * (sg (e none) - qf p.2) = 1 - sg (e none) * qf p.2`. Apply the tactic sequence `rcases sg_eq (e none) with h | h <;> rw [h] <;> ring`. Simplify using `only [pt, this]`. Both sides reduce to the same expression.
-/
theorem pt_sg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℝ × Sp P' Q') :
    pt e (sg (e none), p) = polarPt e p := by
  have : sg (e none) * (sg (e none) - qf p.2) = 1 - sg (e none) * qf p.2 := by
    rcases sg_eq (e none) with h | h <;> rw [h] <;> ring
  simp only [pt, this]
  rfl

def base (P' Q' : ℕ) : Measure (ℝ × Sp P' Q') :=
  ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)).prod volume

def fam (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ) : Measure (Sp P Q) :=
  ((2 : ℝ≥0∞) ^ (P' + Q')) •
    ((base P' Q').map fun p => pt e (t, p)).restrict {y | y (e none) ≠ 0}

/- English proof (translation)
Establish `hO : IsOpen {y : Sp P Q | y (e none) ≠ 0}` using `isOpen_ne_fun (continuous_apply _) continuous_const`. Use `set O := {y : Sp P Q | y (e none) ≠ 0} with hOdef`. Establish `hk : ((2 : ℝ≥0∞) ^ (P' + Q')) ≠ ⊤` using `by simp`. Establish `hpt` using `continuous_pt e`. Establish `hpt' : ∀ t, Continuous fun p => pt e (t, p)` using `fun t => hpt.comp (by fun_prop)`.

Establish `hε` using `sg_eq (e none)`. Use `⟨fun t => ?_, fun φ hφ => ?_, fun φ hφ hs ht => ?_⟩` and prove the remaining obligations. Establish `hS : MeasurableSet (qf ⁻¹' {id t} ∩ O)ᶜ` using `((continuous_qf.measurable (measurableSet_singleton t)).inter hO.measurableSet).compl`. Rewrite using `[fam, Measure.smul_apply, Measure.restrict_apply hS, Measure.map_apply (hpt' t).measurable (hS.inter hO.measurableSet)]`. Establish `: (fun p => pt e (t, p)) ⁻¹' ((qf ⁻¹' {id t} ∩ O)ᶜ ∩ O) = ∅`.

Use `Set.eq_empty_of_forall_notMem fun p hp => hp.1 ⟨?_, hp.2⟩` and prove the remaining obligations. Establish `h : 0 < sg (e none) * (t - qf p.2)`. Assume the negation of the conclusion as `h`. Conclude with `hp.2 (by simp [pt, Real.sqrt_eq_zero_of_nonpos (not_lt.1 h)])`. Establish `hn : Complex.normSq ((Real.sqrt (sg (e none) * (t - qf p.2)) : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I)) = sg (e none) * (t - qf p.2)`.

Rewrite using `[map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt h.le, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `qf (glue e _) = t`. Rewrite using `[qf_glue he, hn]`. Apply the tactic sequence `rcases hε with h1 | h1 <;> rw [h1] <;> ring`.

Rewrite using `[this, measure_empty, smul_zero]`. Establish `hG : Measurable (O.indicator φ)` using `hφ.indicator hO.measurableSet`. Establish `hJ` using `hG.comp hpt.measurable`. Establish `e1 : ∀ t, ∫⁻ v, φ v ∂(fam e t) = (2 : ℝ≥0∞) ^ (P' + Q') * ∫⁻ y, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, O.indicator φ (pt e (t, θ, y))` using `fun t => by`. Rewrite using `[fam, lintegral_smul_measure, ← lintegral_indicator hO.measurableSet, lintegral_map hG (hpt' t).measurable, base, lintegral_prod_symm' (fun p => O.indicator φ (pt e (t, p))) (hG.comp (hpt' t).measurable), smul_eq_mul]`.

Simplify using `only [e1]`. Rewrite using `[lintegral_const_mul' _ _ hk, ← lintegral_indicator hO.measurableSet, dx, lintegral_smul_measure, smul_eq_mul, card_eq e, pow_succ, mul_assoc]`. Use `congr 1`. Rewrite using `[← (measurePreserving_glue e).lintegral_comp hG, lintegral_prod_symm' (fun a => O.indicator φ (glue e a)) (hG.comp (continuous_glue e).measurable), ← lintegral_const_mul' _ _ (by simp)]`. Use `symm`.

Rewrite using `[lintegral_lintegral_swap]`. Use `lintegral_congr fun y => Eq.symm ?_` and prove the remaining obligations. Rewrite using `[lintegral_complex_eq_lintegral_sqrt_mul_exp (sg (e none)) (qf y) hε (fun z => O.indicator φ (glue e (z, y))) (hG.comp ((continuous_glue e).measurable.comp measurable_prodMk_right)) (Set.indicator_of_notMem (by simp [hOdef]) _), ← lintegral_const_mul' _ _ (by simp)]`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul' _ _ (by simp), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]`.

Both sides reduce to the same expression. Use `Measurable.aemeasurable ?_` and prove the remaining obligations. Use `Measurable.lintegral_prod_right' (f := fun a : (ℝ × Sp P' Q') × ℝ => O.indicator φ (pt e (a.1.1, a.2, a.1.2))) ?_` and prove the remaining obligations. Conclude with `hJ.comp (by fun_prop)`. Take `⟨C, hC⟩` from `hφ.bounded_above_of_compact_support hs`.

Take `⟨R, hR⟩` from `hs.isCompact.isBounded.subset_closedBall 0`. Set `b : ℝ × Sp P' Q' → ℝ` to `(Set.univ ×ˢ Metric.closedBall 0 R).indicator fun _ => C`. Establish `hb : Integrable b (base P' Q')`. Use `(integrable_indicator_iff (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)).2 (integrableOn_const ?_ (by simp))` and prove the remaining obligations. Rewrite using `[base, Measure.prod_prod]`.

Conclude with `ENNReal.mul_ne_top (measure_ne_top _ _) measure_closedBall_lt_top.ne`. Establish `hle : ∀ t p, ‖φ (pt e (t, p))‖ ≤ b p` using `fun t p => by`. Distinguish the cases in `h : p ∈ (Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Sp P' Q') R`. Simplify using `only [b, Set.indicator_of_mem h]`. Conclude with `hC _`.

Simplify using `only [b, Set.indicator_of_notMem h]`. Rewrite using `[image_eq_zero_of_notMem_tsupport (f := φ), norm_zero]`. Introduce `h1`. Conclude with `h ⟨trivial, mem_closedBall_zero_iff.2 ((norm_le_glue e (_, p.2)).trans (mem_closedBall_zero_iff.1 (hR h1)))⟩`. Establish `hm : ∀ t, AEStronglyMeasurable (fun p => φ (pt e (t, p))) (base P' Q')` using `fun t => (hφ.comp (hpt' t)).aestronglyMeasurable`.

Prove the components needed by the constructor for the conclusion. Introduce `t _`. Use `Integrable.smul_measure (Integrable.restrict ?_) hk` and prove the remaining obligations. Rewrite using `[integrable_map_measure hφ.aestronglyMeasurable (hpt' t).aemeasurable]`. Conclude with `hb.mono' (hm t) (ae_of_all _ (hle t))`.

Establish `e2 : ∀ t, ∫ x, φ x ∂(fam e t) = ((2 : ℝ≥0∞) ^ (P' + Q')).toReal * ∫ p, φ (pt e (t, p)) ∂(base P' Q')` using `fun t => by`. Rewrite using `[fam, integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (ht h)), integral_map (hpt' t).aemeasurable hφ.aestronglyMeasurable, smul_eq_mul]`. Simplify using `only [e2]`. Conclude with `(continuous_const.mul (continuous_of_dominated hm (fun t => ae_of_all _ (hle t)) hb (ae_of_all _ fun p => hφ.comp (hpt.comp (by fun_prop))))).continuousOn`.
-/
theorem isFibreFamily_fam {e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)} (he : SignCompat e) :
    IsFibreFamily (dx P Q) (qf : Sp P Q → ℝ) id {y | y (e none) ≠ 0} (volume : Measure ℝ)
      Set.univ (fam e) := by
  have hO : IsOpen {y : Sp P Q | y (e none) ≠ 0} :=
    isOpen_ne_fun (continuous_apply _) continuous_const
  set O := {y : Sp P Q | y (e none) ≠ 0} with hOdef
  have hk : ((2 : ℝ≥0∞) ^ (P' + Q')) ≠ ⊤ := by simp
  have hpt := continuous_pt e
  have hpt' : ∀ t, Continuous fun p => pt e (t, p) := fun t => hpt.comp (by fun_prop)
  have hε := sg_eq (e none)
  refine ⟨fun t => ?_, fun φ hφ => ?_, fun φ hφ hs ht => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id t} ∩ O)ᶜ :=
      ((continuous_qf.measurable (measurableSet_singleton t)).inter hO.measurableSet).compl
    rw [fam, Measure.smul_apply, Measure.restrict_apply hS,
      Measure.map_apply (hpt' t).measurable (hS.inter hO.measurableSet)]
    have : (fun p => pt e (t, p)) ⁻¹' ((qf ⁻¹' {id t} ∩ O)ᶜ ∩ O) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => hp.1 ⟨?_, hp.2⟩
      have h : 0 < sg (e none) * (t - qf p.2) := by
        by_contra h
        exact hp.2 (by simp [pt, Real.sqrt_eq_zero_of_nonpos (not_lt.1 h)])
      have hn : Complex.normSq ((Real.sqrt (sg (e none) * (t - qf p.2)) : ℂ) *
          Complex.exp ((p.1 : ℂ) * Complex.I)) = sg (e none) * (t - qf p.2) := by
        rw [map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt h.le, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]; simp
      change qf (glue e _) = t
      rw [qf_glue he, hn]
      rcases hε with h1 | h1 <;> rw [h1] <;> ring
    rw [this, measure_empty, smul_zero]
  · have hG : Measurable (O.indicator φ) := hφ.indicator hO.measurableSet
    have hJ := hG.comp hpt.measurable
    have e1 : ∀ t, ∫⁻ v, φ v ∂(fam e t) = (2 : ℝ≥0∞) ^ (P' + Q') *
        ∫⁻ y, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, O.indicator φ (pt e (t, θ, y)) := fun t => by
      rw [fam, lintegral_smul_measure, ← lintegral_indicator hO.measurableSet,
        lintegral_map hG (hpt' t).measurable, base,
        lintegral_prod_symm' (fun p => O.indicator φ (pt e (t, p)))
          (hG.comp (hpt' t).measurable), smul_eq_mul]
    simp only [e1]
    rw [lintegral_const_mul' _ _ hk, ← lintegral_indicator hO.measurableSet, dx,
      lintegral_smul_measure, smul_eq_mul, card_eq e, pow_succ, mul_assoc]
    congr 1
    rw [← (measurePreserving_glue e).lintegral_comp hG,
      lintegral_prod_symm' (fun a => O.indicator φ (glue e a))
        (hG.comp (continuous_glue e).measurable), ← lintegral_const_mul' _ _ (by simp)]
    symm
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun y => Eq.symm ?_
      rw [lintegral_complex_eq_lintegral_sqrt_mul_exp (sg (e none)) (qf y) hε
        (fun z => O.indicator φ (glue e (z, y)))
        (hG.comp ((continuous_glue e).measurable.comp measurable_prodMk_right))
        (Set.indicator_of_notMem (by simp [hOdef]) _), ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun t => ?_
      rw [lintegral_const_mul' _ _ (by simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
      rfl
    · refine Measurable.aemeasurable ?_
      refine Measurable.lintegral_prod_right' (f := fun a : (ℝ × Sp P' Q') × ℝ =>
        O.indicator φ (pt e (a.1.1, a.2, a.1.2))) ?_
      exact hJ.comp (by fun_prop)
  · obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hs
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    let b : ℝ × Sp P' Q' → ℝ := (Set.univ ×ˢ Metric.closedBall 0 R).indicator fun _ => C
    have hb : Integrable b (base P' Q') := by
      refine (integrable_indicator_iff
        (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)).2
        (integrableOn_const ?_ (by simp))
      rw [base, Measure.prod_prod]
      exact ENNReal.mul_ne_top (measure_ne_top _ _) measure_closedBall_lt_top.ne
    have hle : ∀ t p, ‖φ (pt e (t, p))‖ ≤ b p := fun t p => by
      by_cases h : p ∈ (Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Sp P' Q') R
      · simp only [b, Set.indicator_of_mem h]; exact hC _
      · simp only [b, Set.indicator_of_notMem h]
        rw [image_eq_zero_of_notMem_tsupport (f := φ), norm_zero]
        intro h1
        exact h ⟨trivial, mem_closedBall_zero_iff.2 ((norm_le_glue e (_, p.2)).trans
          (mem_closedBall_zero_iff.1 (hR h1)))⟩
    have hm : ∀ t, AEStronglyMeasurable (fun p => φ (pt e (t, p))) (base P' Q') := fun t =>
      (hφ.comp (hpt' t)).aestronglyMeasurable
    constructor
    · intro t _
      refine Integrable.smul_measure (Integrable.restrict ?_) hk
      rw [integrable_map_measure hφ.aestronglyMeasurable (hpt' t).aemeasurable]
      exact hb.mono' (hm t) (ae_of_all _ (hle t))
    · have e2 : ∀ t, ∫ x, φ x ∂(fam e t) =
          ((2 : ℝ≥0∞) ^ (P' + Q')).toReal * ∫ p, φ (pt e (t, p)) ∂(base P' Q') := fun t => by
        rw [fam, integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (ht h)),
          integral_map (hpt' t).aemeasurable hφ.aestronglyMeasurable, smul_eq_mul]
      simp only [e2]
      exact (continuous_const.mul (continuous_of_dominated hm (fun t => ae_of_all _ (hle t)) hb
        (ae_of_all _ fun p => hφ.comp (hpt.comp (by fun_prop))))).continuousOn

/- English proof (translation)
Introduce `P Q P' Q' e he fib hfib S hS hS0`. Establish `hO : IsOpen {y : Sp P Q | y (e none) ≠ 0}` using `isOpen_ne_fun (continuous_apply _) continuous_const`. Establish `key` using `restrict_eq (dx P Q) qf {y | y (e none) ≠ 0} {x | x ≠ 0} _ fib (fam e) (sg (e none)) continuous_qf.measurable hO (fun y hy h0 => hy (congrFun h0 _)) subset_rfl hfib (isFibreFamily_fam he)`. Establish `hsub : S ⊆ {y | y (e none) ≠ 0}` using `hS0`. Establish `hm : Measurable fun p => pt e (sg (e none), p)` using `((continuous_pt e).comp (by fun_prop)).measurable`.

Rewrite using `[← Measure.restrict_eq_self _ hsub, key, Measure.restrict_eq_self _ hsub, fam, Measure.smul_apply, Measure.restrict_eq_self _ hsub, Measure.map_apply hm hS, smul_eq_mul, base, Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply (hm hS), ← Measure.volume_eq_prod]`. Use `congr 2`. Use extensionality with `p`. Simplify using `[pt_sg, and_comm]`.
-/
theorem fibre_eq_polar : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ fib : ℝ → Measure (Sp P Q), IsDxDq fib → ∀ S : Set (Sp P Q),
      MeasurableSet S → (∀ y ∈ S, y (e none) ≠ 0) →
      fib (sg (e none)) S = (2 : ℝ≥0∞) ^ (P' + Q') * (volume : Measure (ℝ × Sp P' Q'))
        {t | t.1 ∈ Set.Ioo (-Real.pi) Real.pi ∧ polarPt e t ∈ S} := by
  intro P Q P' Q' e he fib hfib S hS hS0
  have hO : IsOpen {y : Sp P Q | y (e none) ≠ 0} :=
    isOpen_ne_fun (continuous_apply _) continuous_const
  have key := restrict_eq (dx P Q) qf {y | y (e none) ≠ 0} {x | x ≠ 0} _ fib (fam e) (sg (e none))
    continuous_qf.measurable hO (fun y hy h0 => hy (congrFun h0 _)) subset_rfl hfib
    (isFibreFamily_fam he)
  have hsub : S ⊆ {y | y (e none) ≠ 0} := hS0
  have hm : Measurable fun p => pt e (sg (e none), p) :=
    ((continuous_pt e).comp (by fun_prop)).measurable
  rw [← Measure.restrict_eq_self _ hsub, key, Measure.restrict_eq_self _ hsub, fam,
    Measure.smul_apply, Measure.restrict_eq_self _ hsub, Measure.map_apply hm hS, smul_eq_mul,
    base, Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply (hm hS),
    ← Measure.volume_eq_prod]
  congr 2
  ext p
  simp [pt_sg, and_comm]

end GlobalTheory.FibrePolar
