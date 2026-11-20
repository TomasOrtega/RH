import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineSquarePushforwardUniformStatement

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder

namespace GlobalTheory.LineCos

def splitLin (d : ℕ) : V (d + 1) ≃ₗ[ℝ] (Fin d → ℂ) × ℂ where
  toFun z := (base z, fib z)
  invFun p := WithLp.toLp 2 (Fin.snoc p.1 p.2 : Fin (d + 1) → ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [fib]
    · simp [base]
  right_inv p := by
    ext i
    · simp [base]
    · simp [fib]

/- English proof (translation)
Set `e : V (d + 1) ≃L[ℝ] (Fin d → ℂ) × ℂ` to `(splitLin d).toContinuousLinearEquiv`. Set `em : V (d + 1) ≃ᵐ (Fin d → ℂ) × ℂ` to `e.toHomeomorph.toMeasurableEquiv`. Use `haveI : Measure.IsAddHaarMeasure (Measure.map e (volume : Measure (V (d + 1)))) := inferInstance`. Use `haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin d → ℂ) × ℂ)) := Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin d → ℂ)) (volume : Measure ℂ)`. Establish `h` using `Measure.isAddLeftInvariant_eq_smul (Measure.map e (volume : Measure (V (d + 1)))) (volume : Measure ((Fin d → ℂ) × ℂ))`.

Use `⟨Measure.addHaarScalarFactor (Measure.map e (volume : Measure (V (d + 1)))) (volume : Measure ((Fin d → ℂ) × ℂ)), ENNReal.coe_ne_top, fun F => ?_⟩` and prove the remaining obligations. Establish `h1 : ∫⁻ z, F z = ∫⁻ p, F (e.symm p) ∂(Measure.map e (volume : Measure (V (d + 1))))`. Use `lintegral_map_equiv (μ := (volume : Measure (V (d + 1)))) (fun p => F (e.symm p)) em` as an intermediate fact. Simplify `this.symm` using `[em]`. Rewrite using `[h1]`.

Use `conv_lhs => rw [h]`. Rewrite using `[lintegral_smul_measure]`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Conclude with `lintegral_prod_le (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ)) (fun p => F (e.symm p))`.
-/
theorem exists_lintegral_le_iterated (d : ℕ) : ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : V (d + 1) → ENNReal,
    ∫⁻ z, F z ≤ c * ∫⁻ b : Fin d → ℂ, ∫⁻ x : ℂ, F ((splitLin d).symm (b, x)) := by
  let e : V (d + 1) ≃L[ℝ] (Fin d → ℂ) × ℂ := (splitLin d).toContinuousLinearEquiv
  let em : V (d + 1) ≃ᵐ (Fin d → ℂ) × ℂ := e.toHomeomorph.toMeasurableEquiv
  haveI : Measure.IsAddHaarMeasure (Measure.map e (volume : Measure (V (d + 1)))) := inferInstance
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin d → ℂ) × ℂ)) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin d → ℂ)) (volume : Measure ℂ)
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ))
  refine ⟨Measure.addHaarScalarFactor (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ)), ENNReal.coe_ne_top, fun F => ?_⟩
  have h1 : ∫⁻ z, F z = ∫⁻ p, F (e.symm p) ∂(Measure.map e (volume : Measure (V (d + 1)))) := by
    have := lintegral_map_equiv (μ := (volume : Measure (V (d + 1)))) (fun p => F (e.symm p)) em
    simpa [em] using this.symm
  rw [h1]
  conv_lhs => rw [h]
  rw [lintegral_smul_measure]
  refine mul_le_mul_right ?_ _
  exact lintegral_prod_le (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ)) (fun p => F (e.symm p))

def fsDensity (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  G.det.re / (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)

/- English proof (translation)
The claim follows from `div_pos (Complex.pos_iff.1 hG.det_pos).1 (mul_pos Real.pi_pos (pow_pos (re_hform_pos hG (lineVec_ne_zero s x)) 2))`.
-/
theorem fsDensity_pos (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < fsDensity s G x :=
  div_pos (Complex.pos_iff.1 hG.det_pos).1
    (mul_pos Real.pi_pos (pow_pos (re_hform_pos hG (lineVec_ne_zero s x)) 2))

/- English proof (translation)
Establish `he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O` using `fun i j => (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)`. Establish `hx : Continuous (fun z : V (d + 1) => fib z)`. Unfold `fib`. Use `fun_prop`. Establish `hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i)` using `fun i => by`.

Consider the cases of `s`. Use `fin_cases i`. Conclude with `continuous_const`. Conclude with `hx`. Use `fin_cases i`.

Conclude with `hx`. Conclude with `continuous_const`. Establish `hh : ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))) O`. Unfold `hform`. Use `continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `(((hw i).mul ((Complex.continuous_conj).comp (hw j))).continuousOn).mul (he i j)`. Establish `hdet : ContinuousOn (fun z => (G (base z)).det) O` using `(Continuous.matrix_det continuous_id).comp_continuousOn hc`. Use `(Complex.continuous_re.comp_continuousOn hdet).div (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hh).pow 2)) fun z hz => ?_` and prove the remaining obligations. Conclude with `(mul_pos Real.pi_pos (pow_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) 2)).ne'`.
-/
theorem continuousOn_fsDensity {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => fsDensity s (G (base z)) (fib z)) O := by
  have he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hx : Continuous (fun z : V (d + 1) => fib z) := by
    unfold fib
    fun_prop
  have hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact hx
    · fin_cases i
      · exact hx
      · exact continuous_const
  have hh : ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))) O := by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hw j))).continuousOn).mul (he i j)
  have hdet : ContinuousOn (fun z => (G (base z)).det) O :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine (Complex.continuous_re.comp_continuousOn hdet).div
    (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hh).pow 2)) fun z hz => ?_
  exact (mul_pos Real.pi_pos (pow_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) 2)).ne'

/- English proof (translation)
Establish `hw : ∀ i, Continuous (fun x : ℂ => lineVec s x i)` using `fun i => by`. Consider the cases of `s`. Use `fin_cases i`. Conclude with `continuous_const`. Conclude with `continuous_id`.

Use `fin_cases i`. Conclude with `continuous_id`. Conclude with `continuous_const`. Establish `hh : ∀ (b : ℂ → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) → Continuous (fun z => hform G (lineVec s z) (b z))` using `fun b hb => by`. Unfold `hform`.

Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((hw i).mul ((Complex.continuous_conj).comp (hb j))).mul continuous_const`. Conclude with `((hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2).measurable.div ((Complex.continuous_re.comp (hh _ hw)).mul continuous_const).measurable`.
-/
theorem measurable_cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have hw : ∀ i, Continuous (fun x : ℂ => lineVec s x i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact continuous_id
    · fin_cases i
      · exact continuous_id
      · exact continuous_const
  have hh : ∀ (b : ℂ → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      Continuous (fun z => hform G (lineVec s z) (b z)) := fun b hb => by
    unfold hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hw i).mul ((Complex.continuous_conj).comp (hb j))).mul continuous_const
  exact ((hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2).measurable.div
    ((Complex.continuous_re.comp (hh _ hw)).mul continuous_const).measurable

/- English proof (translation)
Rewrite using `[← GlobalTheory.T.cosine_square_pushforward_uniform G s hG, Measure.map_apply (measurable_cosSq s G) hA, withDensity_apply _ (measurable_cosSq s G hA), lintegral_indicator (measurable_cosSq s G hA)]`. Both sides reduce to the same expression.
-/
theorem lintegral_fsDensity_indicator (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ x, (cosSq s G ⁻¹' A).indicator (fun x => ENNReal.ofReal (fsDensity s G x)) x =
      volume.restrict (Icc (0 : ℝ) 1) A := by
  rw [← GlobalTheory.T.cosine_square_pushforward_uniform G s hG, Measure.map_apply (measurable_cosSq s G) hA,
    withDensity_apply _ (measurable_cosSq s G hA), lintegral_indicator (measurable_cosSq s G hA)]
  rfl

/- English proof (translation)
Take `⟨c, hc, hF⟩` from `exists_lintegral_le_iterated d`. Establish `hfs` using `continuousOn_fsDensity s hG hp`. Establish `h0` using `fsDensity_pos s (hp z₀ hz₀) (fib z₀)`. Use `set R : ℝ := (|ρ z₀| + 1) / fsDensity s (G (base z₀)) (fib z₀) with hR`. Establish `hR0 : 0 ≤ R` using `by positivity`.

Establish `hb : Continuous (fun z : V (d + 1) => base z)`. Unfold `base`. Use `fun_prop`. Set `K : Set (Fin d → ℂ)` to `Metric.ball (base z₀) 1`. Set `N : Set (V (d + 1))` to `(T ∩ (fun z => R * fsDensity s (G (base z)) (fib z) - ρ z) ⁻¹' Ioi 0) ∩ (fun z => base z) ⁻¹' K`.

Establish `hN : IsOpen N` using `(((continuousOn_const.mul hfs).sub hρ).isOpen_inter_preimage hT isOpen_Ioi).inter (Metric.isOpen_ball.preimage hb)`. Establish `hNT : N ⊆ T` using `fun z hz => hz.1.1`. Use `⟨N, hN, ⟨⟨hz₀, ?_⟩, Metric.mem_ball_self one_pos⟩, hNT, c * (ENNReal.ofReal R * volume K), ENNReal.mul_ne_top hc (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne), ?_⟩` and prove the remaining obligations. Use `show 0 < R * fsDensity s (G (base z₀)) (fib z₀) - ρ z₀`. Rewrite using `[hR, div_mul_cancel₀ _ h0.ne']`.

Combine the linear relations using `[le_abs_self (ρ z₀)]`. Use `set f : V (d + 1) → ℝ := fun z => cosSq s (G (base z)) (fib z) with hf`. Establish `hf' : Measurable (N.piecewise f 0)` using `((continuousOn_cosSq s hG hp).mono hNT).measurable_piecewise continuousOn_const hN.measurableSet`. Establish `hae : f =ᵐ[(volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)] N.piecewise f 0`. Use `(withDensity_absolutelyContinuous _ _).ae_le ?_` and prove the remaining obligations.

Use `filter_upwards [ae_restrict_mem hN.measurableSet] with z hz`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hz]`. Rewrite using `[Measure.map_congr hae, Measure.le_iff]`. Introduce `A hA`. Rewrite using `[Measure.map_apply hf' hA, withDensity_apply _ (hf' hA), Measure.restrict_restrict (hf' hA), ← lintegral_indicator ((hf' hA).inter hN.measurableSet), Measure.smul_apply, smul_eq_mul]`.

Use `(hF _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc c]`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Establish `key : ∀ b : Fin d → ℂ, ∫⁻ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z)) ((splitLin d).symm (b, x)) ≤ K.indicator (fun _ => ENNReal.ofReal R * volume.restrict (Icc (0 : ℝ) 1) A) b`. Introduce `b`.

Establish `hbase : ∀ x, base ((splitLin d).symm (b, x)) = b` using `fun x => congrArg Prod.fst ((splitLin d).apply_symm_apply (b, x))`. Establish `hfib : ∀ x, fib ((splitLin d).symm (b, x)) = x` using `fun x => congrArg Prod.snd ((splitLin d).apply_symm_apply (b, x))`. Distinguish the cases in `hex : ∃ x, (splitLin d).symm (b, x) ∈ N`. Take `⟨x₀, hx₀⟩` from `hex`. Establish `hbK : b ∈ K`.

Use `hx₀.2` as an intermediate fact. Rewrite `this` using `[mem_preimage, hbase]`. Then use the resulting hypothesis. Establish `hGb : (G b).PosDef`. Use `hp _ (hNT hx₀)` as an intermediate fact. Rewrite `this` using `[hbase]`. Then use the resulting hypothesis.

Rewrite using `[indicator_of_mem hbK, ← lintegral_fsDensity_indicator s hGb hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : (splitLin d).symm (b, x) ∈ N.piecewise f 0 ⁻¹' A ∩ N`. Establish `h1 : x ∈ cosSq s (G b) ⁻¹' A`. Use `hx.1` as an intermediate fact.

Rewrite `this` using `[mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx.2, hf]`. Simplify `this` using `only [hbase, hfib, mem_preimage]`. Establish `h2 : 0 < R * fsDensity s (G b) x - ρ ((splitLin d).symm (b, x))`. Use `hx.2.1.2` as an intermediate fact. Simplify `this` using `only [mem_preimage, hbase, hfib, mem_Ioi]`.

Simplify using `only [indicator_of_mem hx, indicator_of_mem h1]`. Rewrite using `[← ENNReal.ofReal_mul hR0]`. Conclude with `ENNReal.ofReal_le_ofReal (by linarith)`. Simplify using `only [indicator_of_notMem hx]`. Conclude with `zero_le`.

Establish `: ∀ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z)) ((splitLin d).symm (b, x)) = 0` using `fun x => indicator_of_notMem (fun h => hex ⟨x, h.2⟩) _`. Simplify using `only [this, lintegral_zero]`. Conclude with `zero_le`. Use `(lintegral_mono key).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_map_cosSq_le (d : ℕ) (T : Set (V (d + 1))) (ρ : V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : V (d + 1))
    (hT : IsOpen T) (hz₀ : z₀ ∈ T) (hρ : ContinuousOn ρ T) (hG : ContinuousOn (fun z => G (base z)) T)
    (hp : ∀ z ∈ T, (G (base z)).PosDef) :
    ∃ N : Set (V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => cosSq s (G (base z)) (fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_lintegral_le_iterated d
  have hfs := continuousOn_fsDensity s hG hp
  have h0 := fsDensity_pos s (hp z₀ hz₀) (fib z₀)
  set R : ℝ := (|ρ z₀| + 1) / fsDensity s (G (base z₀)) (fib z₀) with hR
  have hR0 : 0 ≤ R := by positivity
  have hb : Continuous (fun z : V (d + 1) => base z) := by
    unfold base
    fun_prop
  let K : Set (Fin d → ℂ) := Metric.ball (base z₀) 1
  let N : Set (V (d + 1)) := (T ∩ (fun z => R * fsDensity s (G (base z)) (fib z) - ρ z) ⁻¹' Ioi 0) ∩
    (fun z => base z) ⁻¹' K
  have hN : IsOpen N :=
    (((continuousOn_const.mul hfs).sub hρ).isOpen_inter_preimage hT isOpen_Ioi).inter
      (Metric.isOpen_ball.preimage hb)
  have hNT : N ⊆ T := fun z hz => hz.1.1
  refine ⟨N, hN, ⟨⟨hz₀, ?_⟩, Metric.mem_ball_self one_pos⟩, hNT, c * (ENNReal.ofReal R * volume K),
    ENNReal.mul_ne_top hc (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne), ?_⟩
  · show 0 < R * fsDensity s (G (base z₀)) (fib z₀) - ρ z₀
    rw [hR, div_mul_cancel₀ _ h0.ne']
    linarith [le_abs_self (ρ z₀)]
  set f : V (d + 1) → ℝ := fun z => cosSq s (G (base z)) (fib z) with hf
  have hf' : Measurable (N.piecewise f 0) :=
    ((continuousOn_cosSq s hG hp).mono hNT).measurable_piecewise continuousOn_const hN.measurableSet
  have hae : f =ᵐ[(volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)] N.piecewise f 0 := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem hN.measurableSet] with z hz
    rw [Set.piecewise_eq_of_mem _ _ _ hz]
  rw [Measure.map_congr hae, Measure.le_iff]
  intro A hA
  rw [Measure.map_apply hf' hA, withDensity_apply _ (hf' hA), Measure.restrict_restrict (hf' hA),
    ← lintegral_indicator ((hf' hA).inter hN.measurableSet), Measure.smul_apply, smul_eq_mul]
  refine (hF _).trans ?_
  rw [mul_assoc c]
  refine mul_le_mul_right ?_ _
  have key : ∀ b : Fin d → ℂ, ∫⁻ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
      ((splitLin d).symm (b, x)) ≤
      K.indicator (fun _ => ENNReal.ofReal R * volume.restrict (Icc (0 : ℝ) 1) A) b := by
    intro b
    have hbase : ∀ x, base ((splitLin d).symm (b, x)) = b := fun x =>
      congrArg Prod.fst ((splitLin d).apply_symm_apply (b, x))
    have hfib : ∀ x, fib ((splitLin d).symm (b, x)) = x := fun x =>
      congrArg Prod.snd ((splitLin d).apply_symm_apply (b, x))
    by_cases hex : ∃ x, (splitLin d).symm (b, x) ∈ N
    · obtain ⟨x₀, hx₀⟩ := hex
      have hbK : b ∈ K := by
        have := hx₀.2
        rwa [mem_preimage, hbase] at this
      have hGb : (G b).PosDef := by
        have := hp _ (hNT hx₀)
        rwa [hbase] at this
      rw [indicator_of_mem hbK, ← lintegral_fsDensity_indicator s hGb hA,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      by_cases hx : (splitLin d).symm (b, x) ∈ N.piecewise f 0 ⁻¹' A ∩ N
      · have h1 : x ∈ cosSq s (G b) ⁻¹' A := by
          have := hx.1
          rw [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx.2, hf] at this
          simpa only [hbase, hfib, mem_preimage] using this
        have h2 : 0 < R * fsDensity s (G b) x - ρ ((splitLin d).symm (b, x)) := by
          have := hx.2.1.2
          simpa only [mem_preimage, hbase, hfib, mem_Ioi] using this
        simp only [indicator_of_mem hx, indicator_of_mem h1]
        rw [← ENNReal.ofReal_mul hR0]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · simp only [indicator_of_notMem hx]
        exact zero_le
    · have : ∀ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
          ((splitLin d).symm (b, x)) = 0 := fun x => indicator_of_notMem (fun h => hex ⟨x, h.2⟩) _
      simp only [this, lintegral_zero]
      exact zero_le
  refine (lintegral_mono key).trans (le_of_eq ?_)
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  ring

end GlobalTheory.LineCos
