import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

/- English proof (translation)
Introduce `V _ _ _ _ k T hk`. Take `⟨-, w1, w2, w3⟩` from `avSpec (shF V)`. Take `⟨a1, a2, -⟩` from `w3 wR w1`. Establish `cl` using `fun s t hs ht => cutLaws (V := V) s t hs ht`. Use `⟨Real.exp |T| * ‖k‖, fun ρ hρ => ?_⟩` and prove the remaining obligations.

Establish `e` using `DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Ioi T) measurableSet_Icc.compl measurableSet_Ioi).1 ((shF V).av wR k)`. Rewrite `e` using `[ContinuousLinearMap.comp_apply]`. Rewrite using `[e]`. Distinguish the cases in `h : |T| ≤ ρ`. Establish `e2 : (Icc (-ρ) ρ)ᶜ ∩ Ioi T = Ioi ρ`.

Use extensionality with `x`. Use `abs_le.1 h` as an intermediate fact. Simplify using `only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioi, not_and_or, not_le]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨h1 | h1, h2⟩ <;> linarith`.

Conclude with `fun h1 => ⟨Or.inr h1, by linarith⟩`. Rewrite using `[e2, (a1 k).2]`. Use `erw [← (cut V (Ioi ρ)).integral_comp_comm (a1 k).1]`. Establish `ib : Integrable fun t => (Iic (T - ρ)).indicator Real.exp t * ‖k‖` using `((integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_Iic _)).mul_const _`. Use `(norm_integral_le_of_norm_le ib (Eventually.of_forall fun t => ?_)).trans ?_` and prove the remaining obligations.

Rewrite using `[map_smul, norm_smul]`. Distinguish the cases in `ht : t ≤ T - ρ`. Rewrite using `[indicator_of_mem (mem_Iic.2 ht)]`. Use `mul_le_mul ?_ (((cl _ univ measurableSet_Ioi .univ).2.2.2.2.2.1 _).trans_eq ((shF V).norm t k)) (norm_nonneg _) (Real.exp_pos _).le` and prove the remaining obligations. Use `(norm_indicator_le_norm_self _ _).trans_eq ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `h1` using `DFunLike.congr_fun ((cl (Ioi (ρ + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) k`. Simplify using `only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h1`. Establish `h2` using `DFunLike.congr_fun (cl (Ioi (ρ + t)) (Iic T) measurableSet_Ioi measurableSet_Iic).1 k`. Rewrite `h2` using `[ContinuousLinearMap.comp_apply, hk, Ioi_inter_Iic, Ioc_eq_empty (by linarith [not_le.1 ht]), (cl univ univ .univ .univ).2.2.2.2.1]`.

Establish `h3 : cut V (Ioi ρ) ((shF V).U t k) = 0` using `by show cut V (Ioi ρ) (sh V t k) = 0`. Rewrite using `[← h1, h2]`. Simplify using the standard rewrite rules. Rewrite using `[h3, indicator_of_notMem (by simpa using ht)]; simp`. Rewrite using `[integral_mul_const, integral_indicator measurableSet_Iic, integral_exp_Iic, mul_right_comm, ← Real.exp_add] gcongr`.

Combine the linear relations using `[le_abs_self T]`. Use `((cl _ univ (measurableSet_Icc.compl.inter measurableSet_Ioi) .univ).2.2.2.2.2.1 _).trans ?_` and prove the remaining obligations. Use `(((shF V).av wR).le_of_opNorm_le (a2.trans_eq w2) k).trans ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, ← Real.exp_add]`. Use `gcongr`.

Conclude with `Real.one_le_exp (by linarith [not_le.1 h])`.
-/
theorem UpperTheory.V.Z.IntegralApplyAeEq.resTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (k : L V) (T : ℝ), cut V (Iic T) k = k → Tail (cut V (Ioi T) ((shF V).av wR k)) := by
  intro V _ _ _ _ k T hk
  obtain ⟨-, w1, w2, w3⟩ := avSpec (shF V)
  obtain ⟨a1, a2, -⟩ := w3 wR w1
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  refine ⟨Real.exp |T| * ‖k‖, fun ρ hρ => ?_⟩
  have e := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Ioi T) measurableSet_Icc.compl measurableSet_Ioi).1 ((shF V).av wR k)
  rw [ContinuousLinearMap.comp_apply] at e
  rw [e]
  by_cases h : |T| ≤ ρ
  · have e2 : (Icc (-ρ) ρ)ᶜ ∩ Ioi T = Ioi ρ := by
      ext x
      have := abs_le.1 h
      simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioi, not_and_or, not_le]
      constructor
      · rintro ⟨h1 | h1, h2⟩ <;> linarith
      · exact fun h1 => ⟨Or.inr h1, by linarith⟩
    rw [e2, (a1 k).2]
    erw [← (cut V (Ioi ρ)).integral_comp_comm (a1 k).1]
    have ib : Integrable fun t => (Iic (T - ρ)).indicator Real.exp t * ‖k‖ :=
      ((integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_Iic _)).mul_const _
    refine (norm_integral_le_of_norm_le ib (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [map_smul, norm_smul]
      by_cases ht : t ≤ T - ρ
      · rw [indicator_of_mem (mem_Iic.2 ht)]
        refine mul_le_mul ?_ (((cl _ univ measurableSet_Ioi .univ).2.2.2.2.2.1 _).trans_eq ((shF V).norm t k)) (norm_nonneg _)
          (Real.exp_pos _).le
        refine (norm_indicator_le_norm_self _ _).trans_eq ?_
        simp
      · have h1 := DFunLike.congr_fun ((cl (Ioi (ρ + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) k
        simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h1
        have h2 := DFunLike.congr_fun (cl (Ioi (ρ + t)) (Iic T) measurableSet_Ioi measurableSet_Iic).1 k
        rw [ContinuousLinearMap.comp_apply, hk, Ioi_inter_Iic, Ioc_eq_empty (by linarith [not_le.1 ht]),
          (cl univ univ .univ .univ).2.2.2.2.1] at h2
        have h3 : cut V (Ioi ρ) ((shF V).U t k) = 0 := by
          show cut V (Ioi ρ) (sh V t k) = 0
          rw [← h1, h2]; simp
        rw [h3, indicator_of_notMem (by simpa using ht)]; simp
    · rw [integral_mul_const, integral_indicator measurableSet_Iic, integral_exp_Iic, mul_right_comm, ← Real.exp_add]
      gcongr
      linarith [le_abs_self T]
  · refine ((cl _ univ (measurableSet_Icc.compl.inter measurableSet_Ioi) .univ).2.2.2.2.2.1 _).trans ?_
    refine (((shF V).av wR).le_of_opNorm_le (a2.trans_eq w2) k).trans ?_
    rw [mul_right_comm, ← Real.exp_add]
    gcongr
    exact Real.one_le_exp (by linarith [not_le.1 h])
