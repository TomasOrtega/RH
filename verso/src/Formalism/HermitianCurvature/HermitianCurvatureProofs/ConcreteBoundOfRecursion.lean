import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

noncomputable section

/- English proof (translation)
Introduce `hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e`. Conclude with `⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e, hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e, hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e, hCut E W …`.
-/
theorem real_inputs_by_parts : C.RealInputsConcreteOfParts := by
  intro hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  exact ⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e,
    hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e,
    hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e,
    hCut E Wp Wq S H Vt hPG Kr hK0 Th e⟩

/- English proof (translation)
The claim follows from `real_inputs_by_parts embedding_facts euclidean_frame trace_dual_alt lattice_facts_general gram_positive_semidefinite words_pos_of_parts wave_estimate_of_integral poisson_input_of_parts lift_estimate_of_base block_estimate_of_base level_zero_estimate_product cutoff_of_parts`.
-/
theorem real_inputs_concrete_holds : C.RealInputsConcrete :=
  real_inputs_by_parts embedding_facts euclidean_frame trace_dual_alt
    lattice_facts_general gram_positive_semidefinite words_pos_of_parts wave_estimate_of_integral
    poisson_input_of_parts lift_estimate_of_base block_estimate_of_base level_zero_estimate_product
    cutoff_of_parts

/- English proof (translation)
Introduce `hTA hPT hPJ hPSJ hRI C₁ C₄ hC₁ hC₄`. Take `⟨C, C', hCC⟩` from `hTA C₁ C₄ hC₁ hC₄`. Use `⟨C, C', ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ S jv cE Kr hK0 Th e Θ H _ _ _ Vt c hf hg1 hg2 hΘ hC'Θ hsmall hSz hP hG hI hP1 hP23 hT hLE _ hPG hKr hA2 hEB hDom hLS hA4 R`. Take `⟨hGram, hWP, hWave, hPI, hLift, hBlock, hE, hCut⟩` from `hRI E Wp Wq S jv H Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e`.

Take `⟨V, _, _, _, _, _, ι, _, π, Λ, hD, hZ, emb, dmap, hbij, hFr, hWF⟩` from `hPI`. Establish `hPS : (S.mkData Kr hK0 Th e).PoissonStep` using `@hPSJ hPT hPJ E S.W _ (S.mkData Kr hK0 Th e) V _ _ _ _ _ ι _ π hbij Λ hD hZ emb dmap hFr hWF`. Establish `hr : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 1`. Break down `le_or_gt 0 ((C / Θ) ^ S.f) with hx | hx` into its components or cases. Use the polynomial consequences of the given equalities and inequalities.

Establish `: (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hx.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : 4 ≤ (S.mkData Kr hK0 Th e).K` using `by show 4 ≤ Kst`. Unfold `Kst`. Evaluate the numerical expressions.

Conclude with `hCC E S.W (S.mkData Kr hK0 Th e) Θ (∏ v, jv v) H Vt c hK hf hΘ hC'Θ hr hSz hGram hKr hWP hA2 hEB hDom hWave hPS hLift hBlock hLS hE hCut hA4 R`.
-/
theorem concrete_bound_of_recursion : C.TheoremAConcreteOfParts := by
  intro hTA hPT hPJ hPSJ hRI C₁ C₄ hC₁ hC₄
  obtain ⟨C, C', hCC⟩ := hTA C₁ C₄ hC₁ hC₄
  refine ⟨C, C', ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ S jv cE Kr hK0 Th e Θ H _ _ _ Vt c hf hg1 hg2 hΘ hC'Θ hsmall hSz hP hG hI hP1
    hP23 hT hLE _ hPG hKr hA2 hEB hDom hLS hA4 R
  obtain ⟨hGram, hWP, hWave, hPI, hLift, hBlock, hE, hCut⟩ :=
    hRI E Wp Wq S jv H Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  obtain ⟨V, _, _, _, _, _, ι, _, π, Λ, hD, hZ, emb, dmap, hbij, hFr, hWF⟩ := hPI
  have hPS : (S.mkData Kr hK0 Th e).PoissonStep :=
    @hPSJ hPT hPJ E S.W _ (S.mkData Kr hK0 Th e) V _ _ _ _ _ ι _ π hbij Λ hD hZ emb dmap hFr hWF
  have hr : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 1 := by
    rcases le_or_gt 0 ((C / Θ) ^ S.f) with hx | hx
    · nlinarith
    · have : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hx.le
      linarith
  have hK : 4 ≤ (S.mkData Kr hK0 Th e).K := by
    show 4 ≤ Kst
    unfold Kst
    norm_num
  exact hCC E S.W (S.mkData Kr hK0 Th e) Θ (∏ v, jv v) H Vt c hK hf hΘ hC'Θ hr hSz hGram hKr hWP hA2 hEB hDom
    hWave hPS hLift hBlock hLS hE hCut hA4 R

/- English proof (translation)
The claim follows from `concrete_bound_of_recursion theorem_a_after poisson_summation_level_statement poisson_joint poisson_level_joint real_inputs_concrete_holds`.
-/
theorem concrete_bound_holds : C.TheoremAConcrete :=
  concrete_bound_of_recursion theorem_a_after poisson_summation_level_statement poisson_joint
    poisson_level_joint real_inputs_concrete_holds

end

end Formalism.FourierDecayAlt.P
