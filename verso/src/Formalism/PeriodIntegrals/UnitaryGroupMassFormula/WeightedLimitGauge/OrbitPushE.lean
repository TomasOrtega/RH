import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_opBeta (k : ℕ) (a : Fin k) : Continuous (fun q : TrE k => opBeta k q a) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  unfold opBeta
  exact ((hq _).add ((hq _).mul continuous_const)).div_const _

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem continuous_opGen (k r : ℕ) : Continuous (opGen k r : TrE k → Mat k r) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  unfold opGen
  split_ifs
  all_goals first
    | exact continuous_const
    | exact continuous_opBeta k _
    | exact (continuous_opBeta k _).star
    | exact (hq none).mul continuous_const

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_opEmap (k r : ℕ) (T' : ℝ) :
    Continuous (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) := by

  letI : NormedRing (Mat k r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mat k r) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Mat k r) := Matrix.linftyOpNormedAlgebra
  have h1 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q)) :=
    NormedSpace.exp_continuous.comp (continuous_opGen k r)
  have h2 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') :=
    h1.matrix_mulVec continuous_const
  unfold opCo
  exact (continuous_pi (fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp h2)).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp h2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem opEMeas : OpEMeas := by

  intro k r T' ρ
  unfold opE
  have hball : Metric.ball (0 : TrE k) ρ = ⋃ n : ℕ, Metric.closedBall 0 (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion, dist_zero_right]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hball, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun n => ?_)
  exact ((isCompact_closedBall _ _).image (continuous_opEmap k r T')).isClosed.measurableSet

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem normSq_sum_eq (k : ℕ) (y : EuclideanSpace ℂ (Fin k)) : ∑ i, Complex.normSq (y i) = ‖y‖ ^ 2 := by

  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl (fun i _ => by rw [Complex.sq_norm])

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hypPar_mem (k : ℕ) (T' : ℝ) (hT' : 0 < T') (q : EuclideanSpace ℂ (Fin k) × ℝ) :
    hypPar k T' q ∈ hypS k T' := by

  have h1 : Complex.normSq (Complex.exp (q.2 * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  simp only [hypS, hypPar, Set.mem_setOf_eq]
  rw [normSq_sum_eq, Complex.normSq_mul, Complex.normSq_ofReal, h1, mul_one,
    Real.mul_self_sqrt (by positivity)]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hypLF : HypLF := by
  intro k T' hT'
  have hcont : Continuous (hypPar k T') := by
    unfold hypPar
    refine (continuous_pi (fun i => ?_)).prodMk ?_
    · exact (EuclideanSpace.proj i).continuous.comp continuous_fst
    · refine (Complex.continuous_ofReal.comp ?_).mul ?_
      · exact Real.continuous_sqrt.comp (((continuous_norm.comp continuous_fst).pow 2).add continuous_const)
      · exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hmeas : Measurable (hypPar k T') := hcont.measurable
  have hSc : IsClosed (hypS k T') := by
    have h1 : Continuous (fun p : (Fin k → ℂ) × ℂ => ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2) :=
      (continuous_finset_sum _ (fun i _ => Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_fst))).sub
        (Complex.continuous_normSq.comp continuous_snd)
    exact isClosed_eq h1 continuous_const
  constructor
  · unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hSc.measurableSet.compl]
    have h2 : hypPar k T' ⁻¹' (hypS k T')ᶜ = ∅ := by
      ext q
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact hypPar_mem k T' hT' q
    rw [h2, measure_empty, smul_zero]
  · intro C hC
    obtain ⟨R, hR⟩ := (hC.image continuous_fst).isBounded.exists_norm_le
    have hsub : hypPar k T' ⁻¹' C ⊆
        Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ := by
      intro q hq
      refine ⟨?_, Set.mem_univ _⟩
      have h1 : ‖(hypPar k T' q).1‖ ≤ R := hR _ ⟨_, hq, rfl⟩
      have h2 : ∀ i, ‖q.1 i‖ ≤ R := fun i => le_trans (norm_le_pi_norm (hypPar k T' q).1 i) h1
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖q.1 i‖ ^ 2 ≤ ∑ i : Fin k, R ^ 2 :=
            Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h2 i) 2)
        _ = k * R ^ 2 := by simp
    unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hC.isClosed.measurableSet, smul_eq_mul]
    refine ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero) ?_
    calc _ ≤ (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
          (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ) :=
          measure_mono hsub
      _ = volume (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2))) *
          volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by
        apply ENNReal.mul_lt_top measure_closedBall_lt_top
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top

end PI.RhsWLim.W
