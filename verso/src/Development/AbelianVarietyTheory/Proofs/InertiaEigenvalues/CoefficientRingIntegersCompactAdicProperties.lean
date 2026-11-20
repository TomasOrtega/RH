import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfBounded

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

section Open

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [IsModuleTopology ℚ_[l] LL]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[l] LL) := by
  haveI := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun c => c • (1 : LL) :=
    funext Algebra.algebraMap_eq_smul_one
  rw [h]
  exact continuous_id.smul continuous_const

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem padicInt_mem (A : Subring LL) (hA : IsOpen (A : Set LL)) (u : ℤ_[l]) :
    algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ A := by
  have hU : IsOpen ((algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL)) :=
    hA.preimage continuous_algebraMap_padic
  have h0 : (0 : ℚ_[l]) ∈ (algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL) := by
    simp [A.zero_mem]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := l))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : (u : ℚ_[l]) = ((u.appr n : ℕ) : ℚ_[l]) + (w : ℚ_[l]) * (l : ℚ_[l]) ^ n := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hw
    push_cast at this
    linear_combination -this
  have h1 : algebraMap ℚ_[l] LL ((w : ℚ_[l]) * (l : ℚ_[l]) ^ n) ∈ A := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖(w : ℚ_[l])‖ * ‖(l : ℚ_[l])‖ ^ n ≤ 1 * ‖(l : ℚ_[l])‖ ^ n :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one w) (by positivity)
      _ < ε := by rwa [one_mul]
  rw [hu, map_add, map_natCast]
  exact A.add_mem (natCast_mem A _) h1

end Open

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem good_coeff_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first
  | exact @_root_.GlobalTheory.PowerImageOpen.main
  | exact _root_.GlobalTheory.PowerImageOpen.main
  | (apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerImageOpen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerImageOpen.main ..)

end GlobalTheory.GoodCoeff
