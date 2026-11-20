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
Use `haveI := IsModuleTopology.toContinuousSMul ℚ_[l] LL`. Establish `h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun c => c • (1 : LL)`. Use function extensionality and compare the values at `Algebra.algebraMap_eq_smul_one`. Rewrite using `[h]`. Conclude with `continuous_id.smul continuous_const`.
-/
theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[l] LL) := by
  haveI := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun c => c • (1 : LL) :=
    funext Algebra.algebraMap_eq_smul_one
  rw [h]
  exact continuous_id.smul continuous_const

/- English proof (translation)
Establish `hU : IsOpen ((algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL))` using `hA.preimage continuous_algebraMap_padic`. Establish `h0 : (0 : ℚ_[l]) ∈ (algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL)`. Simplify using `[A.zero_mem]`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hU 0 h0`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := l))`.

Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)`. Establish `hu : (u : ℚ_[l]) = ((u.appr n : ℕ) : ℚ_[l]) + (w : ℚ_[l]) * (l : ℚ_[l]) ^ n`. Use `congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hw` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `-this`.

Establish `h1 : algebraMap ℚ_[l] LL ((w : ℚ_[l]) * (l : ℚ_[l]) ^ n) ∈ A`. Apply `hball` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu, map_add, map_natCast]`.

Conclude with `A.add_mem (natCast_mem A _) h1`.
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
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowerImageOpen.main`. Consider the case `exact _root_.GlobalTheory.PowerImageOpen.main`. Consider the case `(apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowerImageOpen.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowerImageOpen.main ..)`.
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
