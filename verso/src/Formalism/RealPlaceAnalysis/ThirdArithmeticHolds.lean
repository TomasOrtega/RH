import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.RealPlaceAnalysis.StatementD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId

namespace Formalism.REAL

/- English proof (translation)
The claim follows from `compactCasimirOnHighestWeight_holds`.
-/
theorem casKHighest : CasKHighest := compactCasimirOnHighestWeight_holds
/- English proof (translation)
The claim follows from `sumOfSquaresIdentity_holds`.
-/
theorem sumSq : SumSq := sumOfSquaresIdentity_holds
/- English proof (translation)
Introduce `V _ _ n ε E μ w hGl hU hKH`. Establish `hK` using `compactCasimirOnHighestWeight_holds V n ε E μ w hGl hKH`. Establish `hU' : IsUnitary ε (fun a b => if ε a = ε b then E a b else 0)`. Introduce `a b x y`. Distinguish the cases in `h : ε a = ε b`.

Simplify using `only [if_pos h, if_pos h.symm]`. Conclude with `hU a b x y`. Establish `h' : ¬ ε b = ε a` using `fun e => h e.symm`. Simplify using `only [if_neg h, if_neg h', LinearMap.zero_apply, inner_zero_left, inner_zero_right, mul_zero]`. Establish `hCas' : Cas (fun a b => if ε a = ε b then E a b else 0) = CasK ε E`.

Unfold `Cas CasK`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Distinguish the cases in `h : ε a = ε b`. Simplify using `only [if_pos h, if_pos h.symm]`. Establish `h' : ¬ ε b = ε a` using `fun e => h e.symm`.

Simplify using `only [if_neg h, if_neg h', zero_mul]`. Establish `hCasK' : CasK ε (fun a b => if ε a = ε b then E a b else 0) = CasK ε E`. Unfold `CasK`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Distinguish the cases in `h : ε a = ε b`.

Simplify using `only [if_pos h, if_pos h.symm]`. Simplify using `only [if_neg h]`. Establish `hS : (∑ a, ∑ b, ‖E a b w‖ ^ 2) = (∑ a, ∑ b, ‖(if ε a = ε b then E a b else 0) w‖ ^ 2) + ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b w‖ ^ 2)`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : ε a = ε b <;> simp [h]`. Establish `hSc` using `congrArg (fun r : ℝ => (r : ℂ)) hS`. Establish `h1` using `sumOfSquaresIdentity_holds V n ε E w hU`.

Establish `h2` using `sumOfSquaresIdentity_holds V n ε (fun a b => if ε a = ε b then E a b else 0) w hU'`. Rewrite `h2` using `[hCas', hCasK']`. Apply the tactic sequence `first | rw [two_nsmul] at h1 h2 | rw [two_smul] at h1 h2`. Rewrite `h2` using `[add_sub_cancel_right, hK, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Rewrite `h1` using `[LinearMap.sub_apply, LinearMap.add_apply, inner_sub_right, inner_add_right, hK, inner_smul_right, inner_self_eq_norm_sq_to_K]`.

Move the coercions through the operations in `at h1 h2 hSc ⊢`. Take the linear combination `h1 - hSc - h2`.
-/
theorem wdCas : WDCas := by
  intro V _ _ n ε E μ w hGl hU hKH
  have hK := compactCasimirOnHighestWeight_holds V n ε E μ w hGl hKH
  have hU' : IsUnitary ε (fun a b => if ε a = ε b then E a b else 0) := by
    intro a b x y
    by_cases h : ε a = ε b
    · simp only [if_pos h, if_pos h.symm]
      exact hU a b x y
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp only [if_neg h, if_neg h', LinearMap.zero_apply, inner_zero_left, inner_zero_right,
        mul_zero]
  have hCas' : Cas (fun a b => if ε a = ε b then E a b else 0) = CasK ε E := by
    unfold Cas CasK
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : ε a = ε b
    · simp only [if_pos h, if_pos h.symm]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp only [if_neg h, if_neg h', zero_mul]
  have hCasK' : CasK ε (fun a b => if ε a = ε b then E a b else 0) = CasK ε E := by
    unfold CasK
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : ε a = ε b
    · simp only [if_pos h, if_pos h.symm]
    · simp only [if_neg h]
  have hS : (∑ a, ∑ b, ‖E a b w‖ ^ 2) =
      (∑ a, ∑ b, ‖(if ε a = ε b then E a b else 0) w‖ ^ 2) +
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b w‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : ε a = ε b <;> simp [h]
  have hSc := congrArg (fun r : ℝ => (r : ℂ)) hS
  have h1 := sumOfSquaresIdentity_holds V n ε E w hU
  have h2 := sumOfSquaresIdentity_holds V n ε (fun a b => if ε a = ε b then E a b else 0) w hU'
  rw [hCas', hCasK'] at h2
  first | rw [two_nsmul] at h1 h2 | rw [two_smul] at h1 h2
  rw [add_sub_cancel_right, hK, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  rw [LinearMap.sub_apply, LinearMap.add_apply, inner_sub_right, inner_add_right, hK,
    inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  push_cast at h1 h2 hSc ⊢
  linear_combination h1 - hSc - h2
/- English proof (translation)
The claim follows from `half_sum_roots_standard`.
-/
theorem rhoStd : RhoStd := half_sum_roots_standard

/- English proof (translation)
The claim follows from `omega_eigenvalue_holds`.
-/
theorem omEigen : OmEigen := omega_eigenvalue_holds
/- English proof (translation)
The claim follows from `unitary_spectral_gap`.
-/
theorem uGap : UGap := unitary_spectral_gap
/- English proof (translation)
The claim follows from `iteratedGrowthBound_holds`.
-/
theorem growthIter : GrowthIter := iteratedGrowthBound_holds
/- English proof (translation)
The claim follows from `taylorSummable_holds`.
-/
theorem taylorRadius : TaylorRadius := taylorSummable_holds
/- English proof (translation)
The claim follows from `casimir_central_holds`.
-/
theorem casCentral : CasCentral := casimir_central_holds

end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
The claim follows from `generatorPowCovariance_holds`.
-/
theorem epowCov : EpowCov := generatorPowCovariance_holds
/- English proof (translation)
The claim follows from `generatorTraceCentral_holds`.
-/
theorem etrCentral : EtrCentral := generatorTraceCentral_holds
/- English proof (translation)
The claim follows from `diagChar_of generatorPowDiagRecursion_holds`.
-/
theorem diagChar : DiagChar := diagChar_of generatorPowDiagRecursion_holds
end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
The claim follows from `characteristicIdentity_holds`.
-/
theorem charId : CharId := characteristicIdentity_holds
end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
The claim follows from `quantumMinorRowSkew_holds`.
-/
theorem qSkewRow : QSkewRow := quantumMinorRowSkew_holds
/- English proof (translation)
The claim follows from `quantumMinorColSkew_holds`.
-/
theorem qSkewCol : QSkewCol := quantumMinorColSkew_holds
/- English proof (translation)
The claim follows from `quantumDetHighestWeight_holds`.
-/
theorem qDetHW : QDetHW := quantumDetHighestWeight_holds
/- English proof (translation)
The claim follows from `qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds`.
-/
theorem qDetCentral : QDetCentral := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
/- English proof (translation)
The claim follows from `qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds`.
-/
theorem qComatrix : QComatrix := qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
end Formalism.REAL
