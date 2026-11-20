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
A detailed English derivation is pending.
-/
theorem casKHighest : CasKHighest := compactCasimirOnHighestWeight_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumSq : SumSq := sumOfSquaresIdentity_holds
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem rhoStd : RhoStd := half_sum_roots_standard

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem omEigen : OmEigen := omega_eigenvalue_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uGap : UGap := unitary_spectral_gap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem growthIter : GrowthIter := iteratedGrowthBound_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorRadius : TaylorRadius := taylorSummable_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem casCentral : CasCentral := casimir_central_holds

end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem epowCov : EpowCov := generatorPowCovariance_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etrCentral : EtrCentral := generatorTraceCentral_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem diagChar : DiagChar := diagChar_of generatorPowDiagRecursion_holds
end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem charId : CharId := characteristicIdentity_holds
end Formalism.REAL

namespace Formalism.REAL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qSkewRow : QSkewRow := quantumMinorRowSkew_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qSkewCol : QSkewCol := quantumMinorColSkew_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qDetHW : QDetHW := quantumDetHighestWeight_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qDetCentral : QDetCentral := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qComatrix : QComatrix := qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
end Formalism.REAL
