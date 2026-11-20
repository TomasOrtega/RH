import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OKOpen

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_coeff {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (i : ℕ) :
    Continuous fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i := by
  let b := Module.finBasis F A.K
  have h : (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) =
      fun z => (LinearMap.toMatrix b b (Algebra.lmul F A.K z)).charpoly.coeff i := by
    funext z; rw [LinearMap.charpoly_toMatrix]
  rw [h]
  refine (contCoeff _ i).comp ?_
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hl : (fun z : A.K => LinearMap.toMatrix b b (Algebra.lmul F A.K z) r s) =
      fun z => (b.coord r) (z * b s) := by
    funext z; simp [LinearMap.toMatrix_apply]
  rw [hl]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord r).comp (LinearMap.mulRight F (b s)))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  have hset : A.OK = ⋂ i : Fin (Module.finrank F A.K + 1),
      (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Et.OK, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h i; exact h i
    · intro h i
      by_cases hi : i ≤ Module.finrank F A.K
      · exact h ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
        simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage (continuous_coeff A i)

end GlobalTheory.JR.OKOpen
