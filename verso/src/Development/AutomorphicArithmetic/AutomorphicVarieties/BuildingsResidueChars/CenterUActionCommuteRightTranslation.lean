import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CapOpCommuteRightTranslation

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.centerU_action_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∀ z ∈ (isExpLieAlgebra K n).centerU, ∀ g, Commute (uAction z) (rt (K := K) (n := n) g) := by
  intro K _ _ n z hz g
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have hinf : Commute (uAction z) (rtInf (archPart g)) := by
    have hsub : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤
        Subalgebra.centralizer ℂ {rtInf (archPart g)} := by
      rw [Algebra.adjoin_le_iff]
      rintro x ⟨τ, u, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro y rfl
      exact (UpperTheory.capOp_commute_rightTranslation K n ι D τ u (archPart g)).eq.symm
    have hm := hsub (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz)
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm _ rfl).symm
  have hfin : Commute (uAction z) (rtFin (finPart g)) := by
    refine LinearMap.ext fun φ => ?_
    exact uAction_rtFin z (finPart g) φ
  exact hinf.mul_right hfin
