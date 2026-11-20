import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem trFin_pf : TrFin := by
  intro V B _ _ _ L w e h
  classical
  have hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b := by
    rintro ⟨_, v, rfl⟩
    exact h v
  let A : LinearMap.range L →ₗ[ℂ] (B → ℂ) :=
    LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype
  let c : (B → ℂ) →ₗ[ℂ] LinearMap.range L :=
    L.rangeRestrict.comp (Fintype.linearCombination ℂ w)
  have hA : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro r hr0
    apply Subtype.ext
    rw [hr r]
    have hz : ∀ b, e b (r : V) = 0 := fun b => congrFun hr0 b
    simp [hz]
  haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA
  have hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A := by
    ext r
    have h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b) := by
      simp [c, A, Fintype.linearCombination_apply]
    rw [LinearMap.comp_apply, h1, ← hr r]
    rfl
  rw [hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
