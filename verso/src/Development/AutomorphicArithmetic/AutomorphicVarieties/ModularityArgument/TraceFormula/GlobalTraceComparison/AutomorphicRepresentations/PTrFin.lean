import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Introduce `V B _ _ _ L w e h`. Establish `hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b`. Introduce and unpack `⟨_, v, rfl⟩`. Conclude with `h v`. Set `A : LinearMap.range L →ₗ[ℂ] (B → ℂ)` to `LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype`.

Set `c : (B → ℂ) →ₗ[ℂ] LinearMap.range L` to `L.rangeRestrict.comp (Fintype.linearCombination ℂ w)`. Establish `hA : Function.Injective A`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr0`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hr r]`. Establish `hz : ∀ b, e b (r : V) = 0` using `fun b => congrFun hr0 b`. Simplify using `[hz]`. Use `haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA`. Establish `hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A`.

Use extensionality with `r`. Establish `h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b)`. Simplify using `[c, A, Fintype.linearCombination_apply]`. Rewrite using `[LinearMap.comp_apply, h1, ← hr r]`. Both sides reduce to the same expression.

Rewrite using `[hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]`. Simplify using `only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]`.
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
