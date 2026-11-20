import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.S.capAct :
    UpperTheory.V.Cj.S.CapAct := by
  intro E _ _ _ a t u
  have h0 : ∀ w : Cm.UC E a, Commute (cap (a := a) t u) (Cm.uC E a w) := fun w => by
    rw [← Cm.uC_capC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (Cm.capC_mem_center t u) w).symm (Cm.uC E a)
  have h1 : ∀ g, Commute (cap (a := a) t u) (rt E a g) := fun g =>
    GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (Cm.cap_mem_Zalg t u) g
  refine ⟨h1, fun o => ?_, fun z => ?_, fun t' u' => ?_⟩
  · cases o with
    | fin k => exact h1 _
    | cpt k => exact h1 _
    | lie X =>
      have := h0 (Cm.ιC E a X)
      rw [Cm.uC_ιC] at this
      exact this
  · have := h0 (1 ⊗ₜ z)
    rwa [Cm.uC_tmul, one_smul] at this
  · have := h0 (Cm.capC t' u')
    rwa [Cm.uC_capC] at this
