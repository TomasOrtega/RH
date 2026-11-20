import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.S.capOfEig :
    UpperTheory.V.Cj.S.CapOfEig := by
  intro E _ _ _ a φ h0 hc
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have key : ∀ t : E →+* ℂ, ∃ m : Multiset ℂ, Multiset.card m = a ∧
      ∀ u : ℂ, cap t u φ = (m.map (u + ·)).prod • φ := fun t => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) t) (((a : ℂ) - 1) / 2) φ f hf
    refine ⟨m, hm, fun u => ?_⟩
    obtain ⟨c, h1⟩ := hc t u
    have h2 : f (cap t u φ) = _ := h u
    rw [h1, map_smul, hf, smul_eq_mul, mul_one] at h2
    rw [h1, h2]
  choose m hm h using key
  exact ⟨m, fun t => ⟨hm t, h t⟩⟩
