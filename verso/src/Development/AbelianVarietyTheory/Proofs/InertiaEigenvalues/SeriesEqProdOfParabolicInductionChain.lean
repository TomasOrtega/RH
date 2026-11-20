import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInductionStatement

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerSys

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem has_prod_of_inInd : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  intro g _ S π L hL
  induction hL with
  | nil π h0 _ =>
    intro F hF
    refine ⟨[], List.Forall₂.nil, ?_⟩
    obtain ⟨n, r⟩ := π
    simp only at h0
    subst h0
    obtain ⟨v, -, hv⟩ := hF
    have hne : S.e 0 F ≠ 0 := by
      intro h
      apply hv
      simp [h, actK]
    obtain ⟨hm, hd, -⟩ := S.label 0 F hne
    simpa using Polynomial.eq_one_of_monic_natDegree_zero hm hd
  | cons π σ ρ L hπ _ _ hmap ih =>
    intro F hF
    obtain ⟨f, f', hf, hf', rfl⟩ :=
      GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction g S π.1 σ.1 ρ.1 _ π.2.ρ _ _ σ.2.ρ ρ.2.ρ hπ hmap F hF
    obtain ⟨fs, hfs, rfl⟩ := ih f hf
    exact ⟨f' :: fs, List.Forall₂.cons hf' hfs, by simp [mul_comm]⟩

end GlobalTheory.SerSys
