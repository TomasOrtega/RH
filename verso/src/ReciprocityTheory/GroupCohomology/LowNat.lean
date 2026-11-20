import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.ContractNthCastAddCastSucc

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem lowNat_holds : LowNatStatement.{u} := by
  intro R _ G _ _ _ G' _ _ _ M M' P e₀ e₁ e₂ e₀' e₁' e₂' hL hL'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    have hw : M'.coch.d 0 (P.hom.Z 0 ⟨c, hc⟩).1 = 0 := (P.hom.Z 0 ⟨c, hc⟩).2
    have hc' : M.coch.d 0 c = 0 := hc
    change (e₀' (M'.coch.cls 0 (P.hom.Z 0 ⟨c, hc⟩).1 hw) : M'.V) =
      P.u (e₀ (M.coch.cls 0 c hc'))
    have h1 := hL'.1 (P.hom.Z 0 ⟨c, hc⟩).1 hw
    have h2 := hL.1 c hc'
    rw [h1, h2]
    show P.u (c.1 fun i => P.φ (![] i)) = P.u (c.1 ![])
    rw [show (fun i => P.φ (![] i)) = (![] : Fin 0 → G) from funext fun i => i.elim0]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.1 c hc
    have hw : M'.coch.d 1 (P.hom.Z 1 ⟨c, hc⟩).1 = 0 := (P.hom.Z 1 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.1 (P.hom.Z 1 ⟨c, hc⟩).1 hw
    change e₁' (M'.coch.cls 1 (P.hom.Z 1 ⟨c, hc⟩).1 hw) =
      P.h1 (e₁ (M.coch.cls 1 c hc))
    rw [he', he]
    unfold Pair.h1 pairH1DecompositionMap
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g] i)) = P.u (c.1 ![P.φ g])
    rw [show (fun i => P.φ (![g] i)) = ![P.φ g] from by funext i; fin_cases i; rfl]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.2 c hc
    have hw : M'.coch.d 2 (P.hom.Z 2 ⟨c, hc⟩).1 = 0 := (P.hom.Z 2 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.2 (P.hom.Z 2 ⟨c, hc⟩).1 hw
    change e₂' (M'.coch.cls 2 (P.hom.Z 2 ⟨c, hc⟩).1 hw) =
      P.h2 (e₂ (M.coch.cls 2 c hc))
    rw [he', he]
    unfold Pair.h2 compatiblePairH2
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g.1, g.2] i)) = P.u (c.1 ![P.φ g.1, P.φ g.2])
    rw [show (fun i => P.φ (![g.1, g.2] i)) = ![P.φ g.1, P.φ g.2] from by
      funext i; fin_cases i <;> rfl]

end ReciprocityTheory.Coh
