import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.IsCplAt.nonempty_algEquiv :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra R B'],
      IsCplAt R p B → IsCplAt R p B' → Nonempty (B ≃ₐ[R] B') := by
  intro R _ p B _ _ _ B' _ _ _ hB hB'
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  haveI : IsAdicComplete (maximalIdeal B') B' := hB'.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift R p B hB B' (algebraMap R B') hB'.comap_eq
  obtain ⟨χ, hχ, -⟩ := IsCplAt.existsUnique_lift R p B' hB' B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB⟩ := IsCplAt.existsUnique_lift R p B hB B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB'⟩ := IsCplAt.existsUnique_lift R p B' hB' B' (algebraMap R B') hB'.comap_eq
  have h1 : χ.comp ψ = RingHom.id B := by
    have ha : (χ.comp ψ).comp (algebraMap R B) = algebraMap R B := by
      rw [RingHom.comp_assoc, hψ, hχ]
    rw [huB _ ha, huB (RingHom.id B) (RingHom.id_comp _)]
  have h2 : ψ.comp χ = RingHom.id B' := by
    have ha : (ψ.comp χ).comp (algebraMap R B') = algebraMap R B' := by
      rw [RingHom.comp_assoc, hχ, hψ]
    rw [huB' _ ha, huB' (RingHom.id B') (RingHom.id_comp _)]
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom ψ χ h2 h1) ?_⟩
  intro x
  exact congrArg (fun φ : R →+* B' => φ x) hψ
