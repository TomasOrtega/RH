import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
open IsLocalRing

namespace GlobalTheory.CompleteNakayamaLocal

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finite_of_maximalIdeal_map_eq : ∀ {B R : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsAdicComplete (maximalIdeal R) R → (maximalIdeal B).map ψ = maximalIdeal R → ((residue R).comp ψ).Finite → ψ.Finite := by
  intro B R _ _ _ _ _ ψ hB hR hmap hres
  letI : Algebra B R := ψ.toAlgebra
  have hm : (maximalIdeal B).map (algebraMap B R) = maximalIdeal R := hmap
  haveI : IsPrecomplete (maximalIdeal B) B := inferInstance
  haveI : IsHausdorff ((maximalIdeal B).map (algebraMap B R)) R := by
    rw [hm]; infer_instance
  haveI : Module.Finite B (R ⧸ (maximalIdeal B).map (algebraMap B R)) := by
    rw [hm]
    exact hres
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)

end GlobalTheory.CompleteNakayamaLocal
