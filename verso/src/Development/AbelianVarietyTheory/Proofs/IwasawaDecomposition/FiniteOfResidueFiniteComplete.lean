import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
open IsLocalRing

namespace GlobalTheory.CompleteNakayamaLocal

/- English proof (translation)
Introduce `B R _ _ _ _ _ ψ hB hR hmap hres`. Use `letI : Algebra B R := ψ.toAlgebra`. Establish `hm : (maximalIdeal B).map (algebraMap B R) = maximalIdeal R` using `hmap`. Use `haveI : IsPrecomplete (maximalIdeal B) B := inferInstance`. Use `haveI : IsHausdorff ((maximalIdeal B).map (algebraMap B R)) R := by`.

Rewrite using `[hm]`. Use `infer_instance`. Use `haveI : Module.Finite B (R ⧸ (maximalIdeal B).map (algebraMap B R)) := by`. Rewrite using `[hm]`. Conclude with `hres`.

Conclude with `GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)`.
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
