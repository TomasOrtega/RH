import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R _ p B _ _ _ B' _ _ _ hB hB'`. Use `haveI : IsAdicComplete (maximalIdeal B) B := hB.complete`. Use `haveI : IsAdicComplete (maximalIdeal B') B' := hB'.complete`. Take `⟨ψ, hψ, -⟩` from `IsCplAt.existsUnique_lift R p B hB B' (algebraMap R B') hB'.comap_eq`. Take `⟨χ, hχ, -⟩` from `IsCplAt.existsUnique_lift R p B' hB' B (algebraMap R B) hB.comap_eq`.

Take `⟨_, -, huB⟩` from `IsCplAt.existsUnique_lift R p B hB B (algebraMap R B) hB.comap_eq`. Take `⟨_, -, huB'⟩` from `IsCplAt.existsUnique_lift R p B' hB' B' (algebraMap R B') hB'.comap_eq`. Establish `h1 : χ.comp ψ = RingHom.id B`. Establish `ha : (χ.comp ψ).comp (algebraMap R B) = algebraMap R B`. Rewrite using `[RingHom.comp_assoc, hψ, hχ]`.

Rewrite using `[huB _ ha, huB (RingHom.id B) (RingHom.id_comp _)]`. Establish `h2 : ψ.comp χ = RingHom.id B'`. Establish `ha : (ψ.comp χ).comp (algebraMap R B') = algebraMap R B'`. Rewrite using `[RingHom.comp_assoc, hχ, hψ]`. Rewrite using `[huB' _ ha, huB' (RingHom.id B') (RingHom.id_comp _)]`.

Use `⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom ψ χ h2 h1) ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `congrArg (fun φ : R →+* B' => φ x) hψ`.
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
