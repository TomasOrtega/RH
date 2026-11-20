import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete

open IsLocalRing

namespace GlobalTheory.AdicNoeth

/- English proof (translation)
Introduce `R _ _ I`. Establish `fg : I.FG` using `I.fg_of_isNoetherianRing`. Establish `hc` using `AdicCompletion.isAdicComplete_self I fg`. Establish `e : (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃+* R ⧸ I`. Rewrite using `[← AdicCompletion.ker_evalOneₐ_eq_map I fg]`.

Conclude with `RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)`. Conclude with `isNoetherianRing_of_isAdicComplete _ _ (fg.map _) hc (isNoetherianRing_of_ringEquiv _ e.symm)`.
-/
theorem isNoetherianRing_adicCompletion : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R) := by
  intro R _ _ I
  have fg : I.FG := I.fg_of_isNoetherianRing
  have hc := AdicCompletion.isAdicComplete_self I fg
  have e : (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃+* R ⧸ I := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
  exact isNoetherianRing_of_isAdicComplete _ _ (fg.map _) hc
    (isNoetherianRing_of_ringEquiv _ e.symm)

end GlobalTheory.AdicNoeth
