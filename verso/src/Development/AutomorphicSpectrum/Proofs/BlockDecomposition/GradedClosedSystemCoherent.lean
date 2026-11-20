import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

/- English proof (translation)
Consider the cases of `e with`. Consider the case `zero`. Establish `: IsIso (lvl S 0).arrow`. Rewrite using `[lvl_zero]`. Conclude with `(Subobject.isIso_arrow_iff_eq_top _).2 rfl`.

Conclude with `IsCoherent.of_iso (asIso (lvl S 0).arrow).symm hP`. Consider the case `succ e => exact GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)`.
-/
lemma isCoherent_lvl {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules} (hP : IsCoherent P)
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) :
    IsCoherent (lvl S e : X.Modules) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      rw [lvl_zero]
      exact (Subobject.isIso_arrow_iff_eq_top _).2 rfl
    exact IsCoherent.of_iso (asIso (lvl S 0).arrow).symm hP
  | succ e => exact GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)

/- English proof (translation)
Introduce `A _ _ I X _ _ P hP S hS e`. Use `(isCoherent_lvl hP hS (e + 1)).1` as an intermediate fact. Conclude with `isCoherent_cokernel (incl (anti hS) e) (isCoherent_lvl hP hS e)`.
-/
theorem isCoherent_gr : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P →
    ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  intro A _ _ I X _ _ P hP S hS e
  have := (isCoherent_lvl hP hS (e + 1)).1
  exact isCoherent_cokernel (incl (anti hS) e) (isCoherent_lvl hP hS e)

end GlobalTheory.CompanionTheory.GE.Step
