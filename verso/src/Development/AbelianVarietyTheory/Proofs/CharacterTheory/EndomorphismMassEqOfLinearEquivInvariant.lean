import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

/- English proof (translation)
Introduce `F _ _ V _ _ _ Φ hΦ P hP`. Set `e : V ≃ₗ[F] (Fin P.natDegree → F)` to `LinearEquiv.ofFinrankEq _ _ (by simp [hP])`. Unfold `mass`. Use `finsum_mem_eq_of_bijOn (fun g => e.conj g) ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `g hg`.

Simplify using `using hg`. Introduce `g _ h _ hgh`. Simplify using `using congrArg e.symm.conj hgh`. Introduce `h hh`. Use `⟨e.symm.conj h, ?_, by simp⟩` and prove the remaining obligations.

Simplify using `using hh`. Introduce `g _`. Conclude with `(hΦ V _ e g).symm`.
-/
theorem mass_eq_mass_pi_of_invariant : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.natDegree = Module.finrank F V → mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  intro F _ _ V _ _ _ Φ hΦ P hP
  let e : V ≃ₗ[F] (Fin P.natDegree → F) := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  unfold mass
  refine finsum_mem_eq_of_bijOn (fun g => e.conj g) ⟨?_, ?_, ?_⟩ ?_
  · intro g hg
    simpa using hg
  · intro g _ h _ hgh
    simpa using congrArg e.symm.conj hgh
  · intro h hh
    refine ⟨e.symm.conj h, ?_, by simp⟩
    simpa using hh
  · intro g _
    exact (hΦ V _ e g).symm

end GlobalTheory.CuspGL
