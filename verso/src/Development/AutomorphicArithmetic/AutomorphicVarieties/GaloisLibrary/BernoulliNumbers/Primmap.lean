import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `R S _ _ _ _ N _ f hf k χ`. Take `⟨hcond, hval, -⟩` from `b_condmap f hf χ`. Rewrite using `[Bprim_eq, Bprim_eq, hcond, map_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hval a, RingHom.map_rat_algebraMap]`.
-/
theorem UpperTheory.V.Bern.b_primmap :
    ∀ {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ (k : ℕ) (χ : DirichletCharacter R N), f (Bprim k χ) = Bprim k (χ.ringHomComp f) := by
  intro R S _ _ _ _ N _ f hf k χ
  obtain ⟨hcond, hval, -⟩ := b_condmap f hf χ
  rw [Bprim_eq, Bprim_eq, hcond, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, hval a, RingHom.map_rat_algebraMap]
