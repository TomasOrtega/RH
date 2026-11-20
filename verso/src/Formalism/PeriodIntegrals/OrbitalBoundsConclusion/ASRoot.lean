import Mathlib
import Formalism.PeriodIntegrals.ArtSch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC

/- English proof (translation)
Introduce `l _ c b`. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Take `⟨b', rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨z, hz⟩` from `PI.ArtSch.RootWork.exists_root_OC l c' b'`. Use `⟨Ideal.Quotient.mk _ z, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, ← map_mul, ← map_sub, ← map_sub, hz, map_zero]`.
-/
theorem rootModP_holds : PI.ArtSch.RootModP := by
  intro l _ c b
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, hz⟩ := PI.ArtSch.RootWork.exists_root_OC l c' b'
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [← map_pow, ← map_mul, ← map_sub, ← map_sub, hz, map_zero]
