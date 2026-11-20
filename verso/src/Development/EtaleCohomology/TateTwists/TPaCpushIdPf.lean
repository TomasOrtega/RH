import Development.EtaleCohomology.TateTwists.TPairAssocPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Introduce `R _ E I n x`. Take `⟨a, rfl⟩` from `CohomologyClass.mk_surjective x`. Use `show CohomologyClass.mk (zcomp a (Cocycle.ofHom (𝟙 I)) (add_zero n)) = CohomologyClass.mk a`. Use `congr 1`. Apply `Cocycle.ext` to reduce the goal to its premises.

Simplify using `[zcomp]`.
-/
theorem t_pa_cpush_id_of : t_pa_cpush_id := by
  intro R _ E I n x
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp a (Cocycle.ofHom (𝟙 I)) (add_zero n)) = CohomologyClass.mk a
  congr 1
  apply Cocycle.ext
  simp [zcomp]

end LateralTheory.EtaleFoundations
