import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.B1abs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl

namespace UpperTheory.V.Pa

/- English proof (translation)
Introduce `hcoh l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T x0 x k al hS hloc _ hρ hN4 hE hD`. Take `⟨d', hsum, hab⟩` from `hloc`. Take `⟨A⟩` from `arSys hcoh l L Ω s V0 O n r T x0 hS`. Use `b1abs l (locOf r) (globOf r V0) T n x k al _ V0.frame.D0 A d' s.odd ?_ hab (arPl hcoh l L Ω s V0 O n r hS).1 hρ hN4 hE hD` and prove the remaining obligations. Rewrite using `[← hsum]`.

Use `first`. Consider the case `exact (finsum_eq_sum_of_fintype _).symm`. Consider the case `(convert (finsum_eq_sum_of_fintype d').symm)`.
-/
theorem b1Ar : FirstOrderDualArithmeticBound := by
  intro hcoh l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T x0 x k al hS hloc _ hρ hN4 hE hD
  obtain ⟨d', hsum, hab⟩ := hloc
  obtain ⟨A⟩ := arSys hcoh l L Ω s V0 O n r T x0 hS
  refine b1abs l (locOf r) (globOf r V0) T n x k al _ V0.frame.D0 A d' s.odd ?_ hab
    (arPl hcoh l L Ω s V0 O n r hS).1 hρ hN4 hE hD
  rw [← hsum]
  first
    | exact (finsum_eq_sum_of_fintype _).symm
    | (convert (finsum_eq_sum_of_fintype d').symm)

end UpperTheory.V.Pa
