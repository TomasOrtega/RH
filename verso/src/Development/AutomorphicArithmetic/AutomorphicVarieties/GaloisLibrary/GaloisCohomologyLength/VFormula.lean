import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Establish `hX` using `Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)`. Establish `hY` using `Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)`. Rewrite using `[hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]`.
-/
private theorem length_add_coker {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
    Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
      Module.length R (LinearMap.ker f) + Module.length R Y := by
  have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ D e hcase hcoker hsha hloc`. Establish `hker : LinearMap.ker (localH2 D e) = Sha2Zl D e`. Unfold `localH2`. Rewrite using `[LinearMap.ker_pi]`. Both sides reduce to the same expression.

Establish `key` using `length_add_coker (localH2 D e)`. Rewrite `key` using `[hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype]`. Unfold `VLen sumLocalH0TwistLength`. Rewrite using `[key]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl (fun v _ => hloc v)`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.vFormula :
    Formalism.GaloisCohomology.VFormula := by
  intro F Ω _ _ _ _ _ l _ D e hcase hcoker hsha hloc
  have hker : LinearMap.ker (localH2 D e) = Sha2Zl D e := by
    unfold localH2
    rw [LinearMap.ker_pi]
    rfl
  have key := length_add_coker (localH2 D e)
  rw [hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype] at key
  unfold VLen sumLocalH0TwistLength
  rw [key]
  congr 1
  exact Finset.sum_congr rfl (fun v _ => hloc v)
