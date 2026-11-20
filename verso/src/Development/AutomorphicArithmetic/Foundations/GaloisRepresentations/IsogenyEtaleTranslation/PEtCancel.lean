import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

open AlgebraicGeometry in
/- English proof (translation)
Introduce `A B C E f g f' hg hfin1 het1 hfin2 het2`. Establish `h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f')` using `inferInstance`. Establish `h2 : AlgebraicGeometry.IsSeparated g` using `AlgebraicGeometry.IsSeparated.of_comp g f'`. Establish `h3 : AlgebraicGeometry.FormallyUnramified g` using `AlgebraicGeometry.FormallyUnramified.of_comp g f'`. Conclude with `⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩`.
-/
theorem UpperTheory.Gal.FixZ.etCancel_of :
    UpperTheory.Gal.FixZ.EtCancel := by
  intro A B C E f g f' hg hfin1 het1 hfin2 het2
  have h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f') :=
    inferInstance
  have h2 : AlgebraicGeometry.IsSeparated g := AlgebraicGeometry.IsSeparated.of_comp g f'
  have h3 : AlgebraicGeometry.FormallyUnramified g :=
    AlgebraicGeometry.FormallyUnramified.of_comp g f'
  exact ⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩
