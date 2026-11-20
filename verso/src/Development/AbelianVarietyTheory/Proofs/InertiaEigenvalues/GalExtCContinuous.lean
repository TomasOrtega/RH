import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]`. Conclude with `(spectralNorm_eq_of_equiv g x).symm`.
-/
theorem norm_galAlgCl (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv g x).symm

/- English proof (translation)
The claim follows from `AddMonoidHomClass.isometry_of_norm g (norm_galAlgCl g)`.
-/
theorem isometry_galAlgCl (g : GQ l) : Isometry (g : Om l → Om l) :=
  AddMonoidHomClass.isometry_of_norm g (norm_galAlgCl g)

noncomputable def galExtC (g : GQ l) : PadicComplex l ≃+* PadicComplex l :=
  UniformSpace.Completion.mapRingEquiv g.toRingEquiv (isometry_galAlgCl g).continuous
    (isometry_galAlgCl g.symm).continuous

/- English proof (translation)
The claim follows from `UniformSpace.Completion.map_coe (isometry_galAlgCl g).uniformContinuous x`.
-/
theorem galExtC_coe (g : GQ l) (x : Om l) :
    galExtC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.map_coe (isometry_galAlgCl g).uniformContinuous x

/- English proof (translation)
The claim follows from `UniformSpace.Completion.continuous_map`.
-/
theorem galExtC_continuous (g : GQ l) : Continuous (galExtC g) :=
  UniformSpace.Completion.continuous_map

/- English proof (translation)
Proceed by induction on `y using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm`. Consider the case `ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]`.
-/
theorem norm_galExtC (g : GQ l) (y : PadicComplex l) : ‖galExtC g y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm
  | ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]

/- English proof (translation)
Use extensionality with `y`. Express the relevant statement in the definitionally equal form `galExtC (g * h) y = galExtC g (galExtC h y)`. Proceed by induction on `y using UniformSpace.Completion.induction_on with`. Consider the case `hp`. Conclude with `isClosed_eq (galExtC_continuous _) ((galExtC_continuous g).comp (galExtC_continuous h))`.

Consider the case `ih x => rw [galExtC_coe, galExtC_coe, galExtC_coe, AlgEquiv.mul_apply]`.
-/
theorem galExtC_mul (g h : GQ l) : galExtC (g * h) = galExtC g * galExtC h := by
  ext y
  change galExtC (g * h) y = galExtC g (galExtC h y)
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (galExtC_continuous _) ((galExtC_continuous g).comp (galExtC_continuous h))
  | ih x => rw [galExtC_coe, galExtC_coe, galExtC_coe, AlgEquiv.mul_apply]

noncomputable def galActC (l : ℕ) [Fact l.Prime] : GQ l →* (PadicComplex l ≃+* PadicComplex l) :=
  MonoidHom.mk' galExtC galExtC_mul

/- English proof (translation)
Assemble the required witnesses or components as `⟨galExtC_coe, norm_galExtC⟩`.
-/
theorem isActC_galActC (l : ℕ) [Fact l.Prime] : IsActC (galActC l) :=
  ⟨galExtC_coe, norm_galExtC⟩

/- English proof (translation)
Introduce `l _` and use `⟨galActC l, isActC_galActC l⟩`.
-/
theorem exists_isActC :
    ∀ (l : ℕ) [Fact l.Prime], ∃ act : GQ l →* (PadicComplex l ≃+* PadicComplex l), IsActC act :=
  fun l _ => ⟨galActC l, isActC_galActC l⟩

end GlobalTheory.InertiaEigenvalues
