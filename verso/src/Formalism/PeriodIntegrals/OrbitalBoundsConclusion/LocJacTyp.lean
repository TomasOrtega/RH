import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.LocJacTypClosed

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.LocJacTyp.locJacTyp_closed σ ψ v`.
-/
theorem locJacTyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    PI.LocJacTyp.LocJacTyp σ ψ v :=
  PI.UnitaryGroupMassFormula.LocJacTyp.locJacTyp_closed σ ψ v
