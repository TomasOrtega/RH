import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.TorIsoId
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoCoeffZero
open NumberField IsDedekindDomain Polynomial GlobalTheory.CMRam GlobalTheory.FieldSize

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open WeierstrassCurve

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DiscUniformisation.main`. Consider the case `exact _root_.GlobalTheory.DiscUniformisation.main`. Consider the case `(apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DiscUniformisation.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DiscUniformisation.main ..)`.
-/
theorem exists_conj_lattice (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  first
  | exact @_root_.GlobalTheory.DiscUniformisation.main
  | exact _root_.GlobalTheory.DiscUniformisation.main
  | (apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiscUniformisation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiscUniformisation.main ..)

end GlobalTheory.CMRam
