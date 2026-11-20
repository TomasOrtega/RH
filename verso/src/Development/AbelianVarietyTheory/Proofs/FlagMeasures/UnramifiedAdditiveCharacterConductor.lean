import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocalDensityValue

def placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Fv F v →+ AF F :=
  (AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (placeHom F v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

def localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (placeHom F v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : (localChar F ψ v : Fv F v → ℂ) = psiV F ψ v := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem isLocalChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) (m : ℤ)
    (hm : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsLocalChar F v (localChar F ψ v) := by
  refine ⟨hψ.1.comp (continuous_placeHom F v), fun t => hψ.2.1 _, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (m + 1))
  have := (hm t).1 fun s _ => h _
  rw [ht, WithZero.exp_le_exp] at this
  omega

end GlobalTheory.LocalDensityValue
