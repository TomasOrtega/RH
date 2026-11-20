import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegral
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler

open GlobalTheory.CompanionTheory.SW

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `e` using `TopK.coordHomeo (E := E) (AF F) b`. Establish `: SecondCountableTopology (AF F ⊗[F] E)` using `e.secondCountableTopology`. Establish `: BorelSpace (AF F ⊗[F] E)` using `⟨rfl⟩`. Establish `: BorelSpace (Ainf F ⊗[F] E)` using `⟨rfl⟩`. Establish `hc : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _)` using `MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) MeasProj.continuous_fstA`.

Use `measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations. Conclude with `(((continuous_apply i).comp (continuous_apply a)).comp hc).measurable`.
-/
theorem measurable_projInf [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    Measurable (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) MeasProj.continuous_fstA
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable

/- English proof (translation)
Establish `e` using `TopK.coordHomeo (E := E) (AF F) b`. Establish `: SecondCountableTopology (AF F ⊗[F] E)` using `e.secondCountableTopology`. Establish `: BorelSpace (AF F ⊗[F] E)` using `⟨rfl⟩`. Establish `: BorelSpace (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Establish `h1 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projFin : (Fin n → Fin M → AF F ⊗[F] E) → _)` using `MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) MeasProj.continuous_sndA`.

Establish `h2 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)` using `MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (MeasProj.continuous_evalV v)`. Use `measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations. Conclude with `(((continuous_apply i).comp (continuous_apply a)).comp (h2.comp h1)).measurable`.
-/
theorem measurable_projV [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Measurable (fun X : Fin n → Fin M → AF F ⊗[F] E =>
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) MeasProj.continuous_sndA
  have h2 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (MeasProj.continuous_evalV v)
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp (h2.comp h1)).measurable

/- English proof (translation)
Establish `e` using `TopK.coordHomeo (E := E) (AF F) b`. Establish `: SecondCountableTopology (AF F ⊗[F] E)` using `e.secondCountableTopology`. Establish `: BorelSpace (AF F ⊗[F] E)` using `⟨rfl⟩`. Rewrite using `[EulerBox.box_eq b S A hS]`. Conclude with `(MeasProj.isOpen_intOff b S).measurableSet.inter (Finset.measurableSet_biInter S fun v _ => measurable_projV b n M v (hA v))`.
-/
theorem measurableSet_box [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  rw [EulerBox.box_eq b S A hS]
  exact (MeasProj.isOpen_intOff b S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => measurable_projV b n M v (hA v))

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler
