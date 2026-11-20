import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.LocHaar

/- English proof (translation)
Establish `key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), ∃ μ : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E), μ.IsAddHaarMeasure`. Introduce `v`. Take `⟨tr, lc, sc, t2, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v`. Take `⟨h1, h2, h3, h4, h5⟩` from `Formalism.IndefR.Eqv.G5.tens_facts (F := D.host.F) (E := D.host.E) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.deg2`. Conclude with `⟨Measure.addHaar, inferInstance⟩`.

Use `choose lamG h using key`. Conclude with `⟨lamG, h⟩`.
-/
theorem exists_addHaar_tens (D : D7) (n : ℕ) :
    ∃ lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
      ∀ v, (lamG v).IsAddHaarMeasure := by
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      ∃ μ : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
        μ.IsAddHaarMeasure := by
    intro v
    obtain ⟨tr, lc, sc, t2, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v
    obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.G5.tens_facts (F := D.host.F) (E := D.host.E)
      (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.deg2
    exact ⟨Measure.addHaar, inferInstance⟩
  choose lamG h using key
  exact ⟨lamG, h⟩

end GlobalTheory.CompanionTheory.LocHaar
