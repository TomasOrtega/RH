import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.GKExtensionToSmoothVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `h₁ h₂ D` and use `⟨GlobalTheory.T.gKModuleMapCuspForms_extends_multiplicitySpace h₁ h₂ D, GlobalTheory.KFiniteDetermined.restrInj D⟩`.
-/
theorem gkExtension :
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D :=
  fun h₁ h₂ D => ⟨GlobalTheory.T.gKModuleMapCuspForms_extends_multiplicitySpace h₁ h₂ D, GlobalTheory.KFiniteDetermined.restrInj D⟩

end GlobalTheory.GKExtensionToSmoothVectors
