import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExportSeries.SpecGood.spec_good` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTameTwistFamilySpecializationGood.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.tameTwistFamily_specialization_good : ∀ (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) (χ : Multiplicative (↥Q → C) →* A), u.Good Q → (u.spec Q χ).Good := by
  first | exact @GlobalTheory.ExportSeries.SpecGood.spec_good | exact GlobalTheory.ExportSeries.SpecGood.spec_good | (intros; apply GlobalTheory.ExportSeries.SpecGood.spec_good <;> assumption)
