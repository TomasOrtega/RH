import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FChosenPlacesAdmissibleGoodSetup.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.chosenPlaces_admissible_goodSetup : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  first | exact @GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | exact GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | (intros; apply GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint <;> assumption)
