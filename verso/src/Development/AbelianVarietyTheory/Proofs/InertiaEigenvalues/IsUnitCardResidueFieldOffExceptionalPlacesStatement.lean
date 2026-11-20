import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitCardResidueFieldOffExceptionalPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsUnitCardResidueFieldOffExceptionalPlaces.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.isUnit_card_residueField_off_exceptional_places : ∀ {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (k : ℕ) (PP : Pl D.host.E),
  PP ∉ X.S0 i → IsUnit ((Nat.card (kP PP) : ℕ) : X.Ok i k) := by
  first | exact @GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok | exact GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok | (intros; apply GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok <;> assumption)
