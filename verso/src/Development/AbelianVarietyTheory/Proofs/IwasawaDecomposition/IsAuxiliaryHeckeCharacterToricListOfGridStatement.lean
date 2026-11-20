import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridAlt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsAuxiliaryHeckeCharacterToricListOfGridAlt.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  first | exact @GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid | exact GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid | (intros; apply GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid <;> assumption)
