import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeckeGeometricAllStates.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.hecke_geometric_all_states : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  first | exact @GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_lb1 | exact GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_lb1 | (intros; apply GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_lb1 <;> assumption)
