import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeilDatumFixesLatticeVacuaAtInertPlaces.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D := by
  first | exact @GlobalTheory.InertAll.inertAllO | exact GlobalTheory.InertAll.inertAllO | (intros; apply GlobalTheory.InertAll.inertAllO <;> assumption)
