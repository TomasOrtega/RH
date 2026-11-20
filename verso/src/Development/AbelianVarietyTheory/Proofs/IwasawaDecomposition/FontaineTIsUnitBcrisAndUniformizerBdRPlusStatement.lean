import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFontaineTIsUnitBcrisAndUniformizerBdRPlus.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∧ C.j C.t ∈ Per.FilP l 1 ∧ C.j C.t ∉ Per.FilP l 2 ∧ IsUnit (l : Per.Bcris l) := by
  first | exact @GlobalTheory.MemLoc.core_t_unit_fil | exact GlobalTheory.MemLoc.core_t_unit_fil | (intros; apply GlobalTheory.MemLoc.core_t_unit_fil <;> assumption)
