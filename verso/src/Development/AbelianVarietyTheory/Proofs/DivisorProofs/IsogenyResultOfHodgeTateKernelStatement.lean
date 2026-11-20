import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyResultOfHodgeTateKernel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.Iso.isoSt_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsogenyResultOfHodgeTateKernel.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.isogeny_result_of_hodge_tate_kernel : IntSt → LinSt → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → IsoSt := by
  first | exact @GlobalTheory.HalfGeo.Iso.isoSt_of | exact GlobalTheory.HalfGeo.Iso.isoSt_of | (intros; apply GlobalTheory.HalfGeo.Iso.isoSt_of <;> assumption)
