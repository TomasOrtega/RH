import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKsSubMapClsEqHomO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankKsSubMapClsEqHomO.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO : ∀ {k O H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z), Z ≤ G → finrank k ((ksSub σ 0 G Z).map (cls G)) = finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := by
  first | exact @GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | exact GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | (intros; apply GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO <;> assumption)
