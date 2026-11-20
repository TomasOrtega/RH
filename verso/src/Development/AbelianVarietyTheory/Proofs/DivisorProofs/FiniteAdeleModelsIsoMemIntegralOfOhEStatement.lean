import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteAdeleModelsIsoMemIntegralOfOhE.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D → GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | exact GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | (intros; apply GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE <;> assumption)
