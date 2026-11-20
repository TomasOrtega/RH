import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConjugateTopBoundOfInputs.lean&line=271#L271)
-/
theorem _root_.GlobalTheory.T.conjugate_top_bound_of_inputs : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 := by
  first | exact @GlobalTheory.KerConjMean.conjTopK | exact GlobalTheory.KerConjMean.conjTopK | (intros; apply GlobalTheory.KerConjMean.conjTopK <;> assumption)
