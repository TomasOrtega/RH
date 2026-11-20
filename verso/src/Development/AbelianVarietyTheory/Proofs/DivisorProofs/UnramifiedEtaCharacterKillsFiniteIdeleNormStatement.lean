import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEtaCharacterKillsFiniteIdeleNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaTildeNorm.map_finIdl_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedEtaCharacterKillsFiniteIdeleNorm.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.unramified_eta_character_kills_finite_idele_norm : ∀ (D : D7) (χ : HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.EtaTildeNorm.map_finIdl_norm | exact GlobalTheory.EtaTildeNorm.map_finIdl_norm | (intros; apply GlobalTheory.EtaTildeNorm.map_finIdl_norm <;> assumption)
