import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FReductionToLocalLanglandsA.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.reduction_to_local_langlands_A : PrN → PhtCmp → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SA hL := by
  first | exact @GlobalTheory.HeightCounting.Up.sa_of_prN | exact GlobalTheory.HeightCounting.Up.sa_of_prN | (intros; apply GlobalTheory.HeightCounting.Up.sa_of_prN <;> assumption)
