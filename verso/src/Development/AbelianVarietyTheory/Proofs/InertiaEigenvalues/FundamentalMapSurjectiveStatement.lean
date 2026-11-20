import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.FundOnto.fundOnto` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFundamentalMapSurjective.lean&line=283#L283)
-/
theorem _root_.GlobalTheory.T.fundamental_map_surjective : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.FundOnto := by
  first | exact @GlobalTheory.MemLoc.FundOnto.fundOnto | exact GlobalTheory.MemLoc.FundOnto.fundOnto | (intros; apply GlobalTheory.MemLoc.FundOnto.fundOnto <;> assumption)
