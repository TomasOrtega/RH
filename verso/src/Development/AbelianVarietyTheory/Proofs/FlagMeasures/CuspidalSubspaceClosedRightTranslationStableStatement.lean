import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspSubspace.cuspidal_closed_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCuspidalSubspaceClosedRightTranslationStable.lean&line=278#L278)
-/
theorem _root_.GlobalTheory.T.cuspidalSubspace_closed_rightTranslation_stable : ∀ B : RowsAut, ∃ S : Submodule ℂ (B.I.L2 B.μf B.fund), (∀ F, F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext F)) ∧ IsClosed (S : Set (B.I.L2 B.μf B.fund)) ∧ (∀ g, ∀ F ∈ S, B.R g F ∈ S) ∧ ∀ (F : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), (∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y) → Continuous f → f =ᵐ[B.I.muA B.μf] B.I.ext F → (F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) f) := by
  first | exact @GlobalTheory.CuspSubspace.cuspidal_closed_stable | exact GlobalTheory.CuspSubspace.cuspidal_closed_stable | (intros; apply GlobalTheory.CuspSubspace.cuspidal_closed_stable <;> assumption)
