import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeStabilizerNormalisingSubgroup
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HL.FrameStabLat.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsLatticeStabilizerNormalisingSubgroup.lean&line=266#L266)
-/
theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by
  first | exact @GlobalTheory.HL.FrameStabLat.main | exact GlobalTheory.HL.FrameStabLat.main | (intros; apply GlobalTheory.HL.FrameStabLat.main <;> assumption)
