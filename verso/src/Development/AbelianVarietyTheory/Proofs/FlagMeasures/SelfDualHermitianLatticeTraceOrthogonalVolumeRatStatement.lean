import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRat
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HL.VolPerp.vol_perp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.selfDualHermitianLattice_trace_orthogonal_volume_ratio : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  first | exact @GlobalTheory.HL.VolPerp.vol_perp | exact GlobalTheory.HL.VolPerp.vol_perp | (intros; apply GlobalTheory.HL.VolPerp.vol_perp <;> assumption)
