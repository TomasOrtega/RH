import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH0LevelRepEq
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardH0LevelRepEq.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.card_H0_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O), Finite ρ.invariants →
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
      Nat.card (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  first | exact @GlobalTheory.ShapeNeg.card_H0_level_rep | exact GlobalTheory.ShapeNeg.card_H0_level_rep | (intros; apply GlobalTheory.ShapeNeg.card_H0_level_rep <;> assumption)
