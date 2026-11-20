import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUnique
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTermDatumOrbitUnique.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.term_datum_orbit_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  first | exact @GlobalTheory.LocOver.orbit_over_unique | exact GlobalTheory.LocOver.orbit_over_unique | (intros; apply GlobalTheory.LocOver.orbit_over_unique <;> assumption)
