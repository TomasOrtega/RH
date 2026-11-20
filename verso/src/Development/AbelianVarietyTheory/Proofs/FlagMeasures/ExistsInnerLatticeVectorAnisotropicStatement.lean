import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeVectorAnisotropic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsInnerLatticeVectorAnisotropic.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.exists_inner_lattice_vector_anisotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  first | exact @GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | exact GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | (intros; apply GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' <;> assumption)
