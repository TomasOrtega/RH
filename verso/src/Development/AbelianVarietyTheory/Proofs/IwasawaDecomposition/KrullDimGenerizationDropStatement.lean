import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimGenerizationDrop
import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FKrullDimGenerizationDrop.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.krull_dim_generization_drop : ∀ (X : Scheme.{0}) (q η : X), η ⤳ q → η ≠ q → ringKrullDim (X.presheaf.stalk q) ≤ 1 → ringKrullDim (X.presheaf.stalk η) ≤ 0 := by
  first | exact @GlobalTheory.ringKrullDim_stalk_nonpos_of_specializes_of_ne | exact GlobalTheory.ringKrullDim_stalk_nonpos_of_specializes_of_ne | (intros; apply GlobalTheory.ringKrullDim_stalk_nonpos_of_specializes_of_ne <;> assumption)
