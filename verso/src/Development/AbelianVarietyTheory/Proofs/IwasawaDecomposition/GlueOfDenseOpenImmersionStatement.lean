import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGlueOfDenseOpenImmersion.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_section_extending_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  first | exact @GlobalTheory.glue_of_dense_openImmersion | exact GlobalTheory.glue_of_dense_openImmersion | (intros; apply GlobalTheory.glue_of_dense_openImmersion <;> assumption)
