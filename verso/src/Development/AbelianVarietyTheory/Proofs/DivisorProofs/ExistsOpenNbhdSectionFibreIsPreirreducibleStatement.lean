import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOpenNbhdSectionFibreIsPreirreducible.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)), V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧ ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  first | exact @GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible | exact GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible | (intros; apply GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible <;> assumption)
