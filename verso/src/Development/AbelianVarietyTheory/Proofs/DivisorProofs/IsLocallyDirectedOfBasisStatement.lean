import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyDirectedOfBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThickGlue.isLocallyDirected_of_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLocallyDirectedOfBasis.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isLocallyDirected_of_bijective_basis_compatible : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  first | exact @GlobalTheory.ThickGlue.isLocallyDirected_of_basis | exact GlobalTheory.ThickGlue.isLocallyDirected_of_basis | (intros; apply GlobalTheory.ThickGlue.isLocallyDirected_of_basis <;> assumption)
