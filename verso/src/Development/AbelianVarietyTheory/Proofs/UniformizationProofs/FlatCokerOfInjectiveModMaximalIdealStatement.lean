import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdeal
open CategoryTheory CategoryTheory.Limits TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.flat_coker_of_injective_mod_maximalIdeal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FFlatCokerOfInjectiveModMaximalIdeal.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.flat_quotient_range_of_injective_mod_maximal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (M N : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module V N] [IsScalarTower V A N] [Module.Flat V N] (u : M →ₗ[A] N), (∀ x : M, u x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A N) → x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A M)) → Module.Flat V (N ⧸ LinearMap.range u) := by
  first | exact @GlobalTheory.flat_coker_of_injective_mod_maximalIdeal | exact GlobalTheory.flat_coker_of_injective_mod_maximalIdeal | (intros; apply GlobalTheory.flat_coker_of_injective_mod_maximalIdeal <;> assumption)
