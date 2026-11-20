import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducibleStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAugSpanOneMemOfOrthogonalThree.lean&line=188#L188)
-/
theorem _root_.GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  first | exact @GlobalTheory.augSpan_one_mem_of_orthogonal_three | exact GlobalTheory.augSpan_one_mem_of_orthogonal_three | (intros; apply GlobalTheory.augSpan_one_mem_of_orthogonal_three <;> assumption)
