import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterExponentList
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalCharacterExponentList.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.local_character_exponent_list : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N i : ℕ) (hi : i + 1 ≤ N) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) → (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) → ∀ ϖ : kˣ, ∃ L : List ℂ,
      (∀ c ∈ L, ∃ (j : Fin 2) (l : ℕ), l ≤ i ∧ ‖c‖ = nabs k ϖ ^ ((1 - (b j : ℝ)) / 2 + l)) ∧
      ∀ w, polyAt (jac (blockIndex hi) (pairInd k b hb χ) (blockScalar₂ k N i ϖ)) L w = 0 := by
  first | exact @GlobalTheory.LeviBlockExponentLocal.position_exponents | exact GlobalTheory.LeviBlockExponentLocal.position_exponents | (intros; apply GlobalTheory.LeviBlockExponentLocal.position_exponents <;> assumption)
