import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Unfold `CasK`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [LinearMap.sum_apply, inner_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hab : ε a = ε b`.

Rewrite using `[if_pos hab.symm, if_pos hab, Module.End.mul_apply, h a b hab]`. Rewrite using `[if_neg (fun e => hab e.symm), if_neg hab]`. Simplify using the standard rewrite rules.
-/
theorem inner_casK_eq_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (h : KUnit ε E) (x y : M) :
    ⟪x, CasK ε E y⟫_ℂ = ∑ a, ∑ b, if ε a = ε b then ⟪E a b x, E a b y⟫_ℂ else 0 := by
  unfold CasK
  rw [Finset.sum_comm]
  simp only [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab, Module.End.mul_apply, h a b hab]
  · rw [if_neg (fun e => hab e.symm), if_neg hab]
    simp

/- English proof (translation)
Introduce `M _ _ n ε E h`. Use `⟨fun x y => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← inner_conj_symm, inner_casK_eq_sum h, inner_casK_eq_sum h]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[inner_conj_symm]`. Simplify using the standard rewrite rules. Rewrite using `[inner_casK_eq_sum h]`. Simplify using `only [Complex.re_sum]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `inner_self_eq_norm_sq (𝕜 := ℂ) _`. Simplify using the standard rewrite rules.
-/
theorem casK_isSymmetric_and_form :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E →
      LinearMap.IsSymmetric (CasK ε E) ∧
        ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  intro M _ _ n ε E h
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← inner_conj_symm, inner_casK_eq_sum h, inner_casK_eq_sum h]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [inner_conj_symm]
    · simp
  · rw [inner_casK_eq_sum h]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    · simp

end GlobalTheory
