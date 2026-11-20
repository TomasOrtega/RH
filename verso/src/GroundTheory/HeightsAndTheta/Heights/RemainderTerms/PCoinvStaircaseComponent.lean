import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Coinv

noncomputable section

/- English proof (translation)
Introduce `K _ f n v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨e, he, rfl⟩` from `hx`. Establish `hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree` using `(mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)`.

Take `⟨hle, heq⟩` from `h1 f n e he`. Use `⟨fun d hd => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[homogeneousComponent_of_mem hhom, if_neg (by omega)]`. Rewrite using `[homogeneousComponent_of_mem hhom]`. Distinguish the cases in `h : coinvTop f n = e.degree`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos h, heq h.symm, C_1, one_mul]`. Conclude with `⟨0, by rw [if_neg h, C_0, zero_mul]⟩`. Consider the case `zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨hx1, cx, hx2⟩` from `hx`. Take `⟨hy1, cy, hy2⟩` from `hy`. Use `⟨fun d hd => by rw [map_add, hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hx2, hy2, C_add, add_mul]`. Consider the case `smul a x _ hx`.

Take `⟨hx1, cx, hx2⟩` from `hx`. Use `⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]`.
-/
theorem CoinvStaircaseComponent.proof (h1 : CoinvStaircaseDegree.Statement) :
    CoinvStaircaseComponent.Statement := by
  intro K _ f n v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    obtain ⟨hle, heq⟩ := h1 f n e he
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · rw [homogeneousComponent_of_mem hhom]
      by_cases h : coinvTop f n = e.degree
      · refine ⟨1, ?_⟩
        rw [if_pos h, heq h.symm, C_1, one_mul]
      · exact ⟨0, by rw [if_neg h, C_0, zero_mul]⟩
  | zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    obtain ⟨hy1, cy, hy2⟩ := hy
    refine ⟨fun d hd => by rw [map_add, hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩
    rw [map_add, hx2, hy2, C_add, add_mul]
  | smul a x _ hx =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    refine ⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩
    rw [map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
