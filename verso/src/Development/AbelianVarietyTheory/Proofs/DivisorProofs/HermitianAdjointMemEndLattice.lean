import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp only [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [mulVec, dotProduct, map_apply, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]`.
-/
theorem cc_map_mulVec (M : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((M.map cc *ᵥ y) b)) = M *ᵥ fun b => cc (y b) := by
  funext b
  simp only [mulVec, dotProduct, map_apply, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Rewrite using `[herm_eq_dotProduct, herm_eq_dotProduct, hAdj, cc_map_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_transpose]`. Conclude with `(dotProduct_mulVec _ _ _).symm`.
-/
theorem herm_mulVec_left_eq (G Y : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x y : Fin r → E) :
    herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
  rw [herm_eq_dotProduct, herm_eq_dotProduct, hAdj, cc_map_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul,
    ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact (dotProduct_mulVec _ _ _).symm

/- English proof (translation)
Take `⟨hGh, hdet, -, -, hsd⟩` from `h`. Introduce `y hy`. Use `(hsd _).1 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : IsIntegral ℤ (herm G x (hAdj G Y *ᵥ y))`. Rewrite using `[← herm_mulVec_left_eq G Y hdet]`.

Conclude with `(hsd (Y *ᵥ x)).2 (hY x hx) y hy`. Rewrite using `[← GlobalTheory.UCls.Det.herm_symm G hGh]`. Conclude with `h1.map (IsCMField.complexConj E)`.
-/
theorem hAdj_mem_endLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (Y : Matrix (Fin r) (Fin r) E) (h : SelfDualLat G Λ) (hY : Y ∈ endLat Λ) : hAdj G Y ∈ endLat Λ := by
  obtain ⟨hGh, hdet, -, -, hsd⟩ := h
  intro y hy
  refine (hsd _).1 fun x hx => ?_
  have h1 : IsIntegral ℤ (herm G x (hAdj G Y *ᵥ y)) := by
    rw [← herm_mulVec_left_eq G Y hdet]
    exact (hsd (Y *ᵥ x)).2 (hY x hx) y hy
  rw [← GlobalTheory.UCls.Det.herm_symm G hGh]
  exact h1.map (IsCMField.complexConj E)

end GlobalTheory.LieDisc

/- English proof (translation)
Introduce `_ _ _ _ r G Λ Y h hY` and use `GlobalTheory.LieDisc.hAdj_mem_endLat G Λ Y h hY`.
-/
theorem GlobalTheory.LieDisc.hAdj_mem_endLat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ :=
  fun _ _ _ _ r G Λ Y h hY => GlobalTheory.LieDisc.hAdj_mem_endLat G Λ Y h hY
