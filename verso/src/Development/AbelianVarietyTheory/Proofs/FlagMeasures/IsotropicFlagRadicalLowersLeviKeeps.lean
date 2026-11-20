import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagMem

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Simplify using `using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y`.
-/
theorem form_mul (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star (uMat g⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simpa using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

/- English proof (translation)
Establish `hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε` using `m.2`. Establish `h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`.

Use `_ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]`.
-/
theorem Jm_mul_conjTranspose (m : Formalism.REAL.UJ ε) :
    Formalism.REAL.Jm ε * (uMat m)ᴴ = uMat m⁻¹ * Formalism.REAL.Jm ε := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, GlobalTheory.FlagLeviGroup.uMat_mul_inv, Matrix.mul_one]
  calc Formalism.REAL.Jm ε * (uMat m)ᴴ
      = Formalism.REAL.Jm ε * ((uMat m)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]`.
-/
theorem form_conjTranspose (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat m)ᴴ *ᵥ y)) = star ((uMat m⁻¹)ᴴ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

/- English proof (translation)
Introduce `n ε a j W hW`. Use `⟨fun u hu => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `(GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1`. Establish `hu' : u⁻¹ ∈ flagN ε W`. Rewrite `hu`, the goal using `[← hN]`.

Conclude with `N.inv_mem hu`. Simplify using `only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]`. Use `⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `hy _ (hu'.1 i x hx)`. Rewrite `h` using `[star_sub, sub_dotProduct]`.

Rewrite using `[Matrix.mulVec_sub, dotProduct_sub, form_mul]`. Conclude with `h`. Establish `hm' : m⁻¹ ∈ flagM ε W` using `(GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm`. Simplify using `only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]`. Use `⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩, ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[form_mul]`. Conclude with `hy _ (hm' i x hx).1`. Rewrite using `[form_conjTranspose]`. Conclude with `hy _ (hm' i x hx).2`.
-/
theorem lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧
      ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  intro n ε a j W hW
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1
    have hu' : u⁻¹ ∈ flagN ε W := by
      rw [← hN] at hu ⊢
      exact N.inv_mem hu
    simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]
    refine ⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩
    have h := hy _ (hu'.1 i x hx)
    rw [star_sub, sub_dotProduct] at h
    rw [Matrix.mulVec_sub, dotProduct_sub, form_mul]
    exact h
  · have hm' : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm
    simp only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]
    refine ⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩,
      ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩
    · rw [form_mul]
      exact hy _ (hm' i x hx).1
    · rw [form_conjTranspose]
      exact hy _ (hm' i x hx).2

end GlobalTheory.IwConst.FlagMem
