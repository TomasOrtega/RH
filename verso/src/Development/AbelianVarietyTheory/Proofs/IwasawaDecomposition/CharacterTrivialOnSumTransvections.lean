import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

/- English proof (translation)
Introduce `E _ _ _ N X φ d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `ξ α _ _`. Use `⟨1, ?_, map_one φ⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `ξ α horth hγ`. Take `⟨γ0, h0, hφ0⟩` from `ih (ξ ∘ Fin.castSucc) (α ∘ Fin.castSucc) (fun i j => horth _ _) (fun j => hγ _)`. Take `⟨γl, hl, hφl⟩` from `hγ (Fin.last d)`.

Use `⟨γ0 * γl, ?_, by rw [map_mul, hφ0, hφl, one_mul]⟩` and prove the remaining obligations. Establish `hmat : ((γ0 * γl : X.Γ) : GL (Fin N) E) = (γ0 : GL (Fin N) E) * (γl : GL (Fin N) E)` using `rfl`. Rewrite using `[hmat, Matrix.GeneralLinearGroup.coe_mul, h0, hl, transvMat_eq, Fin.sum_univ_castSucc]`. Establish `hz : (∑ j : Fin d, (α ∘ Fin.castSucc) j • rk1 X.Gm ((ξ ∘ Fin.castSucc) j) ((ξ ∘ Fin.castSucc) j)) * (α (Fin.last d) • rk1 X.Gm (ξ (Fin.last d)) (ξ (Fin.last d))) = 0`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, one_add_smul_vecMulVec_mul]`. Simplify using `only [Function.comp_apply, horth, zero_smul, smul_zero]`. Rewrite using `[add_mul, one_mul, mul_add, mul_one, hz, add_zero]`. Simplify using `only [Function.comp]`.

Normalize the expressions using the abelian group laws.
-/
theorem exists_mem_sum_transv_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (φ : X.Γ →* Multiplicative ℝ) (d : ℕ) (ξ : Fin d → Fin N → E) (α : Fin d → E), (∀ i j, herm X.Gm (ξ i) (ξ j) = 0) → (∀ j, ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ j) (α j) ∧ φ γ = 1) → ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 + ∑ j, α j • rk1 X.Gm (ξ j) (ξ j) ∧ φ γ = 1 := by
  intro E _ _ _ N X φ d
  induction d with
  | zero =>
    intro ξ α _ _
    refine ⟨1, ?_, map_one φ⟩
    simp
  | succ d ih =>
    intro ξ α horth hγ
    obtain ⟨γ0, h0, hφ0⟩ := ih (ξ ∘ Fin.castSucc) (α ∘ Fin.castSucc)
      (fun i j => horth _ _) (fun j => hγ _)
    obtain ⟨γl, hl, hφl⟩ := hγ (Fin.last d)
    refine ⟨γ0 * γl, ?_, by rw [map_mul, hφ0, hφl, one_mul]⟩
    have hmat : ((γ0 * γl : X.Γ) : GL (Fin N) E) = (γ0 : GL (Fin N) E) * (γl : GL (Fin N) E) := rfl
    rw [hmat, Matrix.GeneralLinearGroup.coe_mul, h0, hl, transvMat_eq, Fin.sum_univ_castSucc]
    have hz : (∑ j : Fin d, (α ∘ Fin.castSucc) j • rk1 X.Gm ((ξ ∘ Fin.castSucc) j) ((ξ ∘ Fin.castSucc) j))
        * (α (Fin.last d) • rk1 X.Gm (ξ (Fin.last d)) (ξ (Fin.last d))) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, one_add_smul_vecMulVec_mul]
      simp only [Function.comp_apply, horth, zero_smul, smul_zero]
    rw [add_mul, one_mul, mul_add, mul_one, hz, add_zero]
    simp only [Function.comp]
    abel

end GlobalTheory.UnipKill
