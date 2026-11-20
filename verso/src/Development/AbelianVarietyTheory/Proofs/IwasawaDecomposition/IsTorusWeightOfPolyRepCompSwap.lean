import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

/- English proof (translation)
Introduce `n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j`. Use `set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ`. Use `set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP`. Establish `hσσ : ∀ k, σ (σ k) = k` using `fun k => Equiv.swap_apply_self _ _ _`. Establish `hPP : P * P = 1`.

Rewrite using `[hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]`. Establish `: σ.trans σ = Equiv.refl _` using `by ext k; simp [hσσ]`. Rewrite using `[this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]`. Set `p : GL (Fin n) ℂ` to `⟨P, P, hPP, hPP⟩`. Establish `hpp : p * p = 1` using `Units.ext hPP`.

Use `⟨Φ p *ᵥ w, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hw0` to reduce the goal to its premises. Establish `: Φ p *ᵥ (Φ p *ᵥ w) = 0` using `by rw [h]; simp`. Rewrite `this` using `[mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec]`. Then use the resulting hypothesis.

Introduce `D hD`. Establish `hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b)`. Introduce `a b`. Use `show (P * D.val * P) a b = _`. Rewrite using `[hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]`.

Simplify using `[hσ, Equiv.symm_swap]`. Establish `hD' : (p * D * p).val.IsDiag`. Introduce `a b hab`. Rewrite using `[hent]`. Conclude with `hD (fun h => hab (σ.injective h))`.

Establish `key : Φ D * Φ p = Φ p * Φ (p * D * p)`. Rewrite using `[← hΦ.mul, ← hΦ.mul]`. Use `congr 1`. Rewrite using `[← mul_assoc, ← mul_assoc, hpp, one_mul]`. Establish `hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k`.

Simplify using `only [hent, Function.comp]`. Rewrite using `[← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]`. Simplify using `[hσσ]`. Rewrite using `[mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]`.
-/
theorem isWt_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
    IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  intro n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
  have hPP : P * P = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have : σ.trans σ = Equiv.refl _ := by ext k; simp [hσσ]
    rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let p : GL (Fin n) ℂ := ⟨P, P, hPP, hPP⟩
  have hpp : p * p = 1 := Units.ext hPP
  refine ⟨Φ p *ᵥ w, ?_, ?_⟩
  · intro h
    apply hw0
    have : Φ p *ᵥ (Φ p *ᵥ w) = 0 := by rw [h]; simp
    rwa [mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec] at this
  · intro D hD
    have hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b) := by
      intro a b
      show (P * D.val * P) a b = _
      rw [hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      simp [hσ, Equiv.symm_swap]
    have hD' : (p * D * p).val.IsDiag := by
      intro a b hab
      rw [hent]
      exact hD (fun h => hab (σ.injective h))
    have key : Φ D * Φ p = Φ p * Φ (p * D * p) := by
      rw [← hΦ.mul, ← hΦ.mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k := by
      simp only [hent, Function.comp]
      rw [← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]
      simp [hσσ]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]
end GlobalTheory
