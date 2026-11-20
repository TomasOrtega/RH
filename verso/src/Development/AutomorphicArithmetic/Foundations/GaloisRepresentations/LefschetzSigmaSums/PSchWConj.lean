import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
/- English proof (translation)
The claim follows from `(IsAlgClosed.splits p).roots_map _`.
-/
private lemma roots_map_sigma (σ : ℂ ≃+* ℂ) (p : ℂ[X]) :
    (p.map (σ : ℂ →+* ℂ)).roots = p.roots.map (σ : ℂ →+* ℂ) :=
  (IsAlgClosed.splits p).roots_map _

/- English proof (translation)
Unfold `UpperTheory.Gal.Schur.sch`. Conclude with `MvPolynomial.comp_aeval_apply (φ := (σ : ℂ →+* ℂ).toRatAlgHom) x _`.
-/
private lemma sigma_sch (σ : ℂ ≃+* ℂ) {n : ℕ} (μ : Fin n → ℕ) (x : Fin n → ℂ) :
    σ (UpperTheory.Gal.Schur.sch μ x) = UpperTheory.Gal.Schur.sch μ (fun i => σ (x i)) := by
  unfold UpperTheory.Gal.Schur.sch
  exact MvPolynomial.comp_aeval_apply (φ := (σ : ℂ →+* ℂ).toRatAlgHom) x _

/- English proof (translation)
Introduce `hE σ F _ _ n lam χ`. Distinguish the cases in `h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g`. Take `⟨g, hg⟩` from `h`. Establish `hg' : Lists χ (fun τ i => σ (g ((σ.symm : ℂ →+* ℂ).comp τ) i))`. Introduce `τ`.

Establish `h1 : χ.map τ = (χ.map ((σ.symm : ℂ →+* ℂ).comp τ)).map (σ : ℂ →+* ℂ)`. Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `h2` using `hg ((σ.symm : ℂ →+* ℂ).comp τ)`. Unfold `UpperTheory.Gal.W2.rts at h2 ⊢`. Rewrite using `[h1, roots_map_sigma, h2, Multiset.map_map]`. Both sides reduce to the same expression. Rewrite using `[hE F n (conjWt σ lam) χ _ hg', hE F n lam χ g hg, map_prod]`.

Set `e : (F →+* ℂ) ≃ (F →+* ℂ)` to `{ toFun := fun τ => (σ.symm : ℂ →+* ℂ).comp τ invFun := fun τ => (σ : ℂ →+* ℂ).comp τ left_inv := fun τ => by ext x; simp right_inv := fun τ => by ext x; simp }`. Use `Fintype.prod_equiv e _ _ fun τ => ?_` and prove the remaining obligations. Rewrite using `[sigma_sch]`. Both sides reduce to the same expression. Establish `h0 : schW lam χ = 0`.

Unfold `schW`. Conclude with `dif_neg h`. Establish `h1 : schW (conjWt σ lam) χ = 0`. Unfold `schW`. Conclude with `dif_neg h`.

Rewrite using `[h0, h1, map_zero]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.schWConj_of :
    SchWEq → SchWConj := by
  intro hE σ F _ _ n lam χ
  classical
  by_cases h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g
  · obtain ⟨g, hg⟩ := h
    have hg' : Lists χ (fun τ i => σ (g ((σ.symm : ℂ →+* ℂ).comp τ) i)) := by
      intro τ
      have h1 : χ.map τ = (χ.map ((σ.symm : ℂ →+* ℂ).comp τ)).map (σ : ℂ →+* ℂ) := by
        rw [Polynomial.map_map]
        congr 1
        ext x
        simp
      have h2 := hg ((σ.symm : ℂ →+* ℂ).comp τ)
      unfold UpperTheory.Gal.W2.rts at h2 ⊢
      rw [h1, roots_map_sigma, h2, Multiset.map_map]
      rfl
    rw [hE F n (conjWt σ lam) χ _ hg', hE F n lam χ g hg, map_prod]
    let e : (F →+* ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun τ => (σ.symm : ℂ →+* ℂ).comp τ
        invFun := fun τ => (σ : ℂ →+* ℂ).comp τ
        left_inv := fun τ => by ext x; simp
        right_inv := fun τ => by ext x; simp }
    refine Fintype.prod_equiv e _ _ fun τ => ?_
    rw [sigma_sch]
    rfl
  · have h0 : schW lam χ = 0 := by
      unfold schW
      exact dif_neg h
    have h1 : schW (conjWt σ lam) χ = 0 := by
      unfold schW
      exact dif_neg h
    rw [h0, h1, map_zero]
