import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import GroundTheory.AutomorphicForms.Satake

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `n Φ`. Use `⟨polyEmb n (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _`. Introduce `τ`. Rewrite using `[← polyEmb_rename]`.

Use `congr 1`. Rewrite using `[map_prod]`. Repeatedly rewrite using `[MvPolynomial.rename_rename]`. Conclude with `Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)`. Introduce `z`.

Rewrite using `[evalAt_polyEmb, map_prod]`. Use `Finset.prod_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_rename]`. Both sides reduce to the same expression. Introduce `hΦ`.

Use `⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `σ _ h`. Apply `hΦ` to reduce the goal to its premises. Conclude with `MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])`.

Rewrite using `[evalAt_polyEmb]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Gen.symEx_pf :
    UpperTheory.Gal.Gen.SymEx := by
  intro n Φ
  refine ⟨polyEmb n (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩
  · show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _
    intro τ
    rw [← polyEmb_rename]
    congr 1
    rw [map_prod]
    simp_rw [MvPolynomial.rename_rename]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  · intro z
    rw [evalAt_polyEmb, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [MvPolynomial.aeval_rename]
    rfl
  · intro hΦ
    refine ⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro σ _ h
      apply hΦ
      exact MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])
    · rw [evalAt_polyEmb]
      rfl
