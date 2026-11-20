import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Introduce `n l y`. Establish `hb : ∀ (a : Fin n → ℤ) (c : ℂ), bc l (AddMonoidAlgebra.single a c : LaurentRing n) = AddMonoidAlgebra.single ((l : ℤ) • a) c`. Introduce `a c`. Simplify using `[bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]`. Establish `hc : ∀ (σ : Equiv.Perm (Fin n)) (y : LaurentRing n), bc l (permAct σ y) = permAct σ (bc l y)` using `fun σ y => by`.

Establish `: (bc l).comp (permAct σ) = (permAct σ).comp (bc (n` using `n) l) := AddMonoidAlgebra.algHom_ext (fun a => by`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, permAct_single, hb, hb, permAct_single]`. Use the proof step `rfl) (Subsingleton.elim _ _)`. Conclude with `AlgHom.congr_fun this y`. Use `⟨fun τ => ?_, ?_, fun p hp => ?_, fun hy σ => ?_, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[symSum, map_sum]`. Simplify using `only [permAct_permAct]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl`. Rewrite using `[symSum, symSum, map_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ => hc σ y`.

Rewrite using `[symSum, symSum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun σ _ => by rw [map_mul, hp σ]`. Rewrite using `[← hc, hy σ]`. Establish `: (evalAt z).comp (bc l) = evalAt (z ^ l)` using `AddMonoidAlgebra.algHom_ext (fun a => by`. Rewrite using `[AlgHom.comp_apply, hb, evalAt_single, evalAt_single, monomialChar_apply, monomialChar_apply]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, zpow_mul, zpow_natCast, Pi.pow_apply]) (Subsingleton.elim _ _)`. Conclude with `AlgHom.congr_fun this y`.
-/
theorem UpperTheory.ConvolutionTheory.H.symAlg :
    ∀ (n l : ℕ) (y : LaurentRing n), symSum y ∈ symmetricLaurent n ∧ bc l (symSum y) = symSum (bc l y) ∧
      (∀ p ∈ symmetricLaurent n, symSum (y * p) = symSum y * p) ∧ (y ∈ symmetricLaurent n → bc l y ∈ symmetricLaurent n) ∧
      ∀ z : Fin n → ℂˣ, evalAt z (bc l y) = evalAt (z ^ l) y := by
  intro n l y
  have hb : ∀ (a : Fin n → ℤ) (c : ℂ), bc l (AddMonoidAlgebra.single a c : LaurentRing n) = AddMonoidAlgebra.single ((l : ℤ) • a) c := by
    intro a c
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  have hc : ∀ (σ : Equiv.Perm (Fin n)) (y : LaurentRing n), bc l (permAct σ y) = permAct σ (bc l y) := fun σ y => by
    have : (bc l).comp (permAct σ) = (permAct σ).comp (bc (n := n) l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, permAct_single, hb, hb, permAct_single]; rfl) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
  refine ⟨fun τ => ?_, ?_, fun p hp => ?_, fun hy σ => ?_, fun z => ?_⟩
  · rw [symSum, map_sum]
    simp only [permAct_permAct]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl
  · rw [symSum, symSum, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc σ y
  · rw [symSum, symSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by rw [map_mul, hp σ]
  · rw [← hc, hy σ]
  · have : (evalAt z).comp (bc l) = evalAt (z ^ l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, hb, evalAt_single, evalAt_single, monomialChar_apply, monomialChar_apply]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, zpow_mul, zpow_natCast, Pi.pow_apply]) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
