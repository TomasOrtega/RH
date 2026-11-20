import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Apply the tactic sequence `rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]`.
-/
private theorem vs_single {n : ℕ} (i : Fin n) (w : Fin n → ℂˣ) : monomialChar (Pi.single i 1 : Fin n → ℤ) w = w i := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

/- English proof (translation)
Introduce `n z σ τ`. Establish `hL : ∀ (s : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n) (w : Fin n → ℂˣ), monomialChar (∑ p ∈ s, (Pi.single (f p) 1 : Fin n → ℤ)) w = ∏ p ∈ s, (w (f p) : ℂ)`. Introduce `s f w`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [monomialChar_zero]`.

Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monomialChar_add, ih, vs_single]`. Establish `h1 : ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) = ∏ p ∈ pairs n, ((z (σ p.1) : ℂ) - z (τ p.2))`. Simplify using `only [sub_eq_add_neg]`. Rewrite using `[Finset.prod_add]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations.

Rewrite using `[eL, eR, hL S Prod.fst, hL _ Prod.snd, sgS, Finset.prod_neg]`. Simplify using `only [Function.comp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[dPol, map_prod]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, one_smul, evalAt_single, evalAt_single, vs_single, vs_single]`. Simplify using the standard rewrite rules.

Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises. Establish `hge : ∀ j, j ≤ (σ⁻¹ * τ) j` using `fun j => by`. Assume the negation of the conclusion as `hlt`. Use `hne (Finset.prod_eq_zero (i := ((σ⁻¹ * τ) j, j)) (by simpa [pairs] using hlt) ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hs : ∑ j : Fin n, (j : ℕ) = ∑ j : Fin n, (((σ⁻¹ * τ) j : Fin n) : ℕ)` using `(Equiv.sum_comp (σ⁻¹ * τ) fun j : Fin n => (j : ℕ)).symm`. Establish `he` using `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun (j : Fin n) _ => Fin.le_def.1 (hge j)).1 hs`. Establish `: σ⁻¹ * τ = 1` using `Equiv.ext fun j => (Fin.ext (he j (Finset.mem_univ _))).symm`. Conclude with `inv_mul_eq_one.1 this`.
-/
theorem UpperTheory.ConvolutionTheory.H.vandSum :
    ∀ (n : ℕ) (z : Fin n → ℂˣ) (σ τ : Equiv.Perm (Fin n)),
      ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) =
        if σ = τ then evalAt (z ∘ σ) (dPol n 1) else 0 := by
  intro n z σ τ
  have hL : ∀ (s : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n) (w : Fin n → ℂˣ),
      monomialChar (∑ p ∈ s, (Pi.single (f p) 1 : Fin n → ℤ)) w = ∏ p ∈ s, (w (f p) : ℂ) := by
    intro s f w
    classical
    induction s using Finset.induction_on with
    | empty => simp [monomialChar_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monomialChar_add, ih, vs_single]
  have h1 : ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) =
      ∏ p ∈ pairs n, ((z (σ p.1) : ℂ) - z (τ p.2)) := by
    simp only [sub_eq_add_neg]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [eL, eR, hL S Prod.fst, hL _ Prod.snd, sgS, Finset.prod_neg]
    simp only [Function.comp]
    ring
  rw [h1]
  split_ifs with h
  · subst h
    rw [dPol, map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [map_sub, one_smul, evalAt_single, evalAt_single, vs_single, vs_single]
    simp
  · by_contra hne
    apply h
    have hge : ∀ j, j ≤ (σ⁻¹ * τ) j := fun j => by
      by_contra hlt
      refine hne (Finset.prod_eq_zero (i := ((σ⁻¹ * τ) j, j)) (by simpa [pairs] using hlt) ?_)
      simp
    have hs : ∑ j : Fin n, (j : ℕ) = ∑ j : Fin n, (((σ⁻¹ * τ) j : Fin n) : ℕ) := (Equiv.sum_comp (σ⁻¹ * τ) fun j : Fin n => (j : ℕ)).symm
    have he := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun (j : Fin n) _ => Fin.le_def.1 (hge j)).1 hs
    have : σ⁻¹ * τ = 1 := Equiv.ext fun j => (Fin.ext (he j (Finset.mem_univ _))).symm
    exact inv_mul_eq_one.1 this
