import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrimeStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in

/- English proof (translation)
Establish `eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a)` using `fun a => by`. Simplify using `[sumAlgEquiv_C_inl]`. Establish `eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t` using `fun t => by`. Simplify using `[sumAlgEquiv_X_inl]`. Establish `eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s)` using `fun s => by`.

Simplify using `[sumAlgEquiv_X_inr]`. Establish `hX : ∀ v : τ ⊕ σ, d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v))`. Introduce `v`. Apply the tactic sequence `rcases u with t | s <;> rcases v with t' | s'`. Rewrite using `[eL, h1]`.

Distinguish the cases in `h : t = t'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]`. Rewrite using `[eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]`.

Rewrite using `[eL, h3, pderiv_X_of_ne (by simp), map_zero]`. Rewrite using `[eR, h2]`. Distinguish the cases in `h : s = s'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero, map_zero]`. Proceed by induction on `y using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[eC, pderiv_C, map_zero]`. Break down `u with t | s` into its components or cases.

Rewrite using `[h1, pderiv_C]`. Rewrite using `[h2, pderiv_C, map_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]`.
-/
theorem derivation_sumAlgEquiv_eq_pderiv {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by
  classical
  have eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a) := fun a => by
    simp [sumAlgEquiv_C_inl]
  have eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t := fun t => by
    simp [sumAlgEquiv_X_inl]
  have eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s) := fun s => by
    simp [sumAlgEquiv_X_inr]
  have hX : ∀ v : τ ⊕ σ,
      d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v)) := by
    intro v
    rcases u with t | s <;> rcases v with t' | s'
    · rw [eL, h1]
      by_cases h : t = t'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]
    · rw [eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]
    · rw [eL, h3, pderiv_X_of_ne (by simp), map_zero]
    · rw [eR, h2]
      by_cases h : s = s'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero,
          map_zero]
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [eC, pderiv_C, map_zero]
    rcases u with t | s
    · rw [h1, pderiv_C]
    · rw [h2, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]

/- English proof (translation)
Introduce `Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3`. Set `e` to `MvPolynomial.sumAlgEquiv Λ τ σ`. Establish `eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a)` using `fun a => by`. Simplify using `[e, MvPolynomial.sumAlgEquiv_C_inl]`. Take `⟨h, f, s, g, hg, hf, hx, hdet⟩` from `GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e) (fun a ha => hQ a (by rw [← eC]; exact ha))`.

Use `⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩` and prove the remaining obligations. Establish `h4` using `hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)`. Establish `h5` using `Ideal.mem_map_of_mem e h4`. Rewrite `h5` using `[Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply]`. Conclude with `h5`.

Introduce `hmem`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[Ideal.mem_comap, AlgEquiv.map_det]`. Use `hmem using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j : 1`.

Conclude with `(derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm`.
-/
theorem exists_generic_jacobian_data_iterated : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  intro Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3
  let e := MvPolynomial.sumAlgEquiv Λ τ σ
  have eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := fun a => by
    simp [e, MvPolynomial.sumAlgEquiv_C_inl]
  obtain ⟨h, f, s, g, hg, hf, hx, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e)
    (fun a ha => hQ a (by rw [← eC]; exact ha))
  refine ⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩
  · have h4 := hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)
    have h5 := Ideal.mem_map_of_mem e h4
    rw [Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply] at h5
    exact h5
  · intro hmem
    apply hdet
    rw [Ideal.mem_comap, AlgEquiv.map_det]
    convert hmem using 2
    ext i j : 1
    exact (derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm

end GlobalTheory
