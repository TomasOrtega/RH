import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KerTensor

/- English proof (translation)
Establish `hle : LinearMap.ker ev.toLinearMap ≤ LinearMap.ker ℓ` using `fun f hf => h f hf`. Establish `hs' : Function.Surjective ev.toLinearMap` using `hs`. Use `⟨(LinearMap.ker ev.toLinearMap).liftQ ℓ hle ∘ₗ (ev.toLinearMap.quotKerEquivOfSurjective hs').symm.toLinearMap, fun f => ?_⟩` and prove the remaining obligations. Establish `: (ev.toLinearMap.quotKerEquivOfSurjective hs').symm (ev f) = Submodule.Quotient.mk f`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]`.

Both sides reduce to the same expression. Simplify using `[this]`.
-/
theorem exists_factor {O σ A M : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module O M]
    (ev : MvPowerSeries σ O →ₐ[O] A) (hs : Function.Surjective ev)
    (ℓ : MvPowerSeries σ O →ₗ[O] M) (h : ∀ f, ev f = 0 → ℓ f = 0) :
    ∃ l : A →ₗ[O] M, ∀ f, l (ev f) = ℓ f := by
  have hle : LinearMap.ker ev.toLinearMap ≤ LinearMap.ker ℓ := fun f hf => h f hf
  have hs' : Function.Surjective ev.toLinearMap := hs
  refine ⟨(LinearMap.ker ev.toLinearMap).liftQ ℓ hle ∘ₗ
    (ev.toLinearMap.quotKerEquivOfSurjective hs').symm.toLinearMap, fun f => ?_⟩
  have : (ev.toLinearMap.quotKerEquivOfSurjective hs').symm (ev f) = Submodule.Quotient.mk f := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]; rfl
  simp [this]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.coe_C, MvPolynomial.aeval_C, ← ev.commutes a]`. Both sides reduce to the same expression. Consider the case `add p q hp hq => rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]`.

Consider the case `mul_X p i hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, hx, MvPolynomial.aeval_X]`.
-/
theorem eval_coe {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (P : MvPolynomial σ O) :
    ev (P : MvPowerSeries σ O) = MvPolynomial.aeval x P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.coe_C, MvPolynomial.aeval_C, ← ev.commutes a]
    rfl
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, hx,
      MvPolynomial.aeval_X]

/- English proof (translation)
Rewrite using `[eval_coe ev x hx, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Algebra.smul_def]`.
-/
theorem eval_monomial {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (γ : σ →₀ ℕ) (c : O) :
    ev ((MvPolynomial.monomial γ c : MvPolynomial σ O) : MvPowerSeries σ O) =
      c • ∏ i, x i ^ γ i := by
  rw [eval_coe ev x hx, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Algebra.smul_def]

/- English proof (translation)
Rewrite using `[Finsupp.degree_eq_sum]`. Conclude with `Finset.single_le_sum (f := fun i => γ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`.
-/
theorem le_degree {σ : Type} [Fintype σ] (γ : σ →₀ ℕ) (k : σ) : γ k ≤ γ.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (f := fun i => γ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/- English proof (translation)
Simplify using `only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.coe_equivFunOnFinite_symm]`.
-/
theorem degree_sum {σ τ : Type} [Fintype σ] [Fintype τ] (γ : σ ⊕ τ →₀ ℕ) :
    γ.degree = (Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) : σ →₀ ℕ).degree +
      (Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) : τ →₀ ℕ).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.coe_equivFunOnFinite_symm]

end GlobalTheory.KerTensor

namespace GlobalTheory.KerTensor

/- English proof (translation)
Introduce `p O A B σ τ _ _ _ _ _ _ _ x y evA evB E m N hA hB hE sA sB kA kB f hf α hα`. Use `set I : Ideal O := Ideal.span {(p : O) ^ m} with hI`. Establish `fact : ∀ {ρ R : Type} [CommRing R] [Algebra O R] (ev : MvPowerSeries ρ O →ₐ[O] R), Function.Surjective ev → (∀ f, ev f = 0 → ∀ α : ρ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ β : ρ →₀ ℕ, β.degree < N → ∃ l : R →ₗ[O] O ⧸ I, ∀ g, l (ev g) = Ideal.Quotient.mk I (coeff β g)`. Introduce `ρ R _ _ ev hs hk β hβ`. Take `⟨l, hl⟩` from `exists_factor ev hs ((Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ coeff β) (fun g hg => by`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hI]`. Conclude with `Ideal.mem_span_singleton.2 (hk g hg β hβ))`. Conclude with `⟨l, fun g => by rw [hl]; rfl⟩`. Establish `hdeg` using `degree_sum α`. Use `set α₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => α (Sum.inl i) with hα₁`.

Use `set α₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α (Sum.inr j) with hα₂`. Take `⟨l1, hl1⟩` from `fact evA sA kA α₁ (by omega)`. Take `⟨l2, hl2⟩` from `fact evB sB kB α₂ (by omega)`. Set `Λ : A ⊗[O] B →ₗ[O] O ⧸ I` to `TensorProduct.lift ((LinearMap.mul O (O ⧸ I)).compl₁₂ l1 l2)`. Establish `hΛ : ∀ a b, Λ (a ⊗ₜ b) = l1 a * l2 b` using `fun a b => by simp [Λ]`.

Establish `hmono : ∀ (γ : σ ⊕ τ →₀ ℕ) (c : O), Λ (E ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) = Ideal.Quotient.mk I (coeff α ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O))`. Introduce `γ c`. Use `set γ₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) with hγ₁`. Use `set γ₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) with hγ₂`. Establish `e1` using `eval_monomial evA x hA.1 γ₁ 1`.

Establish `e2` using `eval_monomial evB y hB.1 γ₂ 1`. Establish `eE` using `eval_monomial E _ hE.1 γ c`. Establish `split : (∏ k, (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) k ^ γ k) = (∏ i, x i ^ γ₁ i) ⊗ₜ[O] (∏ j, y j ^ γ₂ j)`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, hγ₁, hγ₂, Finsupp.coe_equivFunOnFinite_symm]`.

Establish `h1 : (∏ i, (x i ⊗ₜ[O] (1 : B)) ^ γ (Sum.inl i)) = (∏ i, x i ^ γ (Sum.inl i)) ⊗ₜ[O] (1 : B)`. Rewrite using `[← Algebra.TensorProduct.includeLeft_apply (S := O), map_prod]`. Simplify using `only [map_pow, Algebra.TensorProduct.includeLeft_apply]`. Establish `h2 : (∏ j, ((1 : A) ⊗ₜ[O] y j) ^ γ (Sum.inr j)) = (1 : A) ⊗ₜ[O] (∏ j, y j ^ γ (Sum.inr j))`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply, map_prod]`.

Simplify using `only [map_pow, Algebra.TensorProduct.includeRight_apply]`. Rewrite using `[h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[eE, split, map_smul, hΛ, ← one_smul O (∏ i, x i ^ γ₁ i), ← e1, ← one_smul O (∏ j, y j ^ γ₂ j), ← e2, hl1, hl2]`. Simplify using `only [MvPolynomial.coe_monomial, coeff_monomial]`. Establish `hiff : α = γ ↔ α₁ = γ₁ ∧ α₂ = γ₂`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `⟨h1, h2⟩`. Use extensionality with `k`.

Consider the cases of `k with`. Consider the case `inl i => simpa [hα₁, hγ₁] using congrArg (fun g => g i) h1`. Consider the case `inr j => simpa [hα₂, hγ₂] using congrArg (fun g => g j) h2`. Distinguish the cases in `h : α = γ`. Rewrite using `[if_pos h, if_pos (hiff.1 h).1, if_pos (hiff.1 h).2]`.

Simplify using `[Algebra.smul_def]`. Rewrite using `[if_neg h]`. Distinguish the cases in `h1 : α₁ = γ₁`. Rewrite using `[if_neg (fun h2 => h (hiff.2 ⟨h1, h2⟩))]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h1]`. Simplify using the standard rewrite rules. Establish `hpoly : ∀ P : MvPolynomial (σ ⊕ τ) O, Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = Ideal.Quotient.mk I (coeff α (P : MvPowerSeries (σ ⊕ τ) O))`. Introduce `P`. Proceed by induction on `P using MvPolynomial.induction_on' with`.

Consider the case `monomial γ c => exact hmono γ c`. Consider the case `add P Q hP hQ => rw [MvPolynomial.coe_add, map_add, map_add, hP, hQ, map_add, map_add]`. Take `⟨N', hN'⟩` from `hE.2 m`. Use `set K := max N' N with hK`. Use `set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => K) f with hP`.

Establish `hrest : ∀ γ : σ ⊕ τ →₀ ℕ, γ.degree < K → coeff γ (f - (P : MvPowerSeries (σ ⊕ τ) O)) = 0`. Introduce `γ hγ`. Establish `hle : γ ≤ Finsupp.equivFunOnFinite.symm fun _ => K`. Introduce `k`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`.

Conclude with `le_of_lt (lt_of_le_of_lt (le_degree γ k) hγ)`. Rewrite using `[map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos hle, sub_self]`. Take `⟨c, hc⟩` from `hN' (f - (P : MvPowerSeries (σ ⊕ τ) O)) (fun γ hγ => hrest γ (lt_of_lt_of_le hγ (le_max_left _ _)))`. Establish `hzero : Λ (E (f - (P : MvPowerSeries (σ ⊕ τ) O))) = 0`. Rewrite using `[hc]`.

Establish `: (p : A ⊗[O] B) ^ m * c = ((p : O) ^ m) • c`. Rewrite using `[Algebra.smul_def, map_pow, map_natCast]`. Rewrite using `[this, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul]`. Establish `hsplit : E f = E (P : MvPowerSeries (σ ⊕ τ) O) + E (f - (P : MvPowerSeries (σ ⊕ τ) O))`. Rewrite using `[← map_add, add_sub_cancel]`.

Establish `hPval : Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = 0`. Use `congrArg Λ hsplit` as an intermediate fact. Rewrite `this` using `[hf, map_zero, map_add, hzero, add_zero]`. Conclude with `this.symm`. Establish `hcoeff : coeff α f = coeff α (P : MvPowerSeries (σ ⊕ τ) O)`.

Use `hrest α (lt_of_lt_of_le hα (le_max_right _ _))` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this`. Establish `hmk : Ideal.Quotient.mk I (coeff α f) = 0` using `by rw [hcoeff, ← hpoly, hPval]`. Conclude with `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)`.
-/
theorem ker_tensor : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p O A B σ τ _ _ _ _ _ _ _ x y evA evB E m N hA hB hE sA sB kA kB f hf α hα
  classical
  set I : Ideal O := Ideal.span {(p : O) ^ m} with hI
  have fact : ∀ {ρ R : Type} [CommRing R] [Algebra O R] (ev : MvPowerSeries ρ O →ₐ[O] R),
      Function.Surjective ev → (∀ f, ev f = 0 → ∀ α : ρ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
      ∀ β : ρ →₀ ℕ, β.degree < N → ∃ l : R →ₗ[O] O ⧸ I, ∀ g, l (ev g) = Ideal.Quotient.mk I (coeff β g) := by
    intro ρ R _ _ ev hs hk β hβ
    obtain ⟨l, hl⟩ := exists_factor ev hs ((Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ coeff β) (fun g hg => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.mem_span_singleton.2 (hk g hg β hβ))
    exact ⟨l, fun g => by rw [hl]; rfl⟩
  have hdeg := degree_sum α
  set α₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => α (Sum.inl i) with hα₁
  set α₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α (Sum.inr j) with hα₂
  obtain ⟨l1, hl1⟩ := fact evA sA kA α₁ (by omega)
  obtain ⟨l2, hl2⟩ := fact evB sB kB α₂ (by omega)
  let Λ : A ⊗[O] B →ₗ[O] O ⧸ I := TensorProduct.lift ((LinearMap.mul O (O ⧸ I)).compl₁₂ l1 l2)
  have hΛ : ∀ a b, Λ (a ⊗ₜ b) = l1 a * l2 b := fun a b => by simp [Λ]

  have hmono : ∀ (γ : σ ⊕ τ →₀ ℕ) (c : O),
      Λ (E ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) =
        Ideal.Quotient.mk I (coeff α ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) := by
    intro γ c
    set γ₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) with hγ₁
    set γ₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) with hγ₂
    have e1 := eval_monomial evA x hA.1 γ₁ 1
    have e2 := eval_monomial evB y hB.1 γ₂ 1
    have eE := eval_monomial E _ hE.1 γ c
    have split : (∏ k, (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) k ^ γ k) =
        (∏ i, x i ^ γ₁ i) ⊗ₜ[O] (∏ j, y j ^ γ₂ j) := by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hγ₁, hγ₂, Finsupp.coe_equivFunOnFinite_symm]
      have h1 : (∏ i, (x i ⊗ₜ[O] (1 : B)) ^ γ (Sum.inl i)) = (∏ i, x i ^ γ (Sum.inl i)) ⊗ₜ[O] (1 : B) := by
        rw [← Algebra.TensorProduct.includeLeft_apply (S := O), map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeLeft_apply]
      have h2 : (∏ j, ((1 : A) ⊗ₜ[O] y j) ^ γ (Sum.inr j)) = (1 : A) ⊗ₜ[O] (∏ j, y j ^ γ (Sum.inr j)) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeRight_apply]
      rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [eE, split, map_smul, hΛ, ← one_smul O (∏ i, x i ^ γ₁ i), ← e1, ← one_smul O (∏ j, y j ^ γ₂ j),
      ← e2, hl1, hl2]
    simp only [MvPolynomial.coe_monomial, coeff_monomial]
    have hiff : α = γ ↔ α₁ = γ₁ ∧ α₂ = γ₂ := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        ext k
        cases k with
        | inl i => simpa [hα₁, hγ₁] using congrArg (fun g => g i) h1
        | inr j => simpa [hα₂, hγ₂] using congrArg (fun g => g j) h2
    by_cases h : α = γ
    · rw [if_pos h, if_pos (hiff.1 h).1, if_pos (hiff.1 h).2]
      simp [Algebra.smul_def]
    · rw [if_neg h]
      by_cases h1 : α₁ = γ₁
      · rw [if_neg (fun h2 => h (hiff.2 ⟨h1, h2⟩))]; simp
      · rw [if_neg h1]; simp
  have hpoly : ∀ P : MvPolynomial (σ ⊕ τ) O,
      Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = Ideal.Quotient.mk I (coeff α (P : MvPowerSeries (σ ⊕ τ) O)) := by
    intro P
    induction P using MvPolynomial.induction_on' with
    | monomial γ c => exact hmono γ c
    | add P Q hP hQ => rw [MvPolynomial.coe_add, map_add, map_add, hP, hQ, map_add, map_add]

  obtain ⟨N', hN'⟩ := hE.2 m
  set K := max N' N with hK
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => K) f with hP
  have hrest : ∀ γ : σ ⊕ τ →₀ ℕ, γ.degree < K → coeff γ (f - (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    intro γ hγ
    have hle : γ ≤ Finsupp.equivFunOnFinite.symm fun _ => K := by
      intro k
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact le_of_lt (lt_of_le_of_lt (le_degree γ k) hγ)
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨c, hc⟩ := hN' (f - (P : MvPowerSeries (σ ⊕ τ) O))
    (fun γ hγ => hrest γ (lt_of_lt_of_le hγ (le_max_left _ _)))
  have hzero : Λ (E (f - (P : MvPowerSeries (σ ⊕ τ) O))) = 0 := by
    rw [hc]
    have : (p : A ⊗[O] B) ^ m * c = ((p : O) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul]
  have hsplit : E f = E (P : MvPowerSeries (σ ⊕ τ) O) + E (f - (P : MvPowerSeries (σ ⊕ τ) O)) := by
    rw [← map_add, add_sub_cancel]
  have hPval : Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    have := congrArg Λ hsplit
    rw [hf, map_zero, map_add, hzero, add_zero] at this
    exact this.symm
  have hcoeff : coeff α f = coeff α (P : MvPowerSeries (σ ⊕ τ) O) := by
    have := hrest α (lt_of_lt_of_le hα (le_max_right _ _))
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hmk : Ideal.Quotient.mk I (coeff α f) = 0 := by rw [hcoeff, ← hpoly, hPval]
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)

end GlobalTheory.KerTensor
