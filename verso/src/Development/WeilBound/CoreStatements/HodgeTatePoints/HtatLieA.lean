import Mathlib

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

open TensorProduct

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `m hm`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hf m ?_` and prove the remaining obligations. Introduce and unpack `⟨_, i, rfl⟩`.

Take `⟨Q, _, _, a, -, h2⟩` from `h i`. Establish `h0 : (a ∘ₗ φ) m = (a ∘ₗ φ) 0`. Rewrite using `[LinearMap.comp_apply, LinearMap.mem_ker.1 hm, map_zero, map_zero]`. Take `⟨⟨_, k, rfl⟩, hk⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Simplify `hk` using `[Submonoid.smul_def]`. Introduce `n`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range φ) _ hf n ?_` and prove the remaining obligations. Introduce and unpack `⟨_, i, rfl⟩`. Take `⟨Q, _, _, a, h1, h2⟩` from `h i`.

Take `⟨⟨m, ⟨_, k, rfl⟩⟩, hk⟩` from `IsLocalizedModule.surj (Submonoid.powers (f i)) (a ∘ₗ φ) (a n)`. Establish `h0 : a (f i ^ k • n) = a (φ m)`. Rewrite using `[map_smul]`. Conclude with `hk`. Take `⟨⟨_, l, rfl⟩, hl⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0`.

Use `⟨l + k, f i ^ l • m, ?_⟩` and prove the remaining obligations. Establish `hl' : f i ^ l • f i ^ k • n = f i ^ l • φ m` using `hl`. Use `show φ (f i ^ l • m) = f i ^ (l + k) • n`. Rewrite using `[map_smul, pow_add, mul_smul, hl']`.
-/
theorem bijective_of_cover {R M N J : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) (φ : M →ₗ[R] N)
    (h : ∀ i, ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module R Q) (a : N →ₗ[R] Q),
      IsLocalizedModule (Submonoid.powers (f i)) a ∧ IsLocalizedModule (Submonoid.powers (f i)) (a ∘ₗ φ)) :
    Function.Bijective φ := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hf m ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, -, h2⟩ := h i
    have h0 : (a ∘ₗ φ) m = (a ∘ₗ φ) 0 := by
      rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hm, map_zero, map_zero]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨k, ?_⟩
    simpa [Submonoid.smul_def] using hk
  · intro n
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range φ) _ hf n ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, h1, h2⟩ := h i
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hk⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (a ∘ₗ φ) (a n)
    have h0 : a (f i ^ k • n) = a (φ m) := by
      rw [map_smul]
      exact hk
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨l + k, f i ^ l • m, ?_⟩
    have hl' : f i ^ l • f i ^ k • n = f i ^ l • φ m := hl
    show φ (f i ^ l • m) = f i ^ (l + k) • n
    rw [map_smul, pow_add, mul_smul, hl']

/- English proof (translation)
Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' A P`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Set `b : Fin n → P` to `fun k => π (fun j => if k = j then 1 else 0)`. Establish `hexp : ∀ p : P, ∑ k, s p k • b k = p`. Introduce `p`.

Establish `h1` using `LinearMap.congr_fun hs p`. Establish `h2` using `LinearMap.pi_apply_eq_sum_univ π (s p)`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h1`. Rewrite `h2` using `[h1]`. Conclude with `h2.symm`.

Set `co : Fin n → (P →ₗ[R] A)` to `fun k => (LinearMap.proj k ∘ₗ s).restrictScalars R`. Establish `hco : ∀ k p, co k p = s p k` using `fun _ _ => rfl`. Establish `hsum : ∀ φ : P →ₗ[R] A, ∑ k, φ (b k) • co k = φ`. Introduce `φ`. Use extensionality with `p`.

Use `conv_rhs => rw [← hexp p]`. Simplify using `[map_sum, hA, hco, mul_comm]`. Set `θ : C ⊗[A] (P →ₗ[R] A) →ₗ[C] (P →ₗ[R] C)` to `g.liftBaseChange C`. Establish `hθ : ∀ c φ, θ (c ⊗ₜ φ) = c • g φ` using `fun c φ => LinearMap.liftBaseChange_tmul _ _ _ _`. Set `inv : (P →ₗ[R] C) → C ⊗[A] (P →ₗ[R] A)` to `fun ψ => ∑ k, ψ (b k) ⊗ₜ co k`.

Establish `hl : ∀ z, inv (θ z) = z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp [inv]`. Consider the case `add x y hx hy`.

Establish `: inv (θ (x + y)) = inv (θ x) + inv (θ y)`. Simplify using `[inv, add_tmul, Finset.sum_add_distrib]`. Rewrite using `[this, hx, hy]`. Consider the case `tmul c φ`. Rewrite using `[hθ]`.

Use `conv_rhs => rw [← hsum φ, tmul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, hg, tmul_smul, smul_tmul', Algebra.smul_def (φ (b k)), smul_eq_mul, mul_comm]`. Establish `hr : ∀ ψ, θ (inv ψ) = ψ`. Introduce `ψ`.

Use extensionality with `p`. Use `conv_rhs => rw [← hexp p]`. Simplify using `only [inv, map_sum, hθ, LinearMap.sum_apply, LinearMap.smul_apply, hg, hco, hC, smul_eq_mul, mul_comm]`. Use `IsBaseChange.of_equiv (LinearEquiv.ofBijective θ ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩) fun φ => ?_` and prove the remaining obligations. Conclude with `(hθ 1 φ).trans (one_smul _ _)`.
-/
theorem isBaseChange_hom {R A C P : Type} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C] [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [Module.Finite A P] [Module.Projective A P]
    (hA : ∀ (φ : P →ₗ[R] A) (a : A) p, φ (a • p) = a * φ p)
    (hC : ∀ (φ : P →ₗ[R] C) (a : A) p, φ (a • p) = algebraMap A C a * φ p)
    (g : (P →ₗ[R] A) →ₗ[A] (P →ₗ[R] C)) (hg : ∀ φ p, g φ p = algebraMap A C (φ p)) : IsBaseChange C g := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  let co : Fin n → (P →ₗ[R] A) := fun k => (LinearMap.proj k ∘ₗ s).restrictScalars R
  have hco : ∀ k p, co k p = s p k := fun _ _ => rfl
  have hsum : ∀ φ : P →ₗ[R] A, ∑ k, φ (b k) • co k = φ := by
    intro φ
    ext p
    conv_rhs => rw [← hexp p]
    simp [map_sum, hA, hco, mul_comm]
  let θ : C ⊗[A] (P →ₗ[R] A) →ₗ[C] (P →ₗ[R] C) := g.liftBaseChange C
  have hθ : ∀ c φ, θ (c ⊗ₜ φ) = c • g φ := fun c φ => LinearMap.liftBaseChange_tmul _ _ _ _
  let inv : (P →ₗ[R] C) → C ⊗[A] (P →ₗ[R] A) := fun ψ => ∑ k, ψ (b k) ⊗ₜ co k
  have hl : ∀ z, inv (θ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [inv]
    | add x y hx hy =>
      have : inv (θ (x + y)) = inv (θ x) + inv (θ y) := by
        simp [inv, add_tmul, Finset.sum_add_distrib]
      rw [this, hx, hy]
    | tmul c φ =>
      rw [hθ]
      conv_rhs => rw [← hsum φ, tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.smul_apply, hg, tmul_smul, smul_tmul', Algebra.smul_def (φ (b k)), smul_eq_mul, mul_comm]
  have hr : ∀ ψ, θ (inv ψ) = ψ := by
    intro ψ
    ext p
    conv_rhs => rw [← hexp p]
    simp only [inv, map_sum, hθ, LinearMap.sum_apply, LinearMap.smul_apply, hg, hco, hC, smul_eq_mul, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ
    ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩) fun φ => ?_
  exact (hθ 1 φ).trans (one_smul _ _)

end PositivityTheory.HtPt.Htat.Lie
