import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `H using MvPolynomial.induction_on with`. Consider the case `C c`. Apply the tactic sequence `refine ⟨0, Polynomial.C (MvPolynomial.C c), ?_, ?_⟩ <;> simp`. Consider the case `add p q hp hq`. Take `⟨N1, R1, h1, h1'⟩` from `hp`.

Take `⟨N2, R2, h2, h2'⟩` from `hq`. Use `⟨N1 + N2, R1 * Polynomial.C Δ ^ N2 + R2 * Polynomial.C Δ ^ N1, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, h1, h2, map_add]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, h1', h2', map_add]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p j hp`. Take `⟨N, R, h, h'⟩` from `hp`.

Use `⟨N + 1, R * Q j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_mul, h, hQ]`. Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Polynomial.eval₂_mul, h', hb]`.

Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem specialisation_clear_denominators {k C : Type} [Field k] [Field C] [Algebra k C] {m d : ℕ}
    (a : Fin m → C) (t : Fin d → C) (θ : C) (Δ : MvPolynomial (Fin d) k)
    (Q : Fin m → Polynomial (MvPolynomial (Fin d) k))
    (hQ : ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) = MvPolynomial.aeval t Δ * a j)
    {B : Type} [Field B] [Algebra k B] (t' : Fin d → B) (θ' : B) (b : Fin m → B)
    (hb : ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) = MvPolynomial.aeval t' Δ * b j)
    (H : MvPolynomial (Fin m) k) :
    ∃ (N : ℕ) (R : Polynomial (MvPolynomial (Fin d) k)),
      Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ R =
          MvPolynomial.aeval t Δ ^ N * MvPolynomial.aeval a H ∧
      Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' R =
          MvPolynomial.aeval t' Δ ^ N * MvPolynomial.aeval b H := by
  induction H using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, Polynomial.C (MvPolynomial.C c), ?_, ?_⟩ <;> simp
  | add p q hp hq =>
    obtain ⟨N1, R1, h1, h1'⟩ := hp
    obtain ⟨N2, R2, h2, h2'⟩ := hq
    refine ⟨N1 + N2, R1 * Polynomial.C Δ ^ N2 + R2 * Polynomial.C Δ ^ N1, ?_, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        h1, h2, map_add]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        h1', h2', map_add]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
  | mul_X p j hp =>
    obtain ⟨N, R, h, h'⟩ := hp
    refine ⟨N + 1, R * Q j, ?_, ?_⟩
    · rw [Polynomial.eval₂_mul, h, hQ]
      simp only [map_mul, MvPolynomial.aeval_X]
      ring
    · rw [Polynomial.eval₂_mul, h', hb]
      simp only [map_mul, MvPolynomial.aeval_X]
      ring

/- English proof (translation)
Introduce `k C _ _ _ m d a t θ P Δ Q hΔ hQ hP B _ _ t' θ' hΔ' hP'`. Use `set b : Fin m → B := fun j => Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) / MvPolynomial.aeval t' Δ with hbdef`. Establish `hb : ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) = MvPolynomial.aeval t' Δ * b j`. Introduce `j`. Rewrite using `[hbdef]`.

Clear the denominators using the available nonvanishing facts. Set `Ψ : MvPolynomial (Fin m) k →ₐ[k] B` to `MvPolynomial.aeval b`. Set `g : MvPolynomial (Fin m) k →ₐ[k] Algebra.adjoin k (Set.range a)` to `(MvPolynomial.aeval a).codRestrict (Algebra.adjoin k (Set.range a)) (by`. Introduce `x`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`.

Conclude with `⟨x, rfl⟩)`. Establish `hg : Function.Surjective g`. Introduce and unpack `⟨y, hy⟩`. Rewrite `hy` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨x, rfl⟩` from `hy`.

Conclude with `⟨x, rfl⟩`. Establish `hker : ∀ H ∈ RingHom.ker g, Ψ H = 0`. Introduce `H hH`. Establish `h0 : MvPolynomial.aeval a H = 0`. Use `congrArg Subtype.val (RingHom.mem_ker.mp hH)` as an intermediate fact.

Simplify `this` using `[g]`. Take `⟨N, R, hR, hR'⟩` from `specialisation_clear_denominators a t θ Δ Q hQ t' θ' b hb H`. Rewrite `hR` using `[h0, mul_zero]`. Take `⟨S, rfl⟩` from `hP R hR`. Rewrite `hR'` using `[Polynomial.eval₂_mul, hP', zero_mul]`.

Use `(mul_eq_zero.mp hR'.symm).resolve_left (pow_ne_zero _ hΔ')` as an intermediate fact. Conclude with `this`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hg`. Use `⟨(Ideal.Quotient.liftₐ (RingHom.ker g) Ψ hker).comp e.symm.toAlgHom, ?_⟩` and prove the remaining obligations. Introduce `j`.

Establish `he : e.symm ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ = Ideal.Quotient.mkₐ k (RingHom.ker g) (MvPolynomial.X j)`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[e, g]`. Rewrite using `[hb j]`.

Use `congr 1`. Use `show b j = Ideal.Quotient.liftₐ (RingHom.ker g) Ψ hker (e.symm _)`. Rewrite using `[he, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk]`. Use `erw [Ideal.Quotient.lift_mk]`. Simplify using `[Ψ]`.
-/
theorem specialisation_lift : ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (m d : ℕ) (a : Fin m → C) (t : Fin d → C) (θ : C) (P : Polynomial (MvPolynomial (Fin d) k)) (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)), MvPolynomial.aeval t Δ ≠ 0 → (∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) = MvPolynomial.aeval t Δ * a j) → (∀ R : Polynomial (MvPolynomial (Fin d) k), Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ R = 0 → P ∣ R) → ∀ (B : Type) [Field B] [Algebra k B] (t' : Fin d → B) (θ' : B), MvPolynomial.aeval t' Δ ≠ 0 → Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' P = 0 → ∃ f : Algebra.adjoin k (Set.range a) →ₐ[k] B, ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) = MvPolynomial.aeval t' Δ * f ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ := by
  intro k C _ _ _ m d a t θ P Δ Q hΔ hQ hP B _ _ t' θ' hΔ' hP'
  set b : Fin m → B := fun j =>
    Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) / MvPolynomial.aeval t' Δ with hbdef
  have hb : ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) =
      MvPolynomial.aeval t' Δ * b j := by
    intro j; rw [hbdef]; field_simp
  let Ψ : MvPolynomial (Fin m) k →ₐ[k] B := MvPolynomial.aeval b
  let g : MvPolynomial (Fin m) k →ₐ[k] Algebra.adjoin k (Set.range a) :=
    (MvPolynomial.aeval a).codRestrict (Algebra.adjoin k (Set.range a)) (by
      intro x
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨x, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker : ∀ H ∈ RingHom.ker g, Ψ H = 0 := by
    intro H hH
    have h0 : MvPolynomial.aeval a H = 0 := by
      have := congrArg Subtype.val (RingHom.mem_ker.mp hH)
      simpa [g] using this
    obtain ⟨N, R, hR, hR'⟩ :=
      specialisation_clear_denominators a t θ Δ Q hQ t' θ' b hb H
    rw [h0, mul_zero] at hR
    obtain ⟨S, rfl⟩ := hP R hR
    rw [Polynomial.eval₂_mul, hP', zero_mul] at hR'
    have := (mul_eq_zero.mp hR'.symm).resolve_left (pow_ne_zero _ hΔ')
    exact this
  let e := Ideal.quotientKerAlgEquivOfSurjective hg
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker g) Ψ hker).comp e.symm.toAlgHom, ?_⟩
  intro j
  have he : e.symm ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ =
      Ideal.Quotient.mkₐ k (RingHom.ker g) (MvPolynomial.X j) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [e, g]
  rw [hb j]
  congr 1
  show b j = Ideal.Quotient.liftₐ (RingHom.ker g) Ψ hker (e.symm _)
  rw [he, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk]
  erw [Ideal.Quotient.lift_mk]
  simp [Ψ]

end GlobalTheory
