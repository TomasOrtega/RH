import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.SecondOrderNbhd

open TrivSqZeroExt

noncomputable def deform {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) : O →+* DualNumber R where
  toFun x := inl (f x) + inr (f (D x))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/- English proof (translation)
Simplify using `[deform]`.
-/
@[simp] lemma deform_fst {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).fst = f x := by
  simp [deform]

/- English proof (translation)
Simplify using `[deform]`.
-/
@[simp] lemma deform_snd {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).snd = f (D x) := by
  simp [deform]

/- English proof (translation)
Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_pow, pow_two, h]`. Simplify using the standard rewrite rules.
-/
lemma isNilpotent_span_of_sq {C : Type} [CommRing C] {e : C} (h : e * e = 0) :
    IsNilpotent (Ideal.span {e}) := by
  refine ⟨2, ?_⟩
  rw [Ideal.span_singleton_pow, pow_two, h]
  simp

/- English proof (translation)
Introduce `O _ _ D₁ D₂ h`. Set `i : O →+* DualNumber O` to `(inlHom O O)`. Set `j : DualNumber O →+* DualNumber (DualNumber O)` to `inlHom _ _`. Set `e₁ : DualNumber (DualNumber O)` to `inl DualNumber.eps`. Set `e₂ : DualNumber (DualNumber O)` to `DualNumber.eps`.

Establish `h1 : e₁ * e₁ = 0`. Simplify using `only [e₁]`. Rewrite using `[inl_mul_inl, DualNumber.eps_mul_eps]`. Simplify using the standard rewrite rules. Establish `h2 : e₂ * e₂ = 0` using `DualNumber.eps_mul_eps`.

Use `⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂}, j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i, deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)`. Conclude with `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Apply the tactic sequence `intro x; ext <;> simp [i, j, e₁]`.

Apply the tactic sequence `intro x; ext <;> simp [i, j, e₂]`. Apply the tactic sequence `intro x; ext <;> simp [i, j, e₂]`. Apply the tactic sequence `intro x; ext <;> simp [i, j, e₁, h]`. Introduce `x hx`. Use `congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx` as an intermediate fact.

Simplify `this` using `[i, j, e₁, e₂]`.
-/
theorem exists_second_order_nbhd : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  intro O _ _ D₁ D₂ h
  let i : O →+* DualNumber O := (inlHom O O)
  let j : DualNumber O →+* DualNumber (DualNumber O) := inlHom _ _
  let e₁ : DualNumber (DualNumber O) := inl DualNumber.eps
  let e₂ : DualNumber (DualNumber O) := DualNumber.eps
  have h1 : e₁ * e₁ = 0 := by
    simp only [e₁]; rw [inl_mul_inl, DualNumber.eps_mul_eps]; simp
  have h2 : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  refine ⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂},
    j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i,
    deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · intro x; ext <;> simp [i, j, e₁]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₁, h]
  · intro x hx
    have := congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx
    simpa [i, j, e₁, e₂] using this

end GlobalTheory.SecondOrderNbhd
