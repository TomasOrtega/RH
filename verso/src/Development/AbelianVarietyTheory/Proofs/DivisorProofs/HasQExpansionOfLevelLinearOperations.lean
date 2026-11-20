import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

/- English proof (translation)
Introduce `τ`. Simplify `(hf τ).add (hg τ)` using `only [add_mul]`.
-/
theorem HasQ.add {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ + g τ) (fun n => a n + b n) := by
  intro τ
  simpa only [add_mul] using (hf τ).add (hg τ)

/- English proof (translation)
Introduce `τ`. Simplify `(hf τ).sub (hg τ)` using `only [sub_mul]`.
-/
theorem HasQ.sub {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ - g τ) (fun n => a n - b n) := by
  intro τ
  simpa only [sub_mul] using (hf τ).sub (hg τ)

/- English proof (translation)
Introduce `τ`. Simplify `(hf τ).mul_left c` using `only [mul_assoc]`.
-/
theorem HasQ.const_mul {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (c : ℂ) (hf : HasQ N f a) :
    HasQ N (fun τ => c * f τ) (fun n => c * a n) := by
  intro τ
  simpa only [mul_assoc] using (hf τ).mul_left c

/- English proof (translation)
Introduce `τ`. Establish `h` using `hasSum_single (f := fun n : ℕ => (if n = 0 then c else 0) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) 0 (fun m hm => by simp [hm])`. Simplify using `using h`.
-/
theorem HasQ.const (N : ℕ) (c : ℂ) :
    HasQ N (fun _ => c) (fun n => if n = 0 then c else 0) := by
  intro τ
  have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) 0
    (fun m hm => by simp [hm])
  simpa using h

/- English proof (translation)
Introduce `τ`. Simplify `hasSum_sum fun k hk => h k hk τ` using `only [Finset.sum_mul]`.
-/
theorem HasQ.sum {N : ℕ} {κ : Type*} (s : Finset κ) {f : κ → ℍ → ℂ} {a : κ → ℕ → ℂ}
    (h : ∀ k ∈ s, HasQ N (f k) (a k)) :
    HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n) := by
  intro τ
  simpa only [Finset.sum_mul] using hasSum_sum fun k hk => h k hk τ

/- English proof (translation)
Introduce `N`. Conclude with `⟨fun f g a b hf hg => hf.add hg, fun f g a b hf hg => hf.sub hg, fun c f a hf => hf.const_mul c, fun c => HasQ.const N c, fun κ s f a h => HasQ.sum s h⟩`.
-/
theorem hasQ_linear : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  intro N
  exact ⟨fun f g a b hf hg => hf.add hg, fun f g a b hf hg => hf.sub hg,
    fun c f a hf => hf.const_mul c, fun c => HasQ.const N c, fun κ s f a h => HasQ.sum s h⟩

end GlobalTheory.QFam
