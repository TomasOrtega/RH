import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

open NumberField Module Matrix in
open scoped ENNReal in
/- English proof (translation)
Establish `hint : IsIntegral ℤ (starRingEnd K (a : K))` using `map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)`. Rewrite `hint` using `[starRingEnd_apply]`. Conclude with `⟨⟨star (a : K), (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩`.
-/
private lemma exists_integer_eq_star {K : Type} [Field K] [NumberField K] [StarRing K]
    (a : 𝓞 K) : ∃ b : 𝓞 K, (b : K) = star (a : K) := by
  have hint : IsIntegral ℤ (starRingEnd K (a : K)) :=
    map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)
  rw [starRingEnd_apply] at hint
  exact ⟨⟨star (a : K), (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩

open NumberField Module Matrix in
open scoped ENNReal in

/- English proof (translation)
Introduce `K _ _ _ h`. Unfold `_root_.Formalism.HermitianLatticesTheory.IsCMUnram at h`. Take `⟨-, -, hP⟩` from `h`. Set `S : Set (𝓞 K)` to `{x | ∃ θ τ : 𝓞 K, algebraMap (𝓞 K) K τ = star (algebraMap (𝓞 K) K θ) ∧ x = θ - τ}`. Set `I : Ideal (𝓞 K)` to `Ideal.span S`.

Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hPm, hle⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨θ, τ, hτ, hnot⟩` from `hP P hPm`. Conclude with `hnot (hle (Ideal.subset_span ⟨θ, τ, hτ, rfl⟩))`.

Establish `key : ∀ x ∈ I, ∃ t : 𝓞 K, (x : K) * star (x : K) = (t : K) + star (t : K)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨θ, τ, hτ, rfl⟩` from `hx`.

Express the relevant statement in the definitionally equal form `(τ : K) = star (θ : K) at hτ`. Establish `h2 : star (τ : K) = θ` using `by rw [hτ, star_star]`. Use `⟨θ * (τ - θ), ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[star_sub, star_mul', star_sub, h2, ← hτ]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`. Take `⟨u, hu⟩` from `hy`.

Take `⟨y', hy'⟩` from `exists_integer_eq_star y`. Use `⟨s + u + x * y', ?_⟩` and prove the remaining obligations. Use `push_cast`. Simplify using `only [star_add, star_mul', hy', star_star]`. Take the linear combination `hs + hu`.

Consider the case `smul c x _ hx`. Take `⟨s, hs⟩` from `hx`. Take `⟨c', hc'⟩` from `exists_integer_eq_star c`. Use `⟨c * c' * s, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`.

Use `push_cast`. Simplify using `only [star_mul', hc', star_star]`. Take the linear combination `((c : K) * star (c : K)) * hs`. Take `⟨t, ht⟩` from `key 1 (hI ▸ Submodule.mem_top)`. Conclude with `⟨t, by simpa using ht.symm⟩`.
-/
theorem _root_.GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  intro K _ _ _ h
  unfold _root_.Formalism.HermitianLatticesTheory.IsCMUnram at h
  obtain ⟨-, -, hP⟩ := h
  let S : Set (𝓞 K) := {x | ∃ θ τ : 𝓞 K,
    algebraMap (𝓞 K) K τ = star (algebraMap (𝓞 K) K θ) ∧ x = θ - τ}
  let I : Ideal (𝓞 K) := Ideal.span S
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨θ, τ, hτ, hnot⟩ := hP P hPm
    exact hnot (hle (Ideal.subset_span ⟨θ, τ, hτ, rfl⟩))
  have key : ∀ x ∈ I, ∃ t : 𝓞 K, (x : K) * star (x : K) = (t : K) + star (t : K) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨θ, τ, hτ, rfl⟩ := hx
      change (τ : K) = star (θ : K) at hτ
      have h2 : star (τ : K) = θ := by rw [hτ, star_star]
      refine ⟨θ * (τ - θ), ?_⟩
      push_cast
      rw [star_sub, star_mul', star_sub, h2, ← hτ]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      obtain ⟨y', hy'⟩ := exists_integer_eq_star y
      refine ⟨s + u + x * y', ?_⟩
      push_cast
      simp only [star_add, star_mul', hy', star_star]
      linear_combination hs + hu
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨c', hc'⟩ := exists_integer_eq_star c
      refine ⟨c * c' * s, ?_⟩
      rw [smul_eq_mul]
      push_cast
      simp only [star_mul', hc', star_star]
      linear_combination ((c : K) * star (c : K)) * hs
  obtain ⟨t, ht⟩ := key 1 (hI ▸ Submodule.mem_top)
  exact ⟨t, by simpa using ht.symm⟩

end GlobalTheory
