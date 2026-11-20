import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdIdem

/- English proof (translation)
Establish `h2 : (1 + 1 : K) = (1 + s) + (1 - s)` using `by ring`. Establish `h` using `w.map_add (1 + s) (1 - s)`. Rewrite `h` using `[← h2]`. Break down `le_total (w (1 - s)) (w (1 + s)) with hle | hle` into its components or cases. Use `⟨1, Or.inr rfl, ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[max_eq_left hle]`. Simplify using `using h`. Use `⟨0, Or.inl rfl, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[max_eq_right hle]`. Simplify using `using h`.
-/
theorem local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (s : K) :
    ∃ e : K, (e = 0 ∨ e = 1) ∧ w (1 + 1) ≤ w (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : (1 + 1 : K) = (1 + s) + (1 - s) := by ring
  have h := w.map_add (1 + s) (1 - s)
  rw [← h2] at h
  rcases le_total (w (1 - s)) (w (1 + s)) with hle | hle
  · refine ⟨1, Or.inr rfl, ?_⟩
    rw [max_eq_left hle] at h
    simpa using h
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [max_eq_right hle] at h
    simpa using h

/- English proof (translation)
Distinguish the cases in `h : 1 + s = 0`. Use `⟨0, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h'`. Apply `h2` to reduce the goal to its premises.

Take the linear combination `h + h'`. Conclude with `⟨1, by simp, by simpa [isUnit_iff_ne_zero] using h⟩`.
-/
theorem local_field {K : Type*} [Field K] (h2 : (1 + 1 : K) ≠ 0) (s : K) :
    ∃ e : K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  by_cases h : 1 + s = 0
  · refine ⟨0, by simp, ?_⟩
    rw [isUnit_iff_ne_zero]
    intro h'
    apply h2
    linear_combination h + h'
  · exact ⟨1, by simp, by simpa [isUnit_iff_ne_zero] using h⟩

/- English proof (translation)
Establish `hu : IsUnit (1 + 1 : FiniteAdeleRing R K)`. Establish `: IsUnit (1 + 1 : K)`. Rewrite using `[isUnit_iff_ne_zero]`. Evaluate the numerical expressions. Simplify using `using this.map (algebraMap K (FiniteAdeleRing R K))`.

Rewrite `hu` using `[FiniteAdeleRing.isUnit_iff]`. Use `choose e he hv using fun v : HeightOneSpectrum R => local_val (Valued.v : Valuation (v.adicCompletion K) _) (s v)`. Establish `hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K`. Introduce `v`. Apply the tactic sequence `rcases he v with h | h <;> rw [h]`.

Conclude with `zero_mem _`. Conclude with `one_mem _`. Set `E : FiniteAdeleRing R K` to `⟨e, Filter.Eventually.of_forall hint⟩`. Use `⟨E, ?_, ?_⟩` and prove the remaining obligations. Use `FiniteAdeleRing.ext K fun v => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e v * e v = e v`. Apply the tactic sequence `rcases he v with h | h <;> simp [h]`. Establish `hval : ∀ v : HeightOneSpectrum R, Valued.v ((1 + 1 : FiniteAdeleRing R K) v) ≤ Valued.v ((E * (1 + s) + (1 - E) * (1 - s)) v)` using `fun v => hv v`. Rewrite using `[FiniteAdeleRing.isUnit_iff]`. Use `⟨fun v h0 => ?_, ?_⟩` and prove the remaining obligations.

Use `hval v` as an intermediate fact. Rewrite `this` using `[h0, map_zero, le_zero_iff, map_eq_zero]`. Conclude with `hu.1 v this`. Use `filter_upwards [hu.2, (E * (1 + s) + (1 - E) * (1 - s)).2] with v h1 h2`. Conclude with `le_antisymm h2 (h1 ▸ hval v)`.
-/
theorem finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (s : FiniteAdeleRing R K) :
    ∃ e : FiniteAdeleRing R K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have hu : IsUnit (1 + 1 : FiniteAdeleRing R K) := by
    have : IsUnit (1 + 1 : K) := by
      rw [isUnit_iff_ne_zero]; norm_num
    simpa using this.map (algebraMap K (FiniteAdeleRing R K))
  rw [FiniteAdeleRing.isUnit_iff] at hu
  choose e he hv using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (s v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_, ?_⟩
  · refine FiniteAdeleRing.ext K fun v => ?_
    change e v * e v = e v
    rcases he v with h | h <;> simp [h]
  · have hval : ∀ v : HeightOneSpectrum R, Valued.v ((1 + 1 : FiniteAdeleRing R K) v) ≤
        Valued.v ((E * (1 + s) + (1 - E) * (1 - s)) v) := fun v => hv v
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun v h0 => ?_, ?_⟩
    · have := hval v
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact hu.1 v this
    · filter_upwards [hu.2, (E * (1 + s) + (1 - E) * (1 - s)).2] with v h1 h2
      exact le_antisymm h2 (h1 ▸ hval v)

/- English proof (translation)
Establish `h2 : ∀ v : InfinitePlace K, (1 + 1 : v.Completion) ≠ 0`. Introduce `v h`. Establish `: algebraMap K v.Completion (1 + 1) = 0` using `by rw [map_add, map_one]; exact h`. Rewrite `this` using `[map_eq_zero]`. Evaluate the numerical expressions using `at this`.

Use `choose e he hu using fun v : InfinitePlace K => local_field (h2 v) (s v)`. Conclude with `⟨e, funext he, Pi.isUnit_iff.2 hu⟩`.
-/
theorem infinite_part (K : Type*) [Field K] [CharZero K] (s : InfiniteAdeleRing K) :
    ∃ e : InfiniteAdeleRing K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : ∀ v : InfinitePlace K, (1 + 1 : v.Completion) ≠ 0 := by
    intro v h
    have : algebraMap K v.Completion (1 + 1) = 0 := by rw [map_add, map_one]; exact h
    rw [map_eq_zero] at this
    norm_num at this
  choose e he hu using fun v : InfinitePlace K => local_field (h2 v) (s v)
  exact ⟨e, funext he, Pi.isUnit_iff.2 hu⟩

/- English proof (translation)
Take `⟨e₁, h₁, u₁⟩` from `infinite_part F s.1`. Take `⟨e₂, h₂, u₂⟩` from `finite_part (𝓞 F) F s.2`. Conclude with `⟨(e₁, e₂), Prod.ext h₁ h₂, Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩`.
-/
theorem exists_idem_isUnit (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F) :
    ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  obtain ⟨e₁, h₁, u₁⟩ := infinite_part F s.1
  obtain ⟨e₂, h₂, u₂⟩ := finite_part (𝓞 F) F s.2
  exact ⟨(e₁, e₂), Prod.ext h₁ h₂, Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩

end GlobalTheory.AdIdem
