import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

/- English proof (translation)
Introduce `E _ _ p hp n A hA`. Set `S : Set (HeightOneSpectrum (𝓞 E))` to `{Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}`. Establish `hS : S.Finite`. Establish `hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E}`. Introduce and unpack `Q ⟨i, j, h⟩`.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Conclude with `⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩`. Use `Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub` and prove the remaining obligations. Conclude with `Filter.eventually_cofinite.mp (A i j).2`. Use `bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)` and prove the remaining obligations.

Establish `hpQ : (p : 𝓞 E) ∉ Q.asIdeal`. Take `⟨i', j', h⟩` from `hQ`. Conclude with `fun hm => h (hA Q hm i' j')`. Conclude with `exists_coprime_natCast_mul_v_le_one p hp Q hpQ _`. Assume the negation of the conclusion as `h`.

Conclude with `hQ ⟨i, j, h⟩`.
-/
theorem bnd_of_integral_over_prime : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  intro E _ _ p hp n A hA
  let S : Set (HeightOneSpectrum (𝓞 E)) := {Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}
  have hS : S.Finite := by
    have hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E} := by
      rintro Q ⟨i, j, h⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
    exact Filter.eventually_cofinite.mp (A i j).2
  refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
  · have hpQ : (p : 𝓞 E) ∉ Q.asIdeal := by
      obtain ⟨i', j', h⟩ := hQ
      exact fun hm => h (hA Q hm i' j')
    exact exists_coprime_natCast_mul_v_le_one p hp Q hpQ _
  · by_contra h
    exact hQ ⟨i, j, h⟩

end GlobalTheory.StdAtPrime
