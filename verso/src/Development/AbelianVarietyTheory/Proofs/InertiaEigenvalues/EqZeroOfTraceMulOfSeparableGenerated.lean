import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TraceNondeg

/- English proof (translation)
Set `b` to `Module.finBasis F A`. Establish `hn : IsNilpotent (Algebra.leftMulMatrix b w)`. Apply `ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow` to reduce the goal to its premises. Introduce `k hk _`. Rewrite using `[← map_pow, ← Algebra.trace_eq_matrix_trace]`.

Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[pow_succ']`. Conclude with `h _`. Take `⟨m, hm⟩` from `hn`. Rewrite `hm` using `[← map_pow, ← map_zero (Algebra.leftMulMatrix b)]`.

Conclude with `⟨m, Algebra.leftMulMatrix_injective b hm⟩`.
-/
theorem isNilpotent_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (w : A) (h : ∀ y : A, Algebra.trace F A (w * y) = 0) : IsNilpotent w := by
  classical
  let b := Module.finBasis F A
  have hn : IsNilpotent (Algebra.leftMulMatrix b w) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ']
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact ⟨m, Algebra.leftMulMatrix_injective b hm⟩

/- English proof (translation)
Establish `h1 : minpoly K.E (Algebra.lmul K.E B.A B.g) = minpoly K.E B.g` using `minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g`. Rewrite using `[← h1]`. Conclude with `LinearMap.minpoly_dvd_charpoly _`.
-/
theorem minpoly_dvd_P {K : UQ} (B : InvAlg K) : minpoly K.E B.g ∣ B.P := by
  have h1 : minpoly K.E (Algebra.lmul K.E B.A B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  rw [← h1]
  exact LinearMap.minpoly_dvd_charpoly _

/- English proof (translation)
Introduce `K B hP hgen w hw`. Take `⟨m, hm⟩` from `isNilpotent_of_trace_mul w hw`. Take `⟨f, rfl⟩` from `hgen w`. Establish `hd : minpoly K.E B.g ∣ f ^ m` using `minpoly.dvd K.E B.g (by rw [map_pow]; exact hm)`. Establish `hsq : Squarefree (minpoly K.E B.g)` using `(hP.of_dvd (minpoly_dvd_P B)).squarefree`.

Break down `Nat.eq_zero_or_pos m with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Rewrite `hm` using `[pow_zero]`. Conclude with `(subsingleton_of_zero_eq_one hm.symm).elim _ _`. Establish `hf : minpoly K.E B.g ∣ f` using `(hsq.dvd_pow_iff_dvd h0.ne').mp hd`.

Take `⟨q, rfl⟩` from `hf`. Rewrite using `[map_mul, minpoly.aeval, zero_mul]`.
-/
theorem eq_zero_of_trace_mul_eq_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) →
    ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by
  intro K B hP hgen w hw
  obtain ⟨m, hm⟩ := isNilpotent_of_trace_mul w hw
  obtain ⟨f, rfl⟩ := hgen w
  have hd : minpoly K.E B.g ∣ f ^ m := minpoly.dvd K.E B.g (by rw [map_pow]; exact hm)
  have hsq : Squarefree (minpoly K.E B.g) := (hP.of_dvd (minpoly_dvd_P B)).squarefree
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    rw [pow_zero] at hm
    exact (subsingleton_of_zero_eq_one hm.symm).elim _ _
  have hf : minpoly K.E B.g ∣ f := (hsq.dvd_pow_iff_dvd h0.ne').mp hd
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma.TraceNondeg
