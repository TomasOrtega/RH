import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

namespace UpperTheory

open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `A _ _ _ 𝔞 N hN`. Establish `hN0 : (N : A) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Use `⟨fun hmem => ?_, fun a t h => ?_⟩` and prove the remaining obligations. Establish `hdvd : 𝔞 ∣ Ideal.span {(N : A)}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)`. Take `⟨𝔟, h𝔟⟩` from `hdvd`.

Establish `hle : Ideal.span {(N : A)} ≤ 𝔟`. Rewrite using `[h𝔟]`. Conclude with `Ideal.mul_le_right`. Establish `hne : Ideal.span {(N : A)} ≠ ⊥`. Simplify `hN0` using `[Ideal.span_singleton_eq_bot]`.

Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq hle hne`. Use `⟨a, ?_⟩` and prove the remaining obligations. Unfold `IsGen`. Rewrite using `[sup_comm, ha, mul_comm, ← h𝔟]`. Unfold `IsGen at h ⊢`.

Establish `hs : Ideal.span {(t : A) * a} ⊔ Ideal.span {((N * t : ℕ) : A)} = Ideal.span {(t : A)} * (Ideal.span {a} ⊔ Ideal.span {(N : A)})`. Rewrite using `[Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]`. Rewrite using `[hs, mul_assoc, h, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]`.
-/
theorem exists_generic_moduli_point : GenEx := by
  intro A _ _ _ 𝔞 N hN
  have hN0 : (N : A) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨fun hmem => ?_, fun a t h => ?_⟩
  · have hdvd : 𝔞 ∣ Ideal.span {(N : A)} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    obtain ⟨𝔟, h𝔟⟩ := hdvd
    have hle : Ideal.span {(N : A)} ≤ 𝔟 := by
      rw [h𝔟]; exact Ideal.mul_le_right
    have hne : Ideal.span {(N : A)} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hN0
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    refine ⟨a, ?_⟩
    unfold IsGen
    rw [sup_comm, ha, mul_comm, ← h𝔟]
  · unfold IsGen at h ⊢
    have hs : Ideal.span {(t : A) * a} ⊔ Ideal.span {((N * t : ℕ) : A)}
        = Ideal.span {(t : A)} * (Ideal.span {a} ⊔ Ideal.span {(N : A)}) := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]
    rw [hs, mul_assoc, h, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]

end UpperTheory
