import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferentStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTer

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Glob

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYdc5.main P t ht htP`.
-/
theorem exists_prime_mem_of_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (t : ℕ) (ht : t ≠ 0) (htP : (t : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ (p : R) ∈ P :=
  _root_.UpperTheory.Reformulated.B.DYdc5.main P t ht htP

/- English proof (translation)
Break down `Nat.eq_zero_or_pos i with rfl | hipos` into its components or cases. Simplify using the standard rewrite rules. Establish `hPD : P ∣ differentIdeal ℤ (𝓞 E)` using `(dvd_pow_self P hipos.ne').trans hi`. Establish `hP0 : P ≠ ⊥` using `hPp.ne_zero`. Use `haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp`.

Take `⟨p, hp, hpt, hpP⟩` from `exists_prime_mem_of_natCast_mem P t ht (h P hPprime hP0 hPD)`. Establish `hp0 : ((p : 𝓞 E)) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hS0 : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} ≠ 0`. Introduce `h0`. Use `Ideal.span_singleton_eq_bot.1 h0` as an intermediate fact.

Conclude with `pow_ne_zero _ hp0 this`. Take `⟨J, hJ, hnd⟩` from `(FiniteMultiplicity.of_not_isUnit hPp.not_unit hS0).exists_eq_pow_mul_and_not_dvd`. Establish `hnot` using `GlobalTheory.T.prime_power_not_dvd_different E P J p _ hp hpP hnd hJ`. Establish `hlt : i < multiplicity P (Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)})`. Assume the negation of the conclusion as `hle`.

Conclude with `hnot ((pow_dvd_pow P (not_lt.1 hle)).trans hi)`. Establish `h1 : P ^ i ∣ Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)}`. Conclude with `((pow_dvd_pow P hlt.le).mul_right J).trans (dvd_of_eq hJ.symm)`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]`.

Conclude with `pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hpt) _`.
-/
theorem prime_pow_dvd_span_of_dvd_differentIdeal (E : Type) [Field E] [NumberField E] (t : ℕ)
    (ht : t ≠ 0)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P)
    (P : Ideal (𝓞 E)) (hPp : Prime P) (i : ℕ) (hi : P ^ i ∣ differentIdeal ℤ (𝓞 E)) :
    P ^ i ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp
  have hPD : P ∣ differentIdeal ℤ (𝓞 E) := (dvd_pow_self P hipos.ne').trans hi
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp
  obtain ⟨p, hp, hpt, hpP⟩ := exists_prime_mem_of_natCast_mem P t ht (h P hPprime hP0 hPD)
  have hp0 : ((p : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hS0 : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} ≠ 0 := by
    intro h0
    have := Ideal.span_singleton_eq_bot.1 h0
    exact pow_ne_zero _ hp0 this
  obtain ⟨J, hJ, hnd⟩ :=
    (FiniteMultiplicity.of_not_isUnit hPp.not_unit hS0).exists_eq_pow_mul_and_not_dvd
  have hnot := GlobalTheory.T.prime_power_not_dvd_different E P J p _ hp hpP hnd hJ
  have hlt : i < multiplicity P (Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)}) := by
    by_contra hle
    exact hnot ((pow_dvd_pow P (not_lt.1 hle)).trans hi)
  have h1 : P ^ i ∣ Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    exact ((pow_dvd_pow P hlt.le).mul_right J).trans (dvd_of_eq hJ.symm)
  refine h1.trans ?_
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hpt) _

/- English proof (translation)
Introduce `E _ _ t ht h`. Establish `hD : differentIdeal ℤ (𝓞 E) ≠ 0` using `differentIdeal_ne_bot`. Establish `key : ∀ I : Ideal (𝓞 E), I ≠ 0 → I ∣ differentIdeal ℤ (𝓞 E) → I ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)}`. Introduce `I`. Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_coprime with`.

Consider the case `h0 => exact fun h0 => absurd rfl h0`. Consider the case `h1 hu => exact fun _ _ => hu.dvd`. Consider the case `hpr i hq`. Conclude with `fun _ hd => prime_pow_dvd_span_of_dvd_differentIdeal E t ht h _ hq i hd`. Consider the case `hcp hxy hx hy`.

Introduce `h0 hd`. Conclude with `hxy.mul_dvd (hx (left_ne_zero_of_mul h0) ((dvd_mul_right _ _).trans hd)) (hy (right_ne_zero_of_mul h0) ((dvd_mul_left _ _).trans hd))`. Conclude with `key _ hD dvd_rfl`.
-/
theorem differentIdeal_dvd_span_pow : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 →
    (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) →
    differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  intro E _ _ t ht h
  have hD : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  have key : ∀ I : Ideal (𝓞 E), I ≠ 0 → I ∣ differentIdeal ℤ (𝓞 E) →
      I ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_coprime with
    | h0 => exact fun h0 => absurd rfl h0
    | h1 hu => exact fun _ _ => hu.dvd
    | hpr i hq =>
      exact fun _ hd => prime_pow_dvd_span_of_dvd_differentIdeal E t ht h _ hq i hd
    | hcp hxy hx hy =>
      intro h0 hd
      exact hxy.mul_dvd (hx (left_ne_zero_of_mul h0) ((dvd_mul_right _ _).trans hd))
        (hy (right_ne_zero_of_mul h0) ((dvd_mul_left _ _).trans hd))
  exact key _ hD dvd_rfl

end GlobalTheory.CompanionTheory.Glob
