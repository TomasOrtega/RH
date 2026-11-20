import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotSqMulUnit
open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

/- English proof (translation)
Introduce `E K _ _ _ _ _ p hp hd δ hδ w hpw hunr`. Establish `hmax` using `w.isMaximal`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E))`. Use `(not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_` and prove the remaining obligations.

Rewrite using `[Ideal.under, Ideal.mem_comap]`. Simplify using `using hpw`. Establish `h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1` using `Ideal.ramificationIdx_eq_one_iff.2 hunr`. Establish `h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1` using `Ideal.ramificationIdx_eq_one_iff.2 hv`. Establish `h3 : w.asIdeal.ramificationIdx ℤ = 1`.

Rewrite using `[Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]`. Establish `hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal` using `Ideal.ramificationIdx_eq_one_iff.1 h3`. Establish `hint : IsIntegral ℤ δ`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hδ]`.

Establish `: (-(p : K)) = algebraMap ℤ K (-(p : ℤ))` using `by simp`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Use `set y : 𝓞 K := ⟨δ, hint⟩ with hy`. Establish `hy2 : y ^ 2 = (p : 𝓞 K) * (-1)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))`. Rewrite using `[map_pow, map_mul, map_neg, map_one, map_natCast]`. Express the relevant statement in the definitionally equal form `δ ^ 2 = _`. Rewrite using `[hδ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu : (-1 : 𝓞 K) ∉ w.asIdeal`. Introduce `h`. Conclude with `hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))`. Conclude with `GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2`.
-/
theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
