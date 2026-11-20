import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMultiplicativeLiftCharZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk`. Use `haveI : CharZero (Wq l bk.a) := GlobalTheory.charZero_wittVector_of_field l (Fq l bk.a)`. Establish `hirr : Irreducible (l : Wq l bk.a)` using `WittVector.irreducible l (k := Fq l bk.a)`. Establish `hprime : Prime (l : Wq l bk.a)` using `hirr.prime`. Establish `hP : (Ideal.span {(l : Wq l bk.a)}).IsPrime` using `(Ideal.span_singleton_prime hprime.ne_zero).2 hprime`.

Establish `hE : bk.Ep.IsEisensteinAt (Ideal.span {(l : Wq l bk.a)})`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[bk.monic.leadingCoeff, Ideal.mem_span_singleton]`. Conclude with `fun h => hirr.not_isUnit (isUnit_of_dvd_one h)`. Introduce `n hn`.

Conclude with `Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)`. Take `⟨w, hw⟩` from `bk.coeff_zero`. Rewrite using `[hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]`. Introduce `h`. Establish `h2 : (l : Wq l bk.a) ∣ (w : Wq l bk.a)` using `(mul_dvd_mul_iff_left hprime.ne_zero).1 h`.

Conclude with `hirr.not_isUnit (isUnit_of_dvd_unit h2 w.isUnit)`. Establish `hirrE : Irreducible bk.Ep` using `hE.irreducible hP bk.monic.isPrimitive bk.deg_pos`. Set `F` to `FractionRing (Wq l bk.a)`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (Wq l bk.a) F)`. Establish `hirrF : Irreducible (bk.Ep.map (algebraMap (Wq l bk.a) F))` using `(bk.monic.irreducible_iff_irreducible_map_fraction_map).1 hirrE`.

Take `⟨a, b, hab⟩` from `hirrF.separable`. Rewrite `hab` using `[Polynomial.derivative_map]`. Take `⟨⟨d₁, hd₁⟩, hA⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Wq l bk.a)) a`. Take `⟨⟨d₂, hd₂⟩, hB⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Wq l bk.a)) b`. Use `set A := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) a`.

Use `set B := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) b`. Establish `hd : d₁ * d₂ ≠ 0` using `mul_ne_zero (nonZeroDivisors.ne_zero hd₁) (nonZeroDivisors.ne_zero hd₂)`. Establish `key : Polynomial.C d₂ * A * bk.Ep + Polynomial.C d₁ * B * Polynomial.derivative bk.Ep = Polynomial.C (d₁ * d₂)`. Apply `Polynomial.map_injective (algebraMap (Wq l bk.a) F) (IsFractionRing.injective (Wq l bk.a) F)` to reduce the goal to its premises. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA, hB, Polynomial.derivative_map]`.

Simplify using `only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.C_mul]`. Take the linear combination `(Polynomial.C (algebraMap (Wq l bk.a) F d₁) * Polynomial.C (algebraMap (Wq l bk.a) F d₂)) * hab`. Take `⟨m, u, hu⟩` from `WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l bk.a) (d₁ * d₂) hd`. Use `⟨m, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₂) * A, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₁) * B, ?_⟩` and prove the remaining obligations. Establish `: Polynomial.C ((l : Wq l bk.a) ^ m) = Polynomial.C (↑u⁻¹ : Wq l bk.a) * Polynomial.C (d₁ * d₂)`.

Rewrite using `[hu, ← Polynomial.C_mul]`. Use `congr 1`. Rewrite using `[mul_comm, mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[this, ← key]`. Simplify using `only [Polynomial.C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bezout_Ep_derivative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)),
    a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  intro l _ K bk
  haveI : CharZero (Wq l bk.a) := GlobalTheory.charZero_wittVector_of_field l (Fq l bk.a)
  have hirr : Irreducible (l : Wq l bk.a) := WittVector.irreducible l (k := Fq l bk.a)
  have hprime : Prime (l : Wq l bk.a) := hirr.prime
  have hP : (Ideal.span {(l : Wq l bk.a)}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).2 hprime
  have hE : bk.Ep.IsEisensteinAt (Ideal.span {(l : Wq l bk.a)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [bk.monic.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hirr.not_isUnit (isUnit_of_dvd_one h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · obtain ⟨w, hw⟩ := bk.coeff_zero
      rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
      intro h
      have h2 : (l : Wq l bk.a) ∣ (w : Wq l bk.a) := (mul_dvd_mul_iff_left hprime.ne_zero).1 h
      exact hirr.not_isUnit (isUnit_of_dvd_unit h2 w.isUnit)
  have hirrE : Irreducible bk.Ep := hE.irreducible hP bk.monic.isPrimitive bk.deg_pos
  let F := FractionRing (Wq l bk.a)
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (Wq l bk.a) F)
  have hirrF : Irreducible (bk.Ep.map (algebraMap (Wq l bk.a) F)) :=
    (bk.monic.irreducible_iff_irreducible_map_fraction_map).1 hirrE
  obtain ⟨a, b, hab⟩ := hirrF.separable
  rw [Polynomial.derivative_map] at hab
  obtain ⟨⟨d₁, hd₁⟩, hA⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Wq l bk.a)) a
  obtain ⟨⟨d₂, hd₂⟩, hB⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Wq l bk.a)) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) b
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd₁) (nonZeroDivisors.ne_zero hd₂)
  have key : Polynomial.C d₂ * A * bk.Ep + Polynomial.C d₁ * B * Polynomial.derivative bk.Ep =
      Polynomial.C (d₁ * d₂) := by
    apply Polynomial.map_injective (algebraMap (Wq l bk.a) F) (IsFractionRing.injective (Wq l bk.a) F)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA, hB, Polynomial.derivative_map]
    simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.C_mul]
    linear_combination (Polynomial.C (algebraMap (Wq l bk.a) F d₁) * Polynomial.C (algebraMap (Wq l bk.a) F d₂)) * hab
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l bk.a) (d₁ * d₂) hd
  refine ⟨m, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₂) * A, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₁) * B, ?_⟩
  have : Polynomial.C ((l : Wq l bk.a) ^ m) = Polynomial.C (↑u⁻¹ : Wq l bk.a) * Polynomial.C (d₁ * d₂) := by
    rw [hu, ← Polynomial.C_mul]
    congr 1
    rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]
  rw [this, ← key]
  simp only [Polynomial.C_mul]
  ring

end GlobalTheory.BSP
