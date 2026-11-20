import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `monomial n a`. Simplify using `only [Polynomial.aeval_monomial, map_mul, map_pow, Algebra.algebraMap_self, RingHom.id_apply]`. Use `congr 1`.
-/
private theorem constantCoeff_aeval_eq_aeval_constantCoeff {S : Type} [CommRing S] (Q : Polynomial S) (y : PowerSeries S) :
    constantCoeff (Polynomial.aeval y Q) = Polynomial.aeval (constantCoeff y) Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1

/- English proof (translation)
Introduce `LL S _ _ _ _ m hm ζ E hζ hE0 hE`. Establish `hζm : ζ ^ m = 1`. Take `⟨q, hq⟩` from `Polynomial.cyclotomic.dvd_X_pow_sub_one m LL`. Establish `h` using `congrArg (Polynomial.aeval ζ) hq`. Simplify using `only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h`.

Conclude with `sub_eq_zero.1 h`. Establish `hζu : IsUnit ζ`. Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm.ne'`. Establish `hmul : ζ * ζ ^ k = 1` using `by rw [← pow_succ']; exact hζm`. Conclude with `⟨⟨ζ, ζ ^ k, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩`.

Use `set Φ := Polynomial.cyclotomic m LL with hΦ`. Establish `hsep : Φ.Separable` using `(Polynomial.X_pow_sub_one_separable_iff.2 (by exact_mod_cast hm.ne')).of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one m LL)`. Take `⟨a, b, hab⟩` from `hsep`. Establish `hu : IsUnit (Polynomial.aeval ζ (Polynomial.derivative Φ))`. Establish `h` using `congrArg (Polynomial.aeval ζ) hab`.

Simplify using `only [map_add, map_mul, map_one, hζ, mul_zero, zero_add] at h`. Conclude with `⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩`. Use `set y : PowerSeries S := C ζ * E with hy`. Establish `hy0 : constantCoeff y = ζ` using `by simp [hy, hE0]`. Establish `hyd : derivative S y = y`.

Simplify using `[hy, Derivation.leibniz, derivative_C, hE, smul_eq_mul]`. Establish `hF : Polynomial.aeval y Φ = Polynomial.aeval y (Φ.map (algebraMap LL S))` using `(Polynomial.aeval_map_algebraMap S y Φ).symm`. Establish `h0 : constantCoeff (Polynomial.aeval y Φ) = 0`. Rewrite using `[hF, constantCoeff_aeval_eq_aeval_constantCoeff, hy0, Polynomial.aeval_map_algebraMap, hζ]`. Establish `h1 : constantCoeff (derivative S (Polynomial.aeval y Φ)) = Polynomial.aeval ζ (Polynomial.derivative Φ) * ζ`.

Rewrite using `[hF, Derivation.map_aeval, hyd, smul_eq_mul, map_mul, constantCoeff_aeval_eq_aeval_constantCoeff, hy0, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]`. Take `⟨G, hG⟩` from `PowerSeries.X_dvd_iff.2 h0`. Establish `hGc : constantCoeff (derivative S (Polynomial.aeval y Φ)) = constantCoeff G`. Rewrite using `[hG]`. Simplify using `[Derivation.leibniz, derivative_X, smul_eq_mul]`.

Establish `hGu : IsUnit G`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, ← hGc, h1]`. Conclude with `hu.mul hζu`. Use `⟨hGu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, hG, mul_comm]`.
-/
theorem cycloSimple : CycloSimpleStatement := by
  intro LL S _ _ _ _ m hm ζ E hζ hE0 hE
  have hζm : ζ ^ m = 1 := by
    obtain ⟨q, hq⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m LL
    have h := congrArg (Polynomial.aeval ζ) hq
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.1 h
  have hζu : IsUnit ζ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hmul : ζ * ζ ^ k = 1 := by rw [← pow_succ']; exact hζm
    exact ⟨⟨ζ, ζ ^ k, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩
  set Φ := Polynomial.cyclotomic m LL with hΦ
  have hsep : Φ.Separable :=
    (Polynomial.X_pow_sub_one_separable_iff.2 (by exact_mod_cast hm.ne')).of_dvd
      (Polynomial.cyclotomic.dvd_X_pow_sub_one m LL)
  obtain ⟨a, b, hab⟩ := hsep
  have hu : IsUnit (Polynomial.aeval ζ (Polynomial.derivative Φ)) := by
    have h := congrArg (Polynomial.aeval ζ) hab
    simp only [map_add, map_mul, map_one, hζ, mul_zero, zero_add] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  set y : PowerSeries S := C ζ * E with hy
  have hy0 : constantCoeff y = ζ := by simp [hy, hE0]
  have hyd : derivative S y = y := by
    simp [hy, Derivation.leibniz, derivative_C, hE, smul_eq_mul]
  have hF : Polynomial.aeval y Φ = Polynomial.aeval y (Φ.map (algebraMap LL S)) :=
    (Polynomial.aeval_map_algebraMap S y Φ).symm
  have h0 : constantCoeff (Polynomial.aeval y Φ) = 0 := by
    rw [hF, constantCoeff_aeval_eq_aeval_constantCoeff, hy0, Polynomial.aeval_map_algebraMap, hζ]
  have h1 : constantCoeff (derivative S (Polynomial.aeval y Φ)) =
      Polynomial.aeval ζ (Polynomial.derivative Φ) * ζ := by
    rw [hF, Derivation.map_aeval, hyd, smul_eq_mul, map_mul, constantCoeff_aeval_eq_aeval_constantCoeff, hy0,
      Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
  obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.2 h0
  have hGc : constantCoeff (derivative S (Polynomial.aeval y Φ)) = constantCoeff G := by
    rw [hG]
    simp [Derivation.leibniz, derivative_X, smul_eq_mul]
  have hGu : IsUnit G := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← hGc, h1]
    exact hu.mul hζu
  refine ⟨hGu.unit, ?_⟩
  rw [IsUnit.unit_spec, hG, mul_comm]

end LevelStatements.Lv
