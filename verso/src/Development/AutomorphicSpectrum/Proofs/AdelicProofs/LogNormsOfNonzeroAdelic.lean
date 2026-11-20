import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl.LogNorms

/- English proof (translation)
The claim follows from `HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) ι a`.
-/
theorem norm_integer_le_one (p : ℕ) [Fact p.Prime] {k : Type} [Field k] (ι : k →+* ℂ_[p])
    (a : 𝓞 k) : ‖ι (a : k)‖ ≤ 1 :=
  HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) ι a

/- English proof (translation)
Establish `h1 : ‖(z : ℚ_[p])‖ = 1` using `Padic.norm_intCast_eq_one_iff.2 ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp.out)).2 h).symm`. Rewrite using `[← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z, norm_algebraMap', h1]`.
-/
theorem norm_intCast_eq_one (p : ℕ) [hp : Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) :
    ‖(z : ℂ_[p])‖ = 1 := by
  have h1 : ‖(z : ℚ_[p])‖ = 1 := Padic.norm_intCast_eq_one_iff.2
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp.out)).2 h).symm
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z, norm_algebraMap', h1]

/- English proof (translation)
Take `⟨d, hd, h⟩` from `exists_integral_multiples ℤ ℚ (L := k) {x}`. Conclude with `⟨d, hd, ⟨d • x, h x (Finset.mem_singleton_self x)⟩, zsmul_eq_mul x d⟩`.
-/
theorem exists_int_mul_eq_integer {k : Type} [Field k] [NumberField k] (x : k) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : 𝓞 k, (a : k) = n * x := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ (L := k) {x}
  exact ⟨d, hd, ⟨d • x, h x (Finset.mem_singleton_self x)⟩, zsmul_eq_mul x d⟩

/- English proof (translation)
Establish `h` using `norm_integer_le_one p ι a`. Rewrite `h` using `[ha, map_mul, map_intCast, norm_mul, norm_intCast_eq_one p hp, one_mul]`. Then use the resulting hypothesis.
-/
theorem norm_le_one_of_mul {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ι : k →+* ℂ_[p])
    {x : k} {n : ℤ} {a : 𝓞 k} (ha : (a : k) = n * x) (hp : ¬ (p : ℤ) ∣ n) : ‖ι x‖ ≤ 1 := by
  have h := norm_integer_le_one p ι a
  rwa [ha, map_mul, map_intCast, norm_mul, norm_intCast_eq_one p hp, one_mul] at h

/- English proof (translation)
Take `⟨n, hn, a, ha⟩` from `exists_int_mul_eq_integer x`. Take `⟨m, hm, b, hb⟩` from `exists_int_mul_eq_integer x⁻¹`. Establish `hfin : {p : Nat.Primes | (p : ℕ) ∣ (n * m).natAbs}.Finite`. Use `Set.Finite.of_injOn (f := fun p : Nat.Primes => (p : ℕ)) (t := ((n * m).natAbs.primeFactors : Set ℕ)) ?_ (fun _ _ _ _ h => Subtype.ext h) (Finset.finite_toSet _)` and prove the remaining obligations. Introduce `p hp`.

Conclude with `Finset.mem_coe.2 (Nat.mem_primeFactors.2 ⟨p.2, hp, Int.natAbs_ne_zero.2 (mul_ne_zero hn hm)⟩)`. Use `hfin.subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨ι, hι⟩`. Assume the negation of the conclusion as `hp`. Establish `hnm : ¬ ((p : ℕ) : ℤ) ∣ n * m` using `fun h => hp (Int.natCast_dvd.1 h)`.

Establish `hpn : ¬ ((p : ℕ) : ℤ) ∣ n` using `fun h => hnm (h.mul_right m)`. Establish `hpm : ¬ ((p : ℕ) : ℤ) ∣ m` using `fun h => hnm (h.mul_left n)`. Establish `h1 : ‖ι x‖ ≤ 1` using `norm_le_one_of_mul p ι ha hpn`. Establish `h2 : ‖ι x⁻¹‖ ≤ 1` using `norm_le_one_of_mul p ι hb hpm`. Establish `h0 : 0 < ‖ι x‖` using `norm_pos_iff.2 ((map_ne_zero ι).2 hx)`.

Rewrite `h2` using `[map_inv₀, norm_inv]`. Establish `h3 : ‖ι x‖ = 1` using `le_antisymm h1 ((inv_le_one₀ h0).1 h2)`. Apply `hι` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Real.log ‖ι x‖ = 0`. Rewrite using `[h3, Real.log_one]`.
-/
theorem isAdelic_ofElt (k : Type) [Field k] [NumberField k] (x : k) (hx : x ≠ 0) :
    (LogNorms.ofElt x).IsAdelic := by
  obtain ⟨n, hn, a, ha⟩ := exists_int_mul_eq_integer x
  obtain ⟨m, hm, b, hb⟩ := exists_int_mul_eq_integer x⁻¹
  have hfin : {p : Nat.Primes | (p : ℕ) ∣ (n * m).natAbs}.Finite := by
    refine Set.Finite.of_injOn (f := fun p : Nat.Primes => (p : ℕ))
      (t := ((n * m).natAbs.primeFactors : Set ℕ)) ?_ (fun _ _ _ _ h => Subtype.ext h)
      (Finset.finite_toSet _)
    intro p hp
    exact Finset.mem_coe.2 (Nat.mem_primeFactors.2
      ⟨p.2, hp, Int.natAbs_ne_zero.2 (mul_ne_zero hn hm)⟩)
  refine hfin.subset ?_
  rintro p ⟨ι, hι⟩
  by_contra hp
  have hnm : ¬ ((p : ℕ) : ℤ) ∣ n * m := fun h => hp (Int.natCast_dvd.1 h)
  have hpn : ¬ ((p : ℕ) : ℤ) ∣ n := fun h => hnm (h.mul_right m)
  have hpm : ¬ ((p : ℕ) : ℤ) ∣ m := fun h => hnm (h.mul_left n)
  have h1 : ‖ι x‖ ≤ 1 := norm_le_one_of_mul p ι ha hpn
  have h2 : ‖ι x⁻¹‖ ≤ 1 := norm_le_one_of_mul p ι hb hpm
  have h0 : 0 < ‖ι x‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hx)
  rw [map_inv₀, norm_inv] at h2
  have h3 : ‖ι x‖ = 1 := le_antisymm h1 ((inv_le_one₀ h0).1 h2)
  apply hι
  change Real.log ‖ι x‖ = 0
  rw [h3, Real.log_one]

end GlobalTheory.CompanionTheory.Ar.Fl.LogNorms
