import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory

/- English proof (translation)
Establish `hpp : Prime p` using `hp.prime`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Take `⟨π, z, hπ⟩` from `hd p 2`. Establish `hπP : π ∈ P.asIdeal` using `(hP π).2 ⟨1 + p * z, by rw [hπ]; ring⟩`. Use `set Q : Ideal R := Ideal.comap f (Ideal.span {p ^ k}) with hQdef`.

Establish `hQ : ∀ y : R, y ∈ Q ↔ p ^ k ∣ f y` using `fun y => by`. Rewrite using `[hQdef, Ideal.mem_comap, Ideal.mem_span_singleton]`. Establish `hle : P.asIdeal ^ k ≤ Q`. Establish `h1 : P.asIdeal ≤ Ideal.comap f (Ideal.span {p})` using `fun y hy => by`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`.

Conclude with `(hP y).1 hy`. Combine the equalities or inequalities in the displayed calculation. Take `⟨j, hj, hassoc⟩` from `(dvd_prime_pow P.prime k).1 (Ideal.dvd_iff_le.2 hle)`. Establish `hQj : Q = P.asIdeal ^ j` using `associated_iff_eq.1 hassoc`. Establish `hjk : j = k`.

Assume the negation of the conclusion as `hne`. Establish `hjk' : j ≤ k - 1` using `by omega`. Establish `hmem : π ^ (k - 1) ∈ Q`. Rewrite using `[hQj]`. Conclude with `Ideal.pow_le_pow_right hjk' (Ideal.pow_mem_pow hπP _)`.

Rewrite `hmem` using `[hQ, map_pow, hπ]`. Establish `hfac : (p + p ^ 2 * z) ^ (k - 1) = p ^ (k - 1) * (1 + p * z) ^ (k - 1)`. Rewrite using `[← mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk' : p ^ k = p ^ (k - 1) * p`.

Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `hmem` using `[hfac, hk']`. Establish `hdiv` using `(mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hp0)).1 hmem`.

Establish `hdiv'` using `hpp.dvd_of_dvd_pow hdiv`. Establish `hone : p ∣ 1` using `(dvd_add_left (dvd_mul_right p z)).1 hdiv'`. Conclude with `hp.not_isUnit (isUnit_of_dvd_one hone)`. Rewrite using `[← hQ, hQj, hjk]`.
-/
theorem ordIdeal_of_ringHom {R W : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (P : HeightOneSpectrum R) (p : W) (hp : Irreducible p) (f : R →+* W)
    (hP : ∀ x : R, x ∈ P.asIdeal ↔ p ∣ f x)
    (hd : ∀ (y : W) (n : ℕ), ∃ (x : R) (z : W), f x = y + p ^ n * z)
    (x : R) (k : ℕ) : x ∈ P.asIdeal ^ k ↔ p ^ k ∣ f x := by

  have hpp : Prime p := hp.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨π, z, hπ⟩ := hd p 2
  have hπP : π ∈ P.asIdeal := (hP π).2 ⟨1 + p * z, by rw [hπ]; ring⟩
  set Q : Ideal R := Ideal.comap f (Ideal.span {p ^ k}) with hQdef
  have hQ : ∀ y : R, y ∈ Q ↔ p ^ k ∣ f y := fun y => by
    rw [hQdef, Ideal.mem_comap, Ideal.mem_span_singleton]
  have hle : P.asIdeal ^ k ≤ Q := by
    have h1 : P.asIdeal ≤ Ideal.comap f (Ideal.span {p}) := fun y hy => by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact (hP y).1 hy
    calc P.asIdeal ^ k ≤ (Ideal.comap f (Ideal.span {p})) ^ k := Ideal.pow_right_mono h1 k
      _ ≤ Ideal.comap f ((Ideal.span {p}) ^ k) := Ideal.le_comap_pow f k
      _ = Q := by rw [Ideal.span_singleton_pow]
  obtain ⟨j, hj, hassoc⟩ := (dvd_prime_pow P.prime k).1 (Ideal.dvd_iff_le.2 hle)
  have hQj : Q = P.asIdeal ^ j := associated_iff_eq.1 hassoc
  have hjk : j = k := by
    by_contra hne
    have hjk' : j ≤ k - 1 := by omega
    have hmem : π ^ (k - 1) ∈ Q := by
      rw [hQj]
      exact Ideal.pow_le_pow_right hjk' (Ideal.pow_mem_pow hπP _)
    rw [hQ, map_pow, hπ] at hmem
    have hfac : (p + p ^ 2 * z) ^ (k - 1) = p ^ (k - 1) * (1 + p * z) ^ (k - 1) := by
      rw [← mul_pow]; ring
    have hk' : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hfac, hk'] at hmem
    have hdiv := (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hp0)).1 hmem
    have hdiv' := hpp.dvd_of_dvd_pow hdiv
    have hone : p ∣ 1 := (dvd_add_left (dvd_mul_right p z)).1 hdiv'
    exact hp.not_isUnit (isUnit_of_dvd_one hone)
  rw [← hQ, hQj, hjk]

/- English proof (translation)
Introduce `hxy`. Establish `hinj : Function.Injective (algebraMap W Qq)` using `IsFractionRing.injective W Qq`. Use `choose F hF using h1`. Set `f : 𝓞 E →+* W` to `{ toFun := F map_one' := hinj (by rw [← (hF 1).1]; simp) map_mul' := fun a b => hinj (by`. Rewrite using `[map_mul, ← (hF (a * b)).1, ← (hF a).1, ← (hF b).1]`.

Use the proof step `simp)`. Use the proof step `map_zero' := hinj (by rw [← (hF 0).1]; simp)`. Use the proof step `map_add' := fun a b => hinj (by`. Rewrite using `[map_add, ← (hF (a + b)).1, ← (hF a).1, ← (hF b).1]`. Use the proof step `simp) }`.

Establish `hfx : ∀ a : 𝓞 E, algebraMap W Qq (f a) = ρ a` using `fun a => ((hF a).1).symm`. Establish `hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ (p : W) ∣ f a` using `fun a => (hF a).2`. Establish `hd : ∀ (b : W) (n : ℕ), ∃ (a : 𝓞 E) (c : W), f a = b + (p : W) ^ n * c`. Introduce `b n`. Take `⟨a, c, hac⟩` from `h2 b n`.

Conclude with `⟨a, c, hinj (by rw [hfx, hac])⟩`. Establish `hy : f x = y` using `hinj (by rw [hfx, hxy])`. Rewrite using `[ordIdeal_of_ringHom P (p : W) hp f hP hd x k, hy]`.
-/
theorem ordIdeal_of_embedding {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ) : ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by

  intro hxy
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  choose F hF using h1
  let f : 𝓞 E →+* W :=
    { toFun := F
      map_one' := hinj (by rw [← (hF 1).1]; simp)
      map_mul' := fun a b => hinj (by
        rw [map_mul, ← (hF (a * b)).1, ← (hF a).1, ← (hF b).1]; simp)
      map_zero' := hinj (by rw [← (hF 0).1]; simp)
      map_add' := fun a b => hinj (by
        rw [map_add, ← (hF (a + b)).1, ← (hF a).1, ← (hF b).1]; simp) }
  have hfx : ∀ a : 𝓞 E, algebraMap W Qq (f a) = ρ a := fun a => ((hF a).1).symm
  have hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ (p : W) ∣ f a := fun a => (hF a).2
  have hd : ∀ (b : W) (n : ℕ), ∃ (a : 𝓞 E) (c : W), f a = b + (p : W) ^ n * c := by
    intro b n
    obtain ⟨a, c, hac⟩ := h2 b n
    exact ⟨a, c, hinj (by rw [hfx, hac])⟩
  have hy : f x = y := hinj (by rw [hfx, hxy])
  rw [ordIdeal_of_ringHom P (p : W) hp f hP hd x k, hy]

end GlobalTheory
