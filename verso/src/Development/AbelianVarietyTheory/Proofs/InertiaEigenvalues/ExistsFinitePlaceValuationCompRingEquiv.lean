import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.PlaceTransport

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a` from `⟨_, WithZero.exp_log ha⟩`. Take `⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b` from `⟨_, WithZero.exp_log hb⟩`. Rewrite `ha1`, `hb1` using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Establish `key : ∀ n : ℕ, (m ≤ -(n : ℤ) ↔ k ≤ -(n : ℤ))` using `fun n => by`. Simplify `h n` using `only [WithZero.exp_le_exp]`.

Establish `hkm : k ≤ m`. Use `(key (-m).toNat).1 (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmk : m ≤ k`. Use `(key (-k).toNat).2 (by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[le_antisymm hmk hkm]`.
-/
theorem eq_of_forall_le_exp_neg {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  have key : ∀ n : ℕ, (m ≤ -(n : ℤ) ↔ k ≤ -(n : ℤ)) := fun n => by
    simpa only [WithZero.exp_le_exp] using h n
  have hkm : k ≤ m := by
    have := (key (-m).toNat).1 (by omega)
    omega
  have hmk : m ≤ k := by
    have := (key (-k).toNat).2 (by omega)
    omega
  rw [le_antisymm hmk hkm]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hfx : f x ≠ 0` using `by simpa using hx`. Use `eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx) (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x) (w.intValuation_le_one _) fun n => ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]`.

Express the relevant statement in the definitionally equal form `x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n`. Establish `hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R)` using `fun J => (Ideal.map_comap_of_equiv f.symm).symm`. Rewrite using `[hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]`. Both sides reduce to the same expression.
-/
theorem intValuation_comap_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hfx : f x ≠ 0 := by simpa using hx
  refine eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx)
    (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x)
    (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n
  have hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R) := fun J =>
    (Ideal.map_comap_of_equiv f.symm).symm
  rw [hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]
  rfl

/- English proof (translation)
Introduce `K L _ _ _ _ e la`. Use `set g : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e`. Use `⟨HeightOneSpectrum.comap (g : 𝓞 K →+* 𝓞 L) g.surjective la, fun y => ?_⟩` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) y`. Establish `hcast : ∀ c : 𝓞 K, e (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (g c)` using `fun _ => rfl`.

Rewrite using `[map_div₀, map_div₀, map_div₀, hcast, hcast, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap_equiv, intValuation_comap_equiv]`.
-/
theorem exists_place_valuation_comp_equiv :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
      (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K),
        ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  intro K L _ _ _ _ e la
  set g : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  refine ⟨HeightOneSpectrum.comap (g : 𝓞 K →+* 𝓞 L) g.surjective la, fun y => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hcast : ∀ c : 𝓞 K, e (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (g c) := fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hcast, hcast, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap_equiv, intValuation_comap_equiv]

end GlobalTheory.PlaceTransport
