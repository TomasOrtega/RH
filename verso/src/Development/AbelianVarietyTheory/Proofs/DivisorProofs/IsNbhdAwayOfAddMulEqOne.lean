import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
open GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.AffineCurveNbhd

/- English proof (translation)
Use `set F := algebraMap B A' f with hF`. Establish `hpow : ∀ m : ℕ, F ∣ h ^ m - 1`. Introduce `m`. Establish `h1 : F ∣ h - 1` using `⟨-c, by linear_combination hh⟩`. Use `sub_dvd_pow_sub_pow h 1 m` as an intermediate fact.

Rewrite `this` using `[one_pow]`. Conclude with `h1.trans this`. Establish `hL : ∀ b : B, algebraMap B (Localization.Away h) b = algebraMap A' (Localization.Away h) (algebraMap B A' b)` using `fun b => IsScalarTower.algebraMap_apply B A' (Localization.Away h) b`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a'`.

Take `⟨⟨x, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers h) a'`. Take `⟨n, hn⟩` from `(Submonoid.mem_powers_iff _ _).mp s.2`. Simplify using `only at hs`. Rewrite `hs` using `[← hn]`. Take `⟨b, hb⟩` from `hN.1 x`.

Rewrite `hb` using `[Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `hb`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton, hL b, hL f]`. Take `⟨u, hu⟩` from `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h |>.exists_right_inv`.

Establish `hu1 : algebraMap A' (Localization.Away h) F ∣ u - 1`. Use `⟨algebraMap A' (Localization.Away h) c * u, ?_⟩` and prove the remaining obligations. Use `congrArg (algebraMap A' (Localization.Away h)) hh` as an intermediate fact. Simplify using `only [map_add, map_mul, map_one] at this`. Take the linear combination `hu - u * this`.

Establish `hun : algebraMap A' (Localization.Away h) F ∣ u ^ n - 1`. Use `sub_dvd_pow_sub_pow u 1 n` as an intermediate fact. Rewrite `this` using `[one_pow]`. Conclude with `hu1.trans this`. Take `⟨e, he⟩` from `hun`.

Establish `ha' : a' = algebraMap A' (Localization.Away h) x * u ^ n`. Establish `: a' * (algebraMap A' (Localization.Away h) h * u) ^ n = a'` using `by rw [hu, one_pow, mul_one]`. Rewrite using `[← this, mul_pow, ← mul_assoc, ← map_pow, hs]`. Use `⟨algebraMap A' (Localization.Away h) x * e + algebraMap A' (Localization.Away h) d, ?_⟩` and prove the remaining obligations. Establish `hx : algebraMap A' (Localization.Away h) x = algebraMap A' (Localization.Away h) (algebraMap B A' b) + algebraMap A' (Localization.Away h) F * algebraMap A' (Localization.Away h) d`.

Rewrite using `[← map_mul, ← map_add, ← hd]`. Put the polynomial expressions in normal form. Rewrite using `[ha']`. Take the linear combination `(algebraMap A' (Localization.Away h) x) * he + hx`. Introduce `a ha`.

Rewrite `ha` using `[Ideal.mem_span_singleton, hL a, hL f]`. Take `⟨y, hy⟩` from `ha`. Take `⟨⟨x, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers h) y`. Take `⟨n, hn⟩` from `(Submonoid.mem_powers_iff _ _).mp s.2`. Simplify using `only at hs`.

Establish `heq : algebraMap A' (Localization.Away h) (algebraMap B A' a * h ^ n) = algebraMap A' (Localization.Away h) (F * x)`. Rewrite using `[map_mul, map_mul, hy, ← hs, hn]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨⟨k, hk⟩, hk'⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp heq`. Take `⟨m, rfl⟩` from `(Submonoid.mem_powers_iff _ _).mp hk`.

Simplify using `only at hk'`. Apply `hN.2` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`. Take `⟨g, hg⟩` from `hpow (m + n)`. Use `⟨h ^ m * x - g * algebraMap B A' a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hF]`. Take the linear combination `hk' - algebraMap B A' a * hg`.
-/
theorem isNbhd_away_of_add_mul_eq_one (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A')
    (hN : IsNbhd B A' f) (hh : h + algebraMap B A' f * c = 1) : IsNbhd B (Localization.Away h) f := by
  set F := algebraMap B A' f with hF
  have hpow : ∀ m : ℕ, F ∣ h ^ m - 1 := by
    intro m
    have h1 : F ∣ h - 1 := ⟨-c, by linear_combination hh⟩
    have := sub_dvd_pow_sub_pow h 1 m
    rw [one_pow] at this
    exact h1.trans this
  have hL : ∀ b : B, algebraMap B (Localization.Away h) b =
      algebraMap A' (Localization.Away h) (algebraMap B A' b) := fun b =>
    IsScalarTower.algebraMap_apply B A' (Localization.Away h) b
  refine ⟨?_, ?_⟩
  · intro a'
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    rw [← hn] at hs
    obtain ⟨b, hb⟩ := hN.1 x
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨d, hd⟩ := hb
    refine ⟨b, ?_⟩
    rw [Ideal.mem_span_singleton, hL b, hL f]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h |>.exists_right_inv
    have hu1 : algebraMap A' (Localization.Away h) F ∣ u - 1 := by
      refine ⟨algebraMap A' (Localization.Away h) c * u, ?_⟩
      have := congrArg (algebraMap A' (Localization.Away h)) hh
      simp only [map_add, map_mul, map_one] at this
      linear_combination hu - u * this
    have hun : algebraMap A' (Localization.Away h) F ∣ u ^ n - 1 := by
      have := sub_dvd_pow_sub_pow u 1 n
      rw [one_pow] at this
      exact hu1.trans this
    obtain ⟨e, he⟩ := hun
    have ha' : a' = algebraMap A' (Localization.Away h) x * u ^ n := by
      have : a' * (algebraMap A' (Localization.Away h) h * u) ^ n = a' := by rw [hu, one_pow, mul_one]
      rw [← this, mul_pow, ← mul_assoc, ← map_pow, hs]
    refine ⟨algebraMap A' (Localization.Away h) x * e + algebraMap A' (Localization.Away h) d, ?_⟩
    have hx : algebraMap A' (Localization.Away h) x =
        algebraMap A' (Localization.Away h) (algebraMap B A' b) + algebraMap A' (Localization.Away h) F *
          algebraMap A' (Localization.Away h) d := by
      rw [← map_mul, ← map_add, ← hd]; ring_nf
    rw [ha']
    linear_combination (algebraMap A' (Localization.Away h) x) * he + hx
  · intro a ha
    rw [Ideal.mem_span_singleton, hL a, hL f] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    have heq : algebraMap A' (Localization.Away h) (algebraMap B A' a * h ^ n) =
        algebraMap A' (Localization.Away h) (F * x) := by
      rw [map_mul, map_mul, hy, ← hs, hn]; ring
    obtain ⟨⟨k, hk⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp heq
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hk
    simp only at hk'
    apply hN.2
    rw [Ideal.mem_span_singleton]
    obtain ⟨g, hg⟩ := hpow (m + n)
    refine ⟨h ^ m * x - g * algebraMap B A' a, ?_⟩
    rw [← hF]
    linear_combination hk' - algebraMap B A' a * hg

end GlobalTheory.AffineCurveNbhd
