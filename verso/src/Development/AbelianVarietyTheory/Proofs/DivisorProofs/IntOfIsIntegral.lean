import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.QuadGenerator

/- English proof (translation)
Establish `h' : IsIntegral ℤ (algebraMap ℚ ℂ r)` using `h`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h')`.
-/
theorem int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h')

/- English proof (translation)
The claim follows from `isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)`.
-/
theorem isIntegral_int (n : ℤ) : IsIntegral ℤ (n : ℂ) := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)

/- English proof (translation)
Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]`. Simplify using the standard rewrite rules.
-/
theorem sq_root (d : ℕ) : (Complex.I * (Real.sqrt d : ℝ)) ^ 2 = -(d : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

/- English proof (translation)
Establish `hw2` using `sq_root d`. Use `set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw`. Establish `hwc : starRingEnd ℂ w = -w` using `by simp [hw]`. Establish `hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w)`. Use `hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)` as an intermediate fact.

Simplify `this` using `[hwc, sub_eq_add_neg]`. Take `⟨t, ht⟩` from `int_of_isIntegral (r := 2 * a) (by`. Use `(congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')` and prove the remaining obligations. Use `push_cast`. Use the proof step `ring)`.

Take `⟨n, hn⟩` from `int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by`. Use `(congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(b : ℂ) ^ 2 * hw2)`. Establish `hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ)`.

Use `push_cast`. Rewrite using `[hn, ht]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩` from `int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by`. Rewrite using `[← Rat.cast_pow, hm2, Rat.cast_intCast]`.

Conclude with `isIntegral_int _))`. Establish `hm3 : m ^ 2 = d * (4 * n - t ^ 2)`. Establish `: ((m ^ 2 : ℤ) : ℚ) = ((d * (4 * n - t ^ 2) : ℤ) : ℚ)`. Rewrite using `[← hm2, ← hm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Take `⟨k, hk⟩ : (d : ℤ) ∣ m` from `(Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, hm3⟩`. Establish `hd0 : (d : ℚ) ≠ 0` using `by exact_mod_cast hd.ne_zero`. Establish `hkb : (k : ℚ) = 2 * b`.

Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises. Rewrite using `[← hm, hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨t, k, n, ht, hkb, ?_⟩` and prove the remaining obligations.

Establish `: ((t ^ 2 + d * k ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ)`. Use `push_cast`. Rewrite using `[ht, hkb, hn]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.
-/
theorem half_coords {d : ℕ} (hd : d.Prime) {a b : ℚ}
    (hx : IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ)))) :
    ∃ t k n : ℤ, (t : ℚ) = 2 * a ∧ (k : ℚ) = 2 * b ∧ t ^ 2 + d * k ^ 2 = 4 * n := by
  have hw2 := sq_root d
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
    have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
    simpa [hwc, sub_eq_add_neg] using this
  obtain ⟨t, ht⟩ := int_of_isIntegral (r := 2 * a) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
    push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
    push_cast
    linear_combination (b : ℂ) ^ 2 * hw2)
  have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [hn, ht]; ring
  obtain ⟨m, hm⟩ := int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
    rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
    exact isIntegral_int _))
  have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
    have : ((m ^ 2 : ℤ) : ℚ) = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      rw [← hm2, ← hm]; push_cast; ring
    exact_mod_cast this
  obtain ⟨k, hk⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, hm3⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hkb : (k : ℚ) = 2 * b := by
    apply mul_left_cancel₀ hd0
    rw [← hm, hk]; push_cast; ring
  refine ⟨t, k, n, ht, hkb, ?_⟩
  have : ((t ^ 2 + d * k ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
    push_cast
    rw [ht, hkb, hn]; ring
  exact_mod_cast this

/- English proof (translation)
Take `⟨c, rfl⟩ : ∃ c, d = 4 * c + 1` from `⟨d / 4, by omega⟩`. Move the coercions through the operations in `at h`. Apply the tactic sequence `rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩`. Conclude with `⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩`. Establish `: 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 1` using `by linear_combination -h`.

Use linear arithmetic over natural numbers and integers. Establish `: 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - q ^ 2) = 1` using `by linear_combination -h`. Use linear arithmetic over natural numbers and integers. Establish `: 4 * (n - p ^ 2 - p - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 2` using `by linear_combination -h`. Use linear arithmetic over natural numbers and integers.
-/
theorem even_of_one {d : ℕ} (h4 : d % 4 = 1) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t ∧ 2 ∣ k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 1 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - q ^ 2) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 2 := by linear_combination -h
    omega

/- English proof (translation)
Take `⟨c, rfl⟩ : ∃ c, d = 4 * c + 3` from `⟨d / 4, by omega⟩`. Move the coercions through the operations in `at h`. Apply the tactic sequence `rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩`. Conclude with `⟨p + q, by ring⟩`. Establish `: 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - 3 * q ^ 2 - 3 * q) = 3` using `by linear_combination -h`.

Use linear arithmetic over natural numbers and integers. Establish `: 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - 3 * q ^ 2) = 1` using `by linear_combination -h`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨p + q + 1, by ring⟩`.
-/
theorem even_of_three {d : ℕ} (h4 : d % 4 = 3) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t + k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 3 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨p + q, by ring⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - 3 * q ^ 2 - 3 * q) = 3 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - 3 * q ^ 2) = 1 := by linear_combination -h
    omega
  · exact ⟨p + q + 1, by ring⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, a, b, rfl⟩`. Take `⟨t, k, n, ht, hk, h⟩` from `half_coords hd hx`. Take `⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩` from `even_of_one h4 h`. Establish `ha : a = p` using `by push_cast at ht; linarith`.

Establish `hb : b = q` using `by push_cast at hk; linarith`. Conclude with `⟨q, p, by rw [ha, hb]; push_cast; ring⟩`. Introduce and unpack `⟨u, v, rfl⟩`. Establish `hw : IsIntegral ℤ (Complex.I * (Real.sqrt d : ℝ))`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations.

Rewrite using `[sq_root]`. Simplify using `using isIntegral_int (-(d : ℤ))`. Use `⟨?_, v, u, by push_cast; ring⟩` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `((isIntegral_int u).mul hw).add (isIntegral_int v)`.
-/
theorem integers_one {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 1) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * (Complex.I * (Real.sqrt d : ℝ)) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := even_of_one h4 h
    have ha : a = p := by push_cast at ht; linarith
    have hb : b = q := by push_cast at hk; linarith
    exact ⟨q, p, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw : IsIntegral ℤ (Complex.I * (Real.sqrt d : ℝ)) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [sq_root]
      simpa using isIntegral_int (-(d : ℤ))
    refine ⟨?_, v, u, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, a, b, rfl⟩`. Take `⟨t, k, n, ht, hk, h⟩` from `half_coords hd hx`. Take `⟨j, hj⟩` from `even_of_three h4 h`. Establish `hj' : (t : ℚ) + k = 2 * j` using `by exact_mod_cast hj`.

Establish `ha : a = j - k / 2` using `by linarith`. Establish `hb : b = k / 2` using `by linarith`. Conclude with `⟨k, j, by rw [ha, hb]; push_cast; ring⟩`. Introduce and unpack `⟨u, v, rfl⟩`. Establish `hw2` using `sq_root d`.

Take `⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c` from `⟨(d + 1) / 4, by omega⟩`. Establish `hcC : (d : ℂ) + 1 = 4 * c` using `by exact_mod_cast hc`. Establish `hw : IsIntegral ℤ ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2)`. Use `⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, algebraMap_int_eq, eq_intCast, Int.cast_natCast]`.

Take the linear combination `(1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC`. Use `⟨?_, v - u / 2, u / 2, by push_cast; ring⟩` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `((isIntegral_int u).mul hw).add (isIntegral_int v)`.
-/
theorem integers_three {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨j, hj⟩ := even_of_three h4 h
    have hj' : (t : ℚ) + k = 2 * j := by exact_mod_cast hj
    have ha : a = j - k / 2 := by linarith
    have hb : b = k / 2 := by linarith
    exact ⟨k, j, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw2 := sq_root d
    obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
    have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
    have hw : IsIntegral ℤ ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        algebraMap_int_eq, eq_intCast, Int.cast_natCast]
      linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
    refine ⟨?_, v - u / 2, u / 2, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

/- English proof (translation)
Introduce `E _ _ _ I _ d φ Λ hF hΛ`. Take `⟨hd, h4, -, -, -, -, -, w, hw, hφ⟩` from `hF`. Establish `hs : 0 < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd.pos)`. Establish `hodd : d % 2 = 1` using `hd.eq_two_or_odd.resolve_left (by omega)`. Distinguish the cases in `h3 : d % 4 = 3`.

Establish `him : ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2 : ℂ).im = Real.sqrt d / 2` using `by simp`. Use `⟨w, (-1 + w) / 2, ⟨(-1 + Complex.I * (Real.sqrt d : ℝ)) / 2, by rw [him]; positivity⟩, hw, hφ, by rw [if_pos h3], fun i => ?_, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_three hd h3 x)⟩, Or.inl ⟨h3, him⟩⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_add, map_neg, map_one, map_ofNat, hφ]`. Establish `h1 : d % 4 = 1` using `by omega`. Establish `him : (Complex.I * (Real.sqrt d : ℝ) : ℂ).im = Real.sqrt d` using `by simp`.

Conclude with `⟨w, w, ⟨Complex.I * (Real.sqrt d : ℝ), by rw [him]; exact hs⟩, hw, hφ, by rw [if_neg h3], hφ, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_one hd h1 x)⟩, Or.inr ⟨h1, him⟩⟩`.
-/
theorem exists_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ) (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ (w θ : E) (τ : ℍ), w ^ 2 = -(d : E) ∧ (∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)) ∧ θ = (if d % 4 = 3 then (-1 + w) / 2 else w) ∧ (∀ i, φ i θ = (τ : ℂ)) ∧ IsTauOf Λ 1 τ ∧ ((d % 4 = 3 ∧ τ.im = Real.sqrt d / 2) ∨ (d % 4 = 1 ∧ τ.im = Real.sqrt d)) := by
  intro E _ _ _ I _ d φ Λ hF hΛ
  obtain ⟨hd, h4, -, -, -, -, -, w, hw, hφ⟩ := hF
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
  have hodd : d % 2 = 1 := hd.eq_two_or_odd.resolve_left (by omega)
  by_cases h3 : d % 4 = 3
  · have him : ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2 : ℂ).im = Real.sqrt d / 2 := by simp
    refine ⟨w, (-1 + w) / 2, ⟨(-1 + Complex.I * (Real.sqrt d : ℝ)) / 2, by rw [him]; positivity⟩, hw, hφ,
      by rw [if_pos h3], fun i => ?_, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_three hd h3 x)⟩, Or.inl ⟨h3, him⟩⟩
    rw [map_div₀, map_add, map_neg, map_one, map_ofNat, hφ]
  · have h1 : d % 4 = 1 := by omega
    have him : (Complex.I * (Real.sqrt d : ℝ) : ℂ).im = Real.sqrt d := by simp
    exact ⟨w, w, ⟨Complex.I * (Real.sqrt d : ℝ), by rw [him]; exact hs⟩, hw, hφ,
      by rw [if_neg h3], hφ, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_one hd h1 x)⟩, Or.inr ⟨h1, him⟩⟩

end GlobalTheory.QuadGenerator
