import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce and unpack `⟨c, hc⟩`. Apply `hm` to reduce the goal to its premises. Establish `h` using `congrArg PadicInt.toZMod hc`. Rewrite `h` using `[map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul]`. Conclude with `(ZMod.natCast_eq_zero_iff m l).mp h`.
-/
private theorem lte_not_dvd_natCast {m : ℕ} (hm : ¬ l ∣ m) : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
  rintro ⟨c, hc⟩
  apply hm
  have h := congrArg PadicInt.toZMod hc
  rw [map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul] at h
  exact (ZMod.natCast_eq_zero_iff m l).mp h

/- English proof (translation)
Introduce `h`. Establish `h1 : (l : ℤ_[l]) ∣ 1`. Use `dvd_sub h hu` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Conclude with `PadicInt.prime_p.not_unit (isUnit_of_dvd_one h1)`.
-/
private theorem lte_not_dvd_of_dvd_sub_one {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1) :
    ¬ (l : ℤ_[l]) ∣ u := by
  intro h
  have h1 : (l : ℤ_[l]) ∣ 1 := by
    have := dvd_sub h hu
    rwa [sub_sub_cancel] at this
  exact PadicInt.prime_p.not_unit (isUnit_of_dvd_one h1)

/- English proof (translation)
Break down `n with - | n` into its components or cases. Simplify using the standard rewrite rules. Establish `hfin : FiniteMultiplicity l (n + 1)` using `Nat.finiteMultiplicity_iff.mpr ⟨(Fact.out : l.Prime).ne_one, n.succ_pos⟩`. Break down `emultiplicity_eq_coe.mp hfin.emultiplicity_eq_multiplicity with ⟨⟨c, hc⟩, hnot⟩` into its components or cases. Use `set k := multiplicity l (n + 1) with hk`.

Establish `hcl : ¬ l ∣ c`. Introduce and unpack `⟨d, rfl⟩`. Conclude with `hnot ⟨d, by rw [hc, pow_succ, mul_assoc]⟩`. Establish `hx : (l : ℤ_[l]) ∣ u ^ l ^ k - 1`. Use `sub_dvd_pow_sub_pow u 1 (l ^ k)` as an intermediate fact.

Rewrite `this` using `[one_pow]`. Conclude with `hu.trans this`. Establish `e : u ^ (l ^ k * c) - 1 = (u ^ l ^ k) ^ c - 1 ^ c` using `by rw [one_pow, pow_mul]`. Rewrite using `[hfin.emultiplicity_eq_multiplicity, ← hk]`. Use `conv_lhs => rw [hc, e]`.

Rewrite using `[emultiplicity_pow_sub_pow_of_prime PadicInt.prime_p hx (lte_not_dvd_of_dvd_sub_one hx) (lte_not_dvd_natCast hcl), h k]`.
-/
private theorem lte_reduce {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1)
    (h : ∀ k : ℕ, emultiplicity (l : ℤ_[l]) (u ^ l ^ k - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + k) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  rcases n with - | n
  · simp
  have hfin : FiniteMultiplicity l (n + 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨(Fact.out : l.Prime).ne_one, n.succ_pos⟩
  rcases emultiplicity_eq_coe.mp hfin.emultiplicity_eq_multiplicity with ⟨⟨c, hc⟩, hnot⟩
  set k := multiplicity l (n + 1) with hk
  have hcl : ¬ l ∣ c := by
    rintro ⟨d, rfl⟩
    exact hnot ⟨d, by rw [hc, pow_succ, mul_assoc]⟩
  have hx : (l : ℤ_[l]) ∣ u ^ l ^ k - 1 := by
    have := sub_dvd_pow_sub_pow u 1 (l ^ k)
    rw [one_pow] at this
    exact hu.trans this
  have e : u ^ (l ^ k * c) - 1 = (u ^ l ^ k) ^ c - 1 ^ c := by rw [one_pow, pow_mul]
  rw [hfin.emultiplicity_eq_multiplicity, ← hk]
  conv_lhs => rw [hc, e]
  rw [emultiplicity_pow_sub_pow_of_prime PadicInt.prime_p hx (lte_not_dvd_of_dvd_sub_one hx)
    (lte_not_dvd_natCast hcl), h k]

/- English proof (translation)
Use `lte_reduce hu (fun k => ?_) n` and prove the remaining obligations. Establish `h` using `emultiplicity_pow_prime_pow_sub_pow_prime_pow (p := l) (x := u) (y := 1) PadicInt.prime_p ((Fact.out : l.Prime).odd_of_ne_two hl) hu (lte_not_dvd_of_dvd_sub_one hu) k`. Rewrite `h` using `[one_pow]`. Then use the resulting hypothesis.
-/
theorem emultiplicity_pow_sub_one_odd (hl : l ≠ 2) {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  refine lte_reduce hu (fun k => ?_) n
  have h := emultiplicity_pow_prime_pow_sub_pow_prime_pow (p := l) (x := u) (y := 1)
    PadicInt.prime_p ((Fact.out : l.Prime).odd_of_ne_two hl) hu (lte_not_dvd_of_dvd_sub_one hu) k
  rwa [one_pow] at h

/- English proof (translation)
Substitute `hl` using the available equality. Establish `hp : Prime ((2 : ℕ) : ℤ_[2])` using `PadicInt.prime_p`. Establish `h2 : ((2 : ℕ) : ℤ_[2]) ∣ w - 1` using `(dvd_pow_self _ two_ne_zero).trans hw`. Rewrite using `[show w ^ 2 - 1 = (w - 1) * (w + 1) by ring, emultiplicity_mul hp]`. Use `congr 1`.

Rewrite using `[← Nat.cast_one (R := ℕ∞)]`. Use `emultiplicity_eq_coe.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, show w + 1 = (w - 1) + ((2 : ℕ) : ℤ_[2]) by push_cast; ring]`. Conclude with `dvd_add h2 (dvd_refl _)`. Rewrite using `[one_add_one_eq_two]`.

Introduce `h`. Establish `h3` using `dvd_sub h hw`. Rewrite `h3` using `[show (w + 1) - (w - 1) = ((2 : ℕ) : ℤ_[2]) * 1 by push_cast; ring, pow_two, mul_dvd_mul_iff_left hp.ne_zero]`. Conclude with `hp.not_unit (isUnit_of_dvd_one h3)`.
-/
private theorem lte_two_step (hl : l = 2) {w : ℤ_[l]} (hw : (l : ℤ_[l]) ^ 2 ∣ w - 1) :
    emultiplicity (l : ℤ_[l]) (w ^ l - 1) = emultiplicity (l : ℤ_[l]) (w - 1) + 1 := by
  subst hl
  have hp : Prime ((2 : ℕ) : ℤ_[2]) := PadicInt.prime_p
  have h2 : ((2 : ℕ) : ℤ_[2]) ∣ w - 1 := (dvd_pow_self _ two_ne_zero).trans hw
  rw [show w ^ 2 - 1 = (w - 1) * (w + 1) by ring, emultiplicity_mul hp]
  congr 1
  rw [← Nat.cast_one (R := ℕ∞)]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one, show w + 1 = (w - 1) + ((2 : ℕ) : ℤ_[2]) by push_cast; ring]
    exact dvd_add h2 (dvd_refl _)
  · rw [one_add_one_eq_two]
    intro h
    have h3 := dvd_sub h hw
    rw [show (w + 1) - (w - 1) = ((2 : ℕ) : ℤ_[2]) * 1 by push_cast; ring, pow_two,
      mul_dvd_mul_iff_left hp.ne_zero] at h3
    exact hp.not_unit (isUnit_of_dvd_one h3)

/- English proof (translation)
Establish `hu1 : (l : ℤ_[l]) ∣ u - 1` using `(dvd_pow_self _ two_ne_zero).trans hu`. Distinguish the cases in `hl : l = 2`. Use `lte_reduce hu1 (fun k => ?_) n` and prove the remaining obligations. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Establish `hw : (l : ℤ_[l]) ^ 2 ∣ u ^ l ^ k - 1`. Use `sub_dvd_pow_sub_pow u 1 (l ^ k)` as an intermediate fact. Rewrite `this` using `[one_pow]`. Conclude with `hu.trans this`.

Rewrite using `[pow_succ, pow_mul, lte_two_step hl hw, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `emultiplicity_pow_sub_one_odd hl hu1 n`.
-/
theorem emultiplicity_pow_sub_one_sq {u : ℤ_[l]} (hu : (l : ℤ_[l]) ^ 2 ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  have hu1 : (l : ℤ_[l]) ∣ u - 1 := (dvd_pow_self _ two_ne_zero).trans hu
  by_cases hl : l = 2
  · refine lte_reduce hu1 (fun k => ?_) n
    induction k with
    | zero => simp
    | succ k ih =>
      have hw : (l : ℤ_[l]) ^ 2 ∣ u ^ l ^ k - 1 := by
        have := sub_dvd_pow_sub_pow u 1 (l ^ k)
        rw [one_pow] at this
        exact hu.trans this
      rw [pow_succ, pow_mul, lte_two_step hl hw, ih]
      push_cast
      ring
  · exact emultiplicity_pow_sub_one_odd hl hu1 n

end KStar.TotallyRealRoots
