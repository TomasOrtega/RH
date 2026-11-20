import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`.
-/
private theorem toZMod_eq_zero_iff (x : ℤ_[l]) : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem val_red (u : ℤ_[l]ˣ) :
    ((red l u : (ZMod l)ˣ) : ZMod l) = PadicInt.toZMod (u : ℤ_[l]) := rfl

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hna : ‖a‖ = 1`. Use `le_antisymm (PadicInt.norm_le_one a) (not_lt.1 fun h => ha ?_)` and prove the remaining obligations. Conclude with `(toZMod_eq_zero_iff a).2 h`. Use `set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hF`.

Establish `hev : ∀ z : ℤ_[l], Polynomial.aeval z F = z ^ (l - 1) - 1`. Introduce `z`. Simplify using `[hF]`. Establish `hder : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1`. Establish `: Polynomial.aeval a (Polynomial.derivative F) = ((l - 1 : ℕ) : ℤ_[l]) * a ^ (l - 1 - 1)`.

Rewrite using `[hF, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero, Polynomial.derivative_X_pow, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]`. Rewrite using `[this, norm_mul, norm_pow, hna, PadicInt.norm_natCast_p_sub_one]`. Simplify using the standard rewrite rules. Establish `hnorm : ‖Polynomial.aeval a F‖ < ‖Polynomial.aeval a (Polynomial.derivative F)‖ ^ 2`. Rewrite using `[hder, one_pow, hev, ← toZMod_eq_zero_iff, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one ha, sub_self]`.

Take `⟨z, hz, hza, -⟩` from `hensels_lemma hnorm`. Rewrite `hz` using `[hev, sub_eq_zero]`. Rewrite `hza` using `[hder, ← toZMod_eq_zero_iff, map_sub, sub_eq_zero]`. Establish `hu : IsUnit z` using `IsUnit.of_pow_eq_one hz (by omega)`. Use `⟨hu.unit, ?_, by simpa using hza⟩` and prove the remaining obligations.

Rewrite using `[mem_rootsOfUnity']`. Simplify using `using hz`.
-/
private theorem exists_root_lift (a : ℤ_[l]) (ha : PadicInt.toZMod a ≠ 0) :
    ∃ ζ ∈ rootsOfUnity (l - 1) ℤ_[l], PadicInt.toZMod (ζ : ℤ_[l]) = PadicInt.toZMod a := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hna : ‖a‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one a) (not_lt.1 fun h => ha ?_)
    exact (toZMod_eq_zero_iff a).2 h
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hF
  have hev : ∀ z : ℤ_[l], Polynomial.aeval z F = z ^ (l - 1) - 1 := by
    intro z; simp [hF]
  have hder : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    have : Polynomial.aeval a (Polynomial.derivative F)
        = ((l - 1 : ℕ) : ℤ_[l]) * a ^ (l - 1 - 1) := by
      rw [hF, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        map_natCast]
    rw [this, norm_mul, norm_pow, hna, PadicInt.norm_natCast_p_sub_one]
    simp
  have hnorm : ‖Polynomial.aeval a F‖ < ‖Polynomial.aeval a (Polynomial.derivative F)‖ ^ 2 := by
    rw [hder, one_pow, hev, ← toZMod_eq_zero_iff, map_sub, map_pow, map_one,
      ZMod.pow_card_sub_one_eq_one ha, sub_self]
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma hnorm
  rw [hev, sub_eq_zero] at hz
  rw [hder, ← toZMod_eq_zero_iff, map_sub, sub_eq_zero] at hza
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz (by omega)
  refine ⟨hu.unit, ?_, by simpa using hza⟩
  rw [mem_rootsOfUnity']
  simpa using hz

/- English proof (translation)
Take `⟨ζ, h1, h2⟩` from `exists_root_lift (u : ℤ_[l]) (by rw [← val_red]; exact Units.ne_zero _)`. Conclude with `⟨ζ, h1, Units.ext (by rw [val_red, val_red, h2])⟩`.
-/
theorem exists_teich (u : ℤ_[l]ˣ) :
    ∃ ζ ∈ rootsOfUnity (l - 1) ℤ_[l], red l ζ = red l u := by
  obtain ⟨ζ, h1, h2⟩ := exists_root_lift (u : ℤ_[l]) (by rw [← val_red]; exact Units.ne_zero _)
  exact ⟨ζ, h1, Units.ext (by rw [val_red, val_red, h2])⟩

/- English proof (translation)
Rewrite `hζ` using `[mem_rootsOfUnity']`. Establish `h` using `mul_geom_sum (ζ : ℤ_[l]) o`. Rewrite `h` using `[hζ, sub_self, mul_eq_zero]`. Break down `h with h | h` into its components or cases. Conclude with `Units.ext (by simpa [sub_eq_zero] using h)`.

It suffices to derive a contradiction. Use `congrArg PadicInt.toZMod h` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify using `only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this`. Conclude with `ho ((ZMod.natCast_eq_zero_iff o l).1 this)`.
-/
private theorem eq_one_of_toZMod {o : ℕ} (ho : ¬ l ∣ o) {ζ : ℤ_[l]ˣ}
    (hζ : ζ ∈ rootsOfUnity o ℤ_[l]) (h1 : PadicInt.toZMod (ζ : ℤ_[l]) = 1) : ζ = 1 := by
  rw [mem_rootsOfUnity'] at hζ
  have h := mul_geom_sum (ζ : ℤ_[l]) o
  rw [hζ, sub_self, mul_eq_zero] at h
  rcases h with h | h
  · exact Units.ext (by simpa [sub_eq_zero] using h)
  · exfalso
    have := congrArg PadicInt.toZMod h
    rw [map_sum, map_zero] at this
    simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    exact ho ((ZMod.natCast_eq_zero_iff o l).1 this)

/- English proof (translation)
Use `eq_one_of_toZMod ho hζ ?_` and prove the remaining obligations. Rewrite `h1` using `[mem_princ, pow_one, ← PadicInt.norm_lt_one_iff_dvd, ← toZMod_eq_zero_iff, map_sub, map_one, sub_eq_zero]`. Conclude with `h1`.
-/
theorem eq_one_of_mem_princ_one {o : ℕ} (ho : ¬ l ∣ o) {ζ : ℤ_[l]ˣ}
    (hζ : ζ ∈ rootsOfUnity o ℤ_[l]) (h1 : ζ ∈ princ l 1) : ζ = 1 := by
  refine eq_one_of_toZMod ho hζ ?_
  rw [mem_princ, pow_one, ← PadicInt.norm_lt_one_iff_dvd, ← toZMod_eq_zero_iff, map_sub, map_one,
    sub_eq_zero] at h1
  exact h1

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ζ, hζ, rfl⟩`. Establish `hζ' : ζ ^ o = 1` using `(mem_rootsOfUnity o ζ).1 hζ`.

Rewrite using `[mem_rootsOfUnity, ← map_pow, hζ', map_one]`. Introduce `hx`. Rewrite `hx` using `[mem_rootsOfUnity]`. Take `⟨a, ha⟩` from `ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (x : ZMod l)`. Take `⟨ζ, h1, h2⟩` from `exists_root_lift a (by rw [ha]; exact Units.ne_zero _)`.

Establish `hr : red l ζ = x` using `Units.ext (by rw [val_red, h2, ha])`. Use `⟨ζ, ?_, hr⟩` and prove the remaining obligations. Establish `hnd : ¬ l ∣ l - 1` using `fun h => by`. Use `Nat.le_of_dvd (by omega) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `(mem_rootsOfUnity o ζ).2 (eq_one_of_toZMod hnd (Subgroup.pow_mem _ h1 o) ?_)` and prove the remaining obligations. Rewrite using `[← val_red, map_pow, hr, hx, Units.val_one]`.
-/
theorem map_red_rootsOfUnity {o : ℕ} (ho : o ∣ l - 1) :
    (rootsOfUnity o ℤ_[l]).map (red l) = rootsOfUnity o (ZMod l) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  ext x
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    have hζ' : ζ ^ o = 1 := (mem_rootsOfUnity o ζ).1 hζ
    rw [mem_rootsOfUnity, ← map_pow, hζ', map_one]
  · intro hx
    rw [mem_rootsOfUnity] at hx
    obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (x : ZMod l)
    obtain ⟨ζ, h1, h2⟩ := exists_root_lift a (by rw [ha]; exact Units.ne_zero _)
    have hr : red l ζ = x := Units.ext (by rw [val_red, h2, ha])
    refine ⟨ζ, ?_, hr⟩
    have hnd : ¬ l ∣ l - 1 := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    refine (mem_rootsOfUnity o ζ).2 (eq_one_of_toZMod hnd (Subgroup.pow_mem _ h1 o) ?_)
    rw [← val_red, map_pow, hr, hx, Units.val_one]

end KStar.TotallyRealRoots
