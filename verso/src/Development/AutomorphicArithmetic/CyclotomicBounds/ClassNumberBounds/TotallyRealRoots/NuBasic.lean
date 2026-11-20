import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← Units.val_eq_one, show ((red l u : (ZMod l)ˣ) : ZMod l) = PadicInt.toZMod (u : ℤ_[l]) from rfl, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`.
-/
private theorem nb_red_eq_one {u : ℤ_[l]ˣ} : red l u = 1 ↔ (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
  rw [← Units.val_eq_one, show ((red l u : (ZMod l)ˣ) : ZMod l) = PadicInt.toZMod (u : ℤ_[l]) from rfl,
    ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

/- English proof (translation)
Rewrite using `[← Order.one_le_iff_pos, ← Nat.cast_one (R := ℕ∞), le_nu_iff, resOrder, ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]`. Simplify using `only [pow_one, ← Units.val_pow_eq_pow_val, ← nb_red_eq_one, map_pow]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨_, u, hu, rfl⟩`. Conclude with `Subtype.ext (h u hu)`.

Introduce `h u hu`. Conclude with `congrArg Subtype.val (h ⟨red l u, u, hu, rfl⟩)`.
-/
theorem nu_pos_iff (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : 0 < nu l U tr ↔ resOrder l U ∣ tr := by
  rw [← Order.one_le_iff_pos, ← Nat.cast_one (R := ℕ∞), le_nu_iff, resOrder,
    ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  simp only [pow_one, ← Units.val_pow_eq_pow_val, ← nb_red_eq_one, map_pow]
  constructor
  · rintro h ⟨_, u, hu, rfl⟩
    exact Subtype.ext (h u hu)
  · intro h u hu
    exact congrArg Subtype.val (h ⟨red l u, u, hu, rfl⟩)

/- English proof (translation)
The claim follows from `nb_red_eq_one.mp (Subsingleton.elim _ _)`.
-/
private theorem nb_two_dvd (u : ℤ_[2]ˣ) : ((2 : ℕ) : ℤ_[2]) ∣ (u : ℤ_[2]) - 1 :=
  nb_red_eq_one.mp (Subsingleton.elim _ _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `nuStar_eq_nuStar_one PadicInt.prime_p ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, -, rfl⟩`. Conclude with `nb_two_dvd u`. Introduce `h`.

Rewrite `h` using `[← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff]`. Conclude with `(Nat.not_even_iff_odd.mpr htr) (even_iff_two_dvd.mpr h)`. Rewrite using `[← Nat.cast_one (R := ℕ∞), le_nu_iff]`. Introduce `u _`. Rewrite using `[pow_one, ← Units.val_pow_eq_pow_val]`.

Conclude with `nb_two_dvd _`.
-/
theorem nu_two_of_odd (U : Subgroup ℤ_[2]ˣ) {tr : ℕ} (htr : Odd tr) :
    nu 2 U tr = nu 2 U 1 ∧ 1 ≤ nu 2 U tr := by
  constructor
  · refine nuStar_eq_nuStar_one PadicInt.prime_p ?_ ?_
    · rintro _ ⟨u, -, rfl⟩
      exact nb_two_dvd u
    · intro h
      rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff] at h
      exact (Nat.not_even_iff_odd.mpr htr) (even_iff_two_dvd.mpr h)
  · rw [← Nat.cast_one (R := ℕ∞), le_nu_iff]
    intro u _
    rw [pow_one, ← Units.val_pow_eq_pow_val]
    exact nb_two_dvd _

end KStar.TotallyRealRoots
