import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `R _ _ p hp π M ζ hcop hζ`. Establish `hpp : p.Prime` using `hp.out`. Establish `hM : 0 < M`. Break down `Nat.eq_zero_or_pos M with rfl | h` into its components or cases. Conclude with `absurd (Nat.coprime_zero_right p |>.mp hcop) hpp.one_lt.ne'`.

Conclude with `h`. Establish `hne : NeZero (M : ZMod p)`. Use `⟨fun h => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[ZMod.natCast_eq_zero_iff]`. Conclude with `hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)`.

Establish `hroot : (Polynomial.cyclotomic M R).IsRoot ζ` using `hζ.isRoot_cyclotomic hM`. Establish `hroot' : (Polynomial.cyclotomic M (ZMod p)).IsRoot (π ζ)`. Rewrite using `[← Polynomial.map_cyclotomic M π]`. Conclude with `hroot.map`. Establish `hprim : IsPrimitiveRoot (π ζ) M` using `(Polynomial.isRoot_cyclotomic_iff).mp hroot'`.

Use `⟨hprim, hprim.dvd_of_pow_eq_one _ ?_⟩` and prove the remaining obligations. Conclude with `ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hM.ne')`.
-/
theorem UpperTheory.V.Stick.redRoot :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M : ℕ) (ζ : R),
    p.Coprime M → IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M ∧ M ∣ p - 1 := by
  intro R _ _ p hp π M ζ hcop hζ
  have hpp : p.Prime := hp.out
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · exact absurd (Nat.coprime_zero_right p |>.mp hcop) hpp.one_lt.ne'
    · exact h
  have hne : NeZero (M : ZMod p) := by
    refine ⟨fun h => ?_⟩
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hroot : (Polynomial.cyclotomic M R).IsRoot ζ := hζ.isRoot_cyclotomic hM
  have hroot' : (Polynomial.cyclotomic M (ZMod p)).IsRoot (π ζ) := by
    rw [← Polynomial.map_cyclotomic M π]
    exact hroot.map
  have hprim : IsPrimitiveRoot (π ζ) M := (Polynomial.isRoot_cyclotomic_iff).mp hroot'
  refine ⟨hprim, hprim.dvd_of_pow_eq_one _ ?_⟩
  exact ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hM.ne')
