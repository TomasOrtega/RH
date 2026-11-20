import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp (PadicInt.maximalIdeal_eq_span_p (p := l) ▸ PadicInt.sub_zmodRepr_mem a)`. Rewrite using `[PadicInt.val_toZMod_eq_zmodRepr]`. Establish `h` using `congrArg f hc`. Rewrite `h` using `[map_mul, map_natCast, hl, mul_zero, map_sub, map_natCast, eq_comm, sub_eq_zero]`. Conclude with `h`.
-/
private theorem zlUniq_val (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hl : (l : R) = 0) (a : ℤ_[l]) : f a = ((PadicInt.toZMod a).val : R) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.maximalIdeal_eq_span_p (p := l) ▸ PadicInt.sub_zmodRepr_mem a)
  rw [PadicInt.val_toZMod_eq_zmodRepr]
  have h := congrArg f hc
  rw [map_mul, map_natCast, hl, mul_zero, map_sub, map_natCast, eq_comm, sub_eq_zero] at h
  exact h

/- English proof (translation)
Introduce `l _`. Use `⟨fun {K} _ _ f => ?_, fun {R} _ f f' hl => ⟨?_, zlUniq_val l f hl⟩⟩` and prove the remaining obligations. Take `⟨p, hchar⟩` from `CharP.exists K`. Establish `hp : p.Prime` using `CharP.char_is_prime K p`. Establish `hpl : p = l`.

Assume the negation of the conclusion as `hne`. Establish `hunit : IsUnit (p : ℤ_[l])`. Assume the negation of the conclusion as `hnu`. Establish `hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1`. Rewrite using `[Int.cast_natCast]`.

Conclude with `PadicInt.mem_nonunits.mp hnu`. Rewrite `hlt` using `[PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast]`. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm`. Establish `h` using `hunit.map f`. Rewrite `h` using `[map_natCast, CharP.cast_eq_zero]`.

Conclude with `not_isUnit_zero h`. Substitute `hpl` using the available equality. Conclude with `hchar`. Use extensionality with `a`. Rewrite using `[zlUniq_val l f hl, zlUniq_val l f' hl]`.
-/
theorem UpperTheory.V.Pa.Det.zlUniq :
    ∀ (l : ℕ) [Fact l.Prime], (∀ {K : Type} [Field K] [Finite K] (_ : ℤ_[l] →+* K), CharP K l) ∧ ∀ {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R), (l : R) = 0 → f = f' ∧ ∀ a, f a = ((PadicInt.toZMod a).val : R) := by
  intro l _
  refine ⟨fun {K} _ _ f => ?_, fun {R} _ f f' hl => ⟨?_, zlUniq_val l f hl⟩⟩
  · obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    have hpl : p = l := by
      by_contra hne
      have hunit : IsUnit (p : ℤ_[l]) := by
        by_contra hnu
        have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
          rw [Int.cast_natCast]
          exact PadicInt.mem_nonunits.mp hnu
        rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
        exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
      have h := hunit.map f
      rw [map_natCast, CharP.cast_eq_zero] at h
      exact not_isUnit_zero h
    subst hpl
    exact hchar
  · ext a
    rw [zlUniq_val l f hl, zlUniq_val l f' hl]
