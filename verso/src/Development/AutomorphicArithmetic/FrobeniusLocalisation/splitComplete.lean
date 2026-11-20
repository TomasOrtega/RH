import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobDecomp

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

/- English proof (translation)
Introduce `φ H p hp h1`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hdvd : H.condN ∣ p - 1` using `(Nat.modEq_iff_dvd' hp.one_le).1 h1.symm`. Establish `h2` using `hp.two_le`. Establish `hlt : H.condN < p`.

Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hnd : ¬ p ∣ H.condN` using `fun h => absurd (Nat.le_of_dvd H.condN_pos h) (by omega)`. Establish `hc : Nat.Coprime p H.condN` using `hp.coprime_iff_not_dvd.2 hnd`. Establish `hfrob : H.frobG p = 1`.

Rewrite using `[H.frobG_of_coprime hc]`. Establish `hu : ZMod.unitOfCoprime p hc = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[ZMod.coe_unitOfCoprime, Units.val_one, (ZMod.natCast_eq_natCast_iff _ _ _).2 h1, Nat.cast_one]`. Rewrite using `[hu, map_one]`.

Use `⟨hnd, hfrob, ?_, hlt, ?_, ?_⟩` and prove the remaining obligations. Use `(UpperTheory.HF.frobG_spec φ H p hnd).2.2.2.2.1.1 ?_` and prove the remaining obligations. Rewrite using `[hfrob]`. Conclude with `one_mem _`. Use `Dvd.dvd.trans ?_ hdvd` and prove the remaining obligations.

Rewrite using `[mul_right_comm]`. Conclude with `Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right H.sixteen_dvd_QS _) _`. Use `haveI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)`. Take `⟨⟨P, hP1, hP2⟩⟩` from `Ideal.nonempty_primesOver (S := 𝓞 H.E) (span {(p : ℤ)})`. Establish `h` using `(UpperTheory.HF.frob_decomp φ H p hnd P).2.2`.

Rewrite `h` using `[hfrob, orderOf_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.HF.split_complete :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → p ≡ 1 [MOD H.condN] →
      ¬ p ∣ H.condN ∧ H.frobG p = 1 ∧ jacobiSym (-(H.d : ℤ)) p = 1 ∧ H.condN < p ∧ 16 * H.d * H.q ∣ p - 1 ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard = 4 * φ.ord := by
  intro φ H p hp h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : H.condN ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).1 h1.symm
  have h2 := hp.two_le
  have hlt : H.condN < p := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnd : ¬ p ∣ H.condN := fun h => absurd (Nat.le_of_dvd H.condN_pos h) (by omega)
  have hc : Nat.Coprime p H.condN := hp.coprime_iff_not_dvd.2 hnd
  have hfrob : H.frobG p = 1 := by
    rw [H.frobG_of_coprime hc]
    have hu : ZMod.unitOfCoprime p hc = 1 := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_one, (ZMod.natCast_eq_natCast_iff _ _ _).2 h1, Nat.cast_one]
    rw [hu, map_one]
  refine ⟨hnd, hfrob, ?_, hlt, ?_, ?_⟩
  · refine (UpperTheory.HF.frobG_spec φ H p hnd).2.2.2.2.1.1 ?_
    rw [hfrob]
    exact one_mem _
  · refine Dvd.dvd.trans ?_ hdvd
    rw [mul_right_comm]
    exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right H.sixteen_dvd_QS _) _
  · haveI : (span {(p : ℤ)}).IsPrime :=
      (span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨⟨P, hP1, hP2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 H.E) (span {(p : ℤ)})
    have h := (UpperTheory.HF.frob_decomp φ H p hnd P).2.2
    rwa [hfrob, orderOf_one, mul_one] at h
