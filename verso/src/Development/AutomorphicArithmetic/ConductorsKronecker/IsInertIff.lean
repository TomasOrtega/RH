import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

/- English proof (translation)
Establish `hdp` using `H.toHostRaw.d_prime`. Establish `hN0 : H.condN ≠ 0`. Simplify using `only [HostRaw.condN]`. Conclude with `Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) hdp.ne_zero`. Use `haveI : NeZero H.condN := ⟨hN0⟩`.

Use `set u := frobUnit H.condN p with hu`. Take `⟨h1, -⟩` from `frobUnit_modEq (N := H.condN) hp`. Establish `hcop : Nat.Coprime (p ^ H.condN.factorization p) H.d` using `Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hdp).mpr hd)`. Establish `hdm : H.d ∣ H.condN / p ^ H.condN.factorization p`. Establish `hsplit` using `Nat.ordProj_mul_ordCompl_eq_self H.condN p`.

Establish `: H.d ∣ p ^ H.condN.factorization p * (H.condN / p ^ H.condN.factorization p)`. Rewrite using `[hsplit]`. Conclude with `H.d_dvd_condN`. Conclude with `(Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this`. Establish `hmod : (u : ZMod H.condN).val ≡ p [MOD H.d]` using `Nat.ModEq.of_dvd hdm h1`.

Establish `hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = jacobiSym (-(H.d : ℤ)) p`. Rewrite using `[jacobi_congr hmod]`. Establish `hodd : p % 2 = 1` using `Nat.odd_iff.mp (hp.odd_of_ne_two h2)`. Conclude with `(jacobi_neg_recip H.d_mod_four hodd).symm`. Establish `hart` using `H.der.art_ch u`.

Rewrite `hart` using `[hJ]`. Use `show ¬ (Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (H.art u).1.2) = 0) ↔ _`. Rewrite using `[sgn2_toAdd_eq_zero_iff, ← hart]`. Break down `Int.units_eq_one_or (H.art u).1.2 with hs | hs` into its components or cases. Rewrite using `[hs]`.

Simplify using the standard rewrite rules. Rewrite using `[hs]`. Simplify using the standard rewrite rules.
-/
private lemma notInPhi_iff {φ : Frame} (H : HostAx φ) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hd : p ≠ H.d) :
    ¬ Formalism.D5.InPhi ((arith H.toHostRaw).frob p) ↔ jacobiSym (-(H.d : ℤ)) p = -1 := by
  have hdp := H.toHostRaw.d_prime
  have hN0 : H.condN ≠ 0 := by
    simp only [HostRaw.condN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) hdp.ne_zero
  haveI : NeZero H.condN := ⟨hN0⟩
  set u := frobUnit H.condN p with hu
  obtain ⟨h1, -⟩ := frobUnit_modEq (N := H.condN) hp
  have hcop : Nat.Coprime (p ^ H.condN.factorization p) H.d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hdp).mpr hd)
  have hdm : H.d ∣ H.condN / p ^ H.condN.factorization p := by
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self H.condN p
    have : H.d ∣ p ^ H.condN.factorization p * (H.condN / p ^ H.condN.factorization p) := by
      rw [hsplit]; exact H.d_dvd_condN
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hmod : (u : ZMod H.condN).val ≡ p [MOD H.d] := Nat.ModEq.of_dvd hdm h1
  have hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = jacobiSym (-(H.d : ℤ)) p := by
    rw [jacobi_congr hmod]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    exact (jacobi_neg_recip H.d_mod_four hodd).symm
  have hart := H.der.art_ch u
  rw [hJ] at hart
  show ¬ (Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (H.art u).1.2) = 0) ↔ _
  rw [sgn2_toAdd_eq_zero_iff, ← hart]
  rcases Int.units_eq_one_or (H.art u).1.2 with hs | hs
  · rw [hs]; simp
  · rw [hs]; simp

/- English proof (translation)
Introduce `φ H p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, h2, -, hd, h⟩`. Establish `hj` using `(notInPhi_iff H hp h2 hd).1 h`. Conclude with `⟨hp, H.not_dvd_condN_of_inert hp h2 hj, hj⟩`.

Introduce and unpack `⟨hp, hN, hj⟩`. Conclude with `⟨hp, HostRaw.ne_two_of_not_dvd hN, HostRaw.ne_q_of_not_dvd hN, HostRaw.ne_d_of_not_dvd hN, (notInPhi_iff H hp (HostRaw.ne_two_of_not_dvd hN) (HostRaw.ne_d_of_not_dvd hN)).2 hj⟩`.
-/
theorem UpperTheory.GL.isInert_iff :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), IsInert (arith H.toHostRaw) p ↔ p.Prime ∧ ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 := by
  intro φ H p
  constructor
  · rintro ⟨hp, h2, -, hd, h⟩
    have hj := (notInPhi_iff H hp h2 hd).1 h
    exact ⟨hp, H.not_dvd_condN_of_inert hp h2 hj, hj⟩
  · rintro ⟨hp, hN, hj⟩
    exact ⟨hp, HostRaw.ne_two_of_not_dvd hN, HostRaw.ne_q_of_not_dvd hN, HostRaw.ne_d_of_not_dvd hN,
      (notInPhi_iff H hp (HostRaw.ne_two_of_not_dvd hN) (HostRaw.ne_d_of_not_dvd hN)).2 hj⟩
