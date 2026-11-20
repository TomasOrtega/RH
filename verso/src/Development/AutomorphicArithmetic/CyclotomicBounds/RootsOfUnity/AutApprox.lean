import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
open NumberField KStar.Tree

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : NeZero M := ⟨hM⟩`. Take `⟨ξ, hξ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Establish `hξ' : IsPrimitiveRoot (ξ ^ a) M` using `hξ.pow_of_coprime a ha`. Establish `hpos : 0 < M` using `Nat.pos_of_ne_zero hM`.

Establish `hc : IsConjRoot ℚ (ξ ^ a) ξ`. Unfold `IsConjRoot`. Rewrite using `[← Polynomial.cyclotomic_eq_minpoly_rat hξ hpos, ← Polynomial.cyclotomic_eq_minpoly_rat hξ' hpos]`. Take `⟨σ, hσ⟩` from `hc.exists_algEquiv`. Use `⟨σ, fun t ht => ?_⟩` and prove the remaining obligations.

Take `⟨i, -, rfl⟩` from `hξ.eq_pow_of_pow_eq_one ht`. Rewrite using `[map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem UpperTheory.Mu.exists_aut_pow (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) (hM : M ≠ 0)
    (a : ℕ) (ha : a.Coprime M) : ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ t : Ω, t ^ M = 1 → σ t = t ^ a := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hξ' : IsPrimitiveRoot (ξ ^ a) M := hξ.pow_of_coprime a ha
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  have hc : IsConjRoot ℚ (ξ ^ a) ξ := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hξ hpos, ← Polynomial.cyclotomic_eq_minpoly_rat hξ' hpos]
  obtain ⟨σ, hσ⟩ := hc.exists_algEquiv
  refine ⟨σ, fun t ht => ?_⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one ht
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]`.
-/
private theorem UpperTheory.Mu.dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

/- English proof (translation)
Introduce `l hl Ω _ _ _ N hN ζ hζ v u huv k`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `hp : l.Prime` using `hl.out`. Use `set s := N.factorization l with hs`. Use `set N' := N / l ^ s with hN'`.

Establish `hNN : l ^ s * N' = N` using `Nat.ordProj_mul_ordCompl_eq_self N l`. Establish `hcop : Nat.Coprime l N'` using `Nat.coprime_ordCompl hp hN`. Establish `hcP : Nat.Coprime N' (l ^ (s + k))` using `hcop.symm.pow_right _`. Establish `hN'0 : N' ≠ 0`. Introduce `h`.

Rewrite `hNN` using `[h, mul_zero]`. Conclude with `hN hNN.symm`. Establish `hP0 : l ^ (s + k) ≠ 0` using `pow_ne_zero _ hp.ne_zero`. Use `haveI : NeZero (l ^ (s + k)) := ⟨hP0⟩`. Take `⟨a, ha1, ha2⟩` from `Nat.chineseRemainder hcP (v : ZMod N).val (PadicInt.toZModPow (s + k) (u : ℤ_[l])).val`.

Establish `hau : ((a : ℕ) : ZMod (l ^ (s + k))) = PadicInt.toZModPow (s + k) (u : ℤ_[l])`. Rewrite using `[(ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val]`. Establish `hcoP : a.Coprime (l ^ (s + k))`. Rewrite using `[← ZMod.isUnit_iff_coprime, hau]`. Conclude with `(Units.isUnit u).map _`.

Establish `hcoN' : a.Coprime N'`. Establish `h1 : (v : ZMod N).val.Coprime N'` using `(ZMod.val_coe_unit_coprime v).coprime_dvd_right (Dvd.intro_left _ hNN)`. Unfold `Nat.Coprime at h1 ⊢`. Rewrite using `[ha1.gcd_eq, h1]`. Establish `hdu : (l : ℤ_[l]) ^ (s + k) ∣ (u : ℤ_[l]) - (a : ℤ_[l])`.

Rewrite using `[UpperTheory.Mu.dvd_sub_iff, map_natCast, hau]`. Establish `has : a ≡ (v : ZMod N).val [MOD l ^ s]`. Establish `h1 : (l : ℤ_[l]) ^ s ∣ (a : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l])`. Establish `h2` using `dvd_sub huv ((pow_dvd_pow _ (Nat.le_add_right s k)).trans hdu)`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[UpperTheory.Mu.dvd_sub_iff, map_natCast, map_natCast]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).1 h1`. Establish `haN : a ≡ (v : ZMod N).val [MOD N]`. Use `(Nat.modEq_and_modEq_iff_modEq_mul (hcop.pow_left s)).1 ⟨has, ha1⟩` as an intermediate fact.

Rewrite `this` using `[hNN]`. Then use the resulting hypothesis. Take `⟨σ, hσ⟩` from `UpperTheory.Mu.exists_aut_pow Ω (N' * l ^ (s + k)) (mul_ne_zero hN'0 hP0) a (Nat.Coprime.mul_right hcoN' hcoP)`. Use `⟨σ, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ζ ^ (N' * l ^ (s + k)) = 1`. Establish `: N' * l ^ (s + k) = N * l ^ k` using `by rw [← hNN]; ring`.

Rewrite using `[this, pow_mul, hζ.pow_eq_one, one_pow]`. Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hN, hζ.pow_eq_one⟩`. Rewrite using `[hσ ζ h1, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]`. Conclude with `haN`. Use `(pow_dvd_pow _ (Nat.le_add_left k s)).trans ?_` and prove the remaining obligations.

Rewrite using `[UpperTheory.Mu.dvd_sub_iff, ← hau]`. Take `⟨η, hη⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (s + k))`. Use `haveI (i : ℕ) : HasEnoughRootsOfUnity Ω (l ^ i) := by haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩ infer_instance`. Establish `h1` using `cyclotomicCharacter.spec l (n := s + k) (σ : Ω ≃+* Ω) η hη.pow_eq_one`. Establish `h2 : σ η = η ^ a` using `hσ η (by rw [mul_comm, pow_mul, hη.pow_eq_one, one_pow])`.

Establish `h3 : η ^ (PadicInt.toZModPow (s + k) ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l])).val = η ^ a` using `h1.symm.trans h2`. Establish `hfin : IsOfFinOrder η` using `isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hP0, hη.pow_eq_one⟩`. Rewrite `h3` using `[hfin.pow_eq_pow_iff_modEq, ← hη.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]`. Conclude with `h3`.
-/
theorem UpperTheory.Mu.autApprox :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ), N ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (v : (ZMod N)ˣ) (u : ℤ_[l]ˣ), (l : ℤ_[l]) ^ N.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ (v : ZMod N).val ∧ (l : ℤ_[l]) ^ k ∣ ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro l hl Ω _ _ _ N hN ζ hζ v u huv k
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp : l.Prime := hl.out
  set s := N.factorization l with hs
  set N' := N / l ^ s with hN'
  have hNN : l ^ s * N' = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hcop : Nat.Coprime l N' := Nat.coprime_ordCompl hp hN
  have hcP : Nat.Coprime N' (l ^ (s + k)) := hcop.symm.pow_right _
  have hN'0 : N' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNN
    exact hN hNN.symm
  have hP0 : l ^ (s + k) ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (l ^ (s + k)) := ⟨hP0⟩
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcP (v : ZMod N).val
    (PadicInt.toZModPow (s + k) (u : ℤ_[l])).val
  have hau : ((a : ℕ) : ZMod (l ^ (s + k))) = PadicInt.toZModPow (s + k) (u : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val]
  have hcoP : a.Coprime (l ^ (s + k)) := by
    rw [← ZMod.isUnit_iff_coprime, hau]
    exact (Units.isUnit u).map _
  have hcoN' : a.Coprime N' := by
    have h1 : (v : ZMod N).val.Coprime N' :=
      (ZMod.val_coe_unit_coprime v).coprime_dvd_right (Dvd.intro_left _ hNN)
    unfold Nat.Coprime at h1 ⊢
    rw [ha1.gcd_eq, h1]
  have hdu : (l : ℤ_[l]) ^ (s + k) ∣ (u : ℤ_[l]) - (a : ℤ_[l]) := by
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, hau]
  have has : a ≡ (v : ZMod N).val [MOD l ^ s] := by
    have h1 : (l : ℤ_[l]) ^ s ∣ (a : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) := by
      have h2 := dvd_sub huv ((pow_dvd_pow _ (Nat.le_add_right s k)).trans hdu)
      convert h2 using 1
      ring
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, map_natCast] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  have haN : a ≡ (v : ZMod N).val [MOD N] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul (hcop.pow_left s)).1 ⟨has, ha1⟩
    rwa [hNN] at this
  obtain ⟨σ, hσ⟩ := UpperTheory.Mu.exists_aut_pow Ω (N' * l ^ (s + k)) (mul_ne_zero hN'0 hP0) a
    (Nat.Coprime.mul_right hcoN' hcoP)
  refine ⟨σ, ?_, ?_⟩
  · have h1 : ζ ^ (N' * l ^ (s + k)) = 1 := by
      have : N' * l ^ (s + k) = N * l ^ k := by rw [← hNN]; ring
      rw [this, pow_mul, hζ.pow_eq_one, one_pow]
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hN, hζ.pow_eq_one⟩
    rw [hσ ζ h1, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
    exact haN
  · refine (pow_dvd_pow _ (Nat.le_add_left k s)).trans ?_
    rw [UpperTheory.Mu.dvd_sub_iff, ← hau]
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (s + k))
    haveI (i : ℕ) : HasEnoughRootsOfUnity Ω (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    have h1 := cyclotomicCharacter.spec l (n := s + k) (σ : Ω ≃+* Ω) η hη.pow_eq_one
    have h2 : σ η = η ^ a := hσ η (by rw [mul_comm, pow_mul, hη.pow_eq_one, one_pow])
    have h3 : η ^ (PadicInt.toZModPow (s + k) ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l])).val = η ^ a :=
      h1.symm.trans h2
    have hfin : IsOfFinOrder η := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hP0, hη.pow_eq_one⟩
    rw [hfin.pow_eq_pow_iff_modEq, ← hη.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h3
    exact h3
