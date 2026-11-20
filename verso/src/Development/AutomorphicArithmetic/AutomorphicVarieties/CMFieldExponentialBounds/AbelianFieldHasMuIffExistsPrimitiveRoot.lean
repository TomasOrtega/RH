import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

/- English proof (translation)
Take `⟨v, hv⟩` from `ZMod.unitsMap_surjective h (ZMod.unitOfCoprime b hb)`. Use `⟨(v : ZMod N).val, ZMod.val_coe_unit_coprime v, ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ← ZMod.unitsMap_val h v, hv]`. Simplify using the standard rewrite rules.
-/
private theorem lift_coprime {n N b : ℕ} [NeZero N] (h : n ∣ N) (hb : b.Coprime n) :
    ∃ a : ℕ, a.Coprime N ∧ a ≡ b [MOD n] := by
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime b hb)
  refine ⟨(v : ZMod N).val, ZMod.val_coe_unit_coprime v, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ← ZMod.unitsMap_val h v, hv]
  simp

/- English proof (translation)
Use `haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩`. Use `haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ`. Establish `hirr` using `Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)`. Use `set ζ := IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)`.

Use `set τ := (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).symm (ZMod.unitOfCoprime a ha) with hτdef`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Establish `hτ : hζ.autToPow ℚ τ = ZMod.unitOfCoprime a ha` using `(IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).apply_symm_apply (ZMod.unitOfCoprime a ha)`. Establish `hτζ : τ ζ = ζ ^ a`. Rewrite using `[← hζ.autToPow_spec ℚ τ, hτ, ZMod.coe_unitOfCoprime, ZMod.val_natCast]`.

Use `conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hx`. Rewrite using `[map_pow, hτζ, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem exists_aut {N a : ℕ} [NeZero N] (ha : a.Coprime N) :
    ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ, ∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  set ζ := IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)
  set τ := (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).symm (ZMod.unitOfCoprime a ha) with hτdef
  refine ⟨τ, ?_⟩
  have hτ : hζ.autToPow ℚ τ = ZMod.unitOfCoprime a ha :=
    (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).apply_symm_apply (ZMod.unitOfCoprime a ha)
  have hτζ : τ ζ = ζ ^ a := by
    rw [← hζ.autToPow_spec ℚ τ, hτ, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  intro x hx
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hτζ, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Take `⟨u, hu, e⟩` from `hb`. Conclude with `⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩`.
-/
private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `A l hl hl2 L _ _ hL`. Take `⟨N, hN, j, ζ, hdvd, hζ, hfix⟩` from `hL`. Use `haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩`. Use `haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ`. Establish `hl3 : 3 ≤ l`.

Use `hl.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hker1 : A.ker 1` using `⟨1, A.H.one_mem, by simp⟩`. Establish `haut : ∀ a : ℕ, a.Coprime N → ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ, (∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a) ∧ ((∀ y : L, τ (j y) = j y) ↔ A.ker a)`. Introduce `a ha`.

Take `⟨τ, hτ⟩` from `exists_aut ha`. Conclude with `⟨τ, hτ, hfix τ a (hτ ζ hζ.pow_eq_one)⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hlm, hmu⟩`. Establish `hlN : l ∣ N` using `hlm.trans hdvd`.

Establish `hz : IsPrimitiveRoot (ζ ^ (N / l)) l` using `IsPrimitiveRoot.pow (NeZero.pos N) hζ (by rw [Nat.div_mul_cancel hlN])`. Establish `hord : orderOf (ζ ^ (N / l)) = l` using `hz.eq_orderOf.symm`. Establish `hfin : IsOfFinOrder (ζ ^ (N / l))` using `isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hz.pow_eq_one⟩`. Establish `hmem : ζ ^ (N / l) ∈ j.fieldRange` using `by haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)`. Rewrite using `[← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]`.

Introduce `τ hτ`. Rewrite `hτ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `hτj : ∀ y : L, τ (j y) = j y` using `fun y => hτ _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)`. Establish `hτN : (τ ζ) ^ N = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`. Take `⟨a, -, ha⟩` from `hζ.eq_pow_of_pow_eq_one hτN`.

Establish `hka : A.ker a` using `(hfix τ a ha.symm).1 hτj`. Establish `ha1 : a ≡ 1 [MOD l]` using `hmu a hka`. Establish `hpow : (ζ ^ (N / l)) ^ a = (ζ ^ (N / l)) ^ 1`. Rewrite using `[hfin.pow_eq_pow_iff_modEq, hord]`. Conclude with `ha1`.

Rewrite using `[map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]`. Take `⟨w, hw⟩ : ∃ w : L, j w = ζ ^ (N / l)` from `AlgHom.mem_fieldRange.1 hmem`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[← hw]`. Conclude with `(IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).1 hz`.

Introduce and unpack `⟨z, hz⟩`. Establish `hw : IsPrimitiveRoot (j z) l` using `hz.map_of_injective j.toRingHom.injective`. Establish `hord : orderOf (j z) = l` using `hw.eq_orderOf.symm`. Establish `hfin : IsOfFinOrder (j z)` using `isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hw.pow_eq_one⟩`. Establish `hlN : l ∣ N`.

Assume the negation of the conclusion as `hnd`. Establish `hcop : Nat.Coprime N l` using `Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)`. Establish `hirr` using `Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos (NeZero.pos N) hl.pos)`. Establish `h1` using `IsPrimitiveRoot.lcm_totient_le_finrank hζ hw hirr`. Rewrite `h1` using `[IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)), Nat.Coprime.lcm_eq_mul hcop, Nat.totient_mul hcop, Nat.totient_prime hl]`.

Establish `hpos : 0 < N.totient` using `Nat.totient_pos.2 (NeZero.pos N)`. Establish `h2 : 2 ≤ l - 1` using `by omega`. Use the polynomial consequences of the given equalities and inequalities. Establish `hwN : (j z) ^ N = 1`. Take `⟨k, hk⟩` from `hlN`.

Establish `e1 : (j z) ^ N = ((j z) ^ l) ^ k` using `by rw [← pow_mul, ← hk]`. Rewrite using `[e1, hw.pow_eq_one, one_pow]`. Establish `key : ∀ a : ℕ, a.Coprime N → A.ker a → a ≡ 1 [MOD l]`. Introduce `a ha hka`. Take `⟨τ, hτ, hiff⟩` from `haut a ha`.

Establish `h1` using `hiff.2 hka z`. Rewrite `h1` using `[hτ _ hwN]`. Establish `h2 : (j z) ^ a = (j z) ^ 1` using `by rw [pow_one]; exact h1`. Rewrite `h2` using `[hfin.pow_eq_pow_iff_modEq, hord]`. Conclude with `h2`.

Establish `hlm : l ∣ A.m`. Assume the negation of the conclusion as `hnd`. Establish `hcop : Nat.Coprime A.m l` using `Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)`. Take `⟨b, hb1, hb2⟩` from `Nat.chineseRemainder hcop 1 2`. Establish `hbm : Nat.Coprime b A.m`.

Unfold `Nat.Coprime`. Rewrite using `[hb1.gcd_eq, Nat.gcd_one_left]`. Establish `h2l : Nat.Coprime 2 l` using `(Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm hl2)`. Establish `hbl : Nat.Coprime b l`. Unfold `Nat.Coprime`.

Rewrite using `[hb2.gcd_eq]`. Conclude with `h2l`. Establish `hbcop : Nat.Coprime b (A.m * l)` using `Nat.Coprime.mul_right hbm hbl`. Establish `hmlN : A.m * l ∣ N` using `Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd hlN`. Take `⟨a, ha, hab⟩` from `lift_coprime hmlN hbcop`.

Establish `ham : a ≡ 1 [MOD A.m]` using `(Nat.ModEq.of_mul_right l hab).trans hb1`. Establish `hal : a ≡ 2 [MOD l]` using `(Nat.ModEq.of_mul_left A.m hab).trans hb2`. Establish `hka : A.ker a` using `ker_congr A ham hker1`. Establish `h21 : 2 ≡ 1 [MOD l]` using `hal.symm.trans (key a ha hka)`. Unfold `Nat.ModEq at h21`.

Rewrite `h21` using `[Nat.mod_eq_of_lt (by omega : 2 < l), Nat.mod_eq_of_lt (by omega : 1 < l)]`. Use linear arithmetic over natural numbers and integers. Use `⟨hlm, ?_⟩` and prove the remaining obligations. Introduce `a hka`. Establish `hacop : a.Coprime A.m`.

Take `⟨u, -, hu⟩` from `hka`. Conclude with `(ZMod.isUnit_iff_coprime a A.m).1 ⟨u, hu⟩`. Take `⟨a', ha', ha'a⟩` from `lift_coprime hdvd hacop`. Establish `hka'` using `ker_congr A ha'a hka`. Conclude with `(Nat.ModEq.of_dvd hlm ha'a).symm.trans (key a' ha' hka')`.
-/
theorem UpperTheory.V.abelianField_hasMu_iff_exists_primitiveRoot :
    ∀ (A : AbF) (l : ℕ), l.Prime → l ≠ 2 → ∀ (L : Type) [Field L] [NumberField L], IsAbField A L →
      (A.HasMu l ↔ ∃ z : L, IsPrimitiveRoot z l) := by
  intro A l hl hl2 L _ _ hL
  obtain ⟨N, hN, j, ζ, hdvd, hζ, hfix⟩ := hL
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  have hker1 : A.ker 1 := ⟨1, A.H.one_mem, by simp⟩
  have haut : ∀ a : ℕ, a.Coprime N → ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      (∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a) ∧ ((∀ y : L, τ (j y) = j y) ↔ A.ker a) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := exists_aut ha
    exact ⟨τ, hτ, hfix τ a (hτ ζ hζ.pow_eq_one)⟩
  constructor
  · rintro ⟨hlm, hmu⟩
    have hlN : l ∣ N := hlm.trans hdvd
    have hz : IsPrimitiveRoot (ζ ^ (N / l)) l :=
      IsPrimitiveRoot.pow (NeZero.pos N) hζ (by rw [Nat.div_mul_cancel hlN])
    have hord : orderOf (ζ ^ (N / l)) = l := hz.eq_orderOf.symm
    have hfin : IsOfFinOrder (ζ ^ (N / l)) := isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hz.pow_eq_one⟩
    have hmem : ζ ^ (N / l) ∈ j.fieldRange := by
      haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
      rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have hτj : ∀ y : L, τ (j y) = j y := fun y => hτ _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
      have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
      obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hτN
      have hka : A.ker a := (hfix τ a ha.symm).1 hτj
      have ha1 : a ≡ 1 [MOD l] := hmu a hka
      have hpow : (ζ ^ (N / l)) ^ a = (ζ ^ (N / l)) ^ 1 := by
        rw [hfin.pow_eq_pow_iff_modEq, hord]
        exact ha1
      rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
    obtain ⟨w, hw⟩ : ∃ w : L, j w = ζ ^ (N / l) := AlgHom.mem_fieldRange.1 hmem
    refine ⟨w, ?_⟩
    rw [← hw] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).1 hz
  · rintro ⟨z, hz⟩
    have hw : IsPrimitiveRoot (j z) l := hz.map_of_injective j.toRingHom.injective
    have hord : orderOf (j z) = l := hw.eq_orderOf.symm
    have hfin : IsOfFinOrder (j z) := isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hw.pow_eq_one⟩
    have hlN : l ∣ N := by
      by_contra hnd
      have hcop : Nat.Coprime N l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      have hirr := Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos (NeZero.pos N) hl.pos)
      have h1 := IsPrimitiveRoot.lcm_totient_le_finrank hζ hw hirr
      rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)),
        Nat.Coprime.lcm_eq_mul hcop, Nat.totient_mul hcop, Nat.totient_prime hl] at h1
      have hpos : 0 < N.totient := Nat.totient_pos.2 (NeZero.pos N)
      have h2 : 2 ≤ l - 1 := by omega
      nlinarith
    have hwN : (j z) ^ N = 1 := by
      obtain ⟨k, hk⟩ := hlN
      have e1 : (j z) ^ N = ((j z) ^ l) ^ k := by rw [← pow_mul, ← hk]
      rw [e1, hw.pow_eq_one, one_pow]
    have key : ∀ a : ℕ, a.Coprime N → A.ker a → a ≡ 1 [MOD l] := by
      intro a ha hka
      obtain ⟨τ, hτ, hiff⟩ := haut a ha
      have h1 := hiff.2 hka z
      rw [hτ _ hwN] at h1
      have h2 : (j z) ^ a = (j z) ^ 1 := by rw [pow_one]; exact h1
      rw [hfin.pow_eq_pow_iff_modEq, hord] at h2
      exact h2
    have hlm : l ∣ A.m := by
      by_contra hnd
      have hcop : Nat.Coprime A.m l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop 1 2
      have hbm : Nat.Coprime b A.m := by
        unfold Nat.Coprime
        rw [hb1.gcd_eq, Nat.gcd_one_left]
      have h2l : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm hl2)
      have hbl : Nat.Coprime b l := by
        unfold Nat.Coprime
        rw [hb2.gcd_eq]
        exact h2l
      have hbcop : Nat.Coprime b (A.m * l) := Nat.Coprime.mul_right hbm hbl
      have hmlN : A.m * l ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd hlN
      obtain ⟨a, ha, hab⟩ := lift_coprime hmlN hbcop
      have ham : a ≡ 1 [MOD A.m] := (Nat.ModEq.of_mul_right l hab).trans hb1
      have hal : a ≡ 2 [MOD l] := (Nat.ModEq.of_mul_left A.m hab).trans hb2
      have hka : A.ker a := ker_congr A ham hker1
      have h21 : 2 ≡ 1 [MOD l] := hal.symm.trans (key a ha hka)
      unfold Nat.ModEq at h21
      rw [Nat.mod_eq_of_lt (by omega : 2 < l), Nat.mod_eq_of_lt (by omega : 1 < l)] at h21
      omega
    refine ⟨hlm, ?_⟩
    intro a hka
    have hacop : a.Coprime A.m := by
      obtain ⟨u, -, hu⟩ := hka
      exact (ZMod.isUnit_iff_coprime a A.m).1 ⟨u, hu⟩
    obtain ⟨a', ha', ha'a⟩ := lift_coprime hdvd hacop
    have hka' := ker_congr A ha'a hka
    exact (Nat.ModEq.of_dvd hlm ha'a).symm.trans (key a' ha' hka')
