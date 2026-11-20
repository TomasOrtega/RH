import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.EpsDec

/- English proof (translation)
Rewrite using `[ZMod.natCast_eq_natCast_iff' a b N]`. Rewrite `h` using `[pow_eq_pow_mod a hζ.pow_eq_one, pow_eq_pow_mod b hζ.pow_eq_one]`. Conclude with `hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) h`.
-/
theorem natCast_eq_of_pow_eq {M : Type} [CommMonoid M] {ζ : M} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod N) = b := by
  rw [ZMod.natCast_eq_natCast_iff' a b N]
  rw [pow_eq_pow_mod a hζ.pow_eq_one, pow_eq_pow_mod b hζ.pow_eq_one] at h
  exact hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) h

/- English proof (translation)
Introduce `l _ Ω _ _ _ n w B hB hdiv hn σ hσ`. Establish `hl : l.Prime` using `Fact.out`. Establish `hl2` using `hl.two_le`. Use `set p := normV w with hpdef`. Establish `hp : p.Prime` using `GlobalTheory.Ord2.PrimeChar.normV_prime w`.

Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hA : B.valuation (p : Ω) < 1` using `GlobalTheory.Ord2.PrimeChar.val_normV_lt_one hB`. Establish `hpl : p ≠ l`. Introduce `e`. Establish `h1 : l ∣ p - 1` using `(dvd_pow_self l (by omega)).trans hdiv`.

Rewrite `h1` using `[e]`. Establish `h2` using `Nat.le_of_dvd (by omega) h1`. Use linear arithmetic over natural numbers and integers. Establish `hcop : (l ^ n).Coprime p` using `Nat.Coprime.pow_left n ((Nat.coprime_primes hl hp).2 hpl.symm)`. Take `⟨k, hk⟩` from `UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω p B hA (l ^ n) hcop σ hσ`.

Establish `hp1 : (p : ZMod (l ^ n)) = 1`. Establish `h1 : 1 ≤ p` using `hp.one_lt.le`. Establish `: ((p - 1 : ℕ) : ZMod (l ^ n)) = 0` using `(CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n) _).2 hdiv`. Rewrite `this` using `[Nat.cast_sub h1, Nat.cast_one, sub_eq_zero]`. Conclude with `this`.

Establish `hIAC : IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Establish `hN0 : l ^ n ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)`.

Establish `hspec` using `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ.pow_eq_one`. Use `set c : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc`. Establish `hσζ : σ ζ = ζ ^ (PadicInt.toZModPow n c).val` using `hspec`. Establish `hζp : ζ ^ (p ^ k) = ζ ^ 1`. Rewrite using `[pow_eq_pow_mod (p ^ k) hζ.pow_eq_one, pow_eq_pow_mod 1 hζ.pow_eq_one]`.

Use `congr 1`. Rewrite using `[← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hp1, one_pow, Nat.cast_one]`. Establish `hm : PadicInt.toZModPow n c = 1`. Establish `h1 : ζ ^ (PadicInt.toZModPow n c).val = ζ ^ 1` using `by rw [← hσζ, hk ζ hζ.pow_eq_one, hζp]`. Establish `h2` using `natCast_eq_of_pow_eq hζ hN0 h1`.

Rewrite `h2` using `[ZMod.natCast_zmod_val, Nat.cast_one]`. Then use the resulting hypothesis. Establish `hker : c - 1 ∈ Ideal.span {((l : ℤ_[l])) ^ n}`. Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hm, map_one, sub_self]`. Establish `hnorm` using `(PadicInt.norm_le_pow_iff_mem_span_pow (c - 1) n).2 hker`. Establish `e1 : eps l σ - 1 = algebraMap ℚ_[l] (Qbar l) ((c : ℚ_[l]) - 1)`.

Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Unfold `Cg`. Rewrite using `[e1, norm_algebraMap', norm_pow]`. Establish `e2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l])` using `by simp`.

Rewrite using `[e2, norm_algebraMap', Padic.norm_p]`. Establish `e3 : ‖(c : ℚ_[l]) - 1‖ = ‖c - 1‖`. Rewrite using `[PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]`. Rewrite using `[e3]`. Use `hnorm.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`.
-/
theorem eps_dec_cong : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl)
    (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n →
    ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  intro l _ Ω _ _ _ n w B hB hdiv hn σ hσ
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  set p := normV w with hpdef
  have hp : p.Prime := GlobalTheory.Ord2.PrimeChar.normV_prime w
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : B.valuation (p : Ω) < 1 := GlobalTheory.Ord2.PrimeChar.val_normV_lt_one hB
  have hpl : p ≠ l := by
    intro e
    have h1 : l ∣ p - 1 := (dvd_pow_self l (by omega)).trans hdiv
    rw [e] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    omega
  have hcop : (l ^ n).Coprime p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes hl hp).2 hpl.symm)
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω p B hA (l ^ n) hcop σ hσ
  have hp1 : (p : ZMod (l ^ n)) = 1 := by
    have h1 : 1 ≤ p := hp.one_lt.le
    have : ((p - 1 : ℕ) : ZMod (l ^ n)) = 0 := (CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n) _).2 hdiv
    rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hIAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow n c).val := hspec
  have hζp : ζ ^ (p ^ k) = ζ ^ 1 := by
    rw [pow_eq_pow_mod (p ^ k) hζ.pow_eq_one, pow_eq_pow_mod 1 hζ.pow_eq_one]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hp1, one_pow, Nat.cast_one]
  have hm : PadicInt.toZModPow n c = 1 := by
    have h1 : ζ ^ (PadicInt.toZModPow n c).val = ζ ^ 1 := by rw [← hσζ, hk ζ hζ.pow_eq_one, hζp]
    have h2 := natCast_eq_of_pow_eq hζ hN0 h1
    rwa [ZMod.natCast_zmod_val, Nat.cast_one] at h2
  have hker : c - 1 ∈ Ideal.span {((l : ℤ_[l])) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hm, map_one, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow (c - 1) n).2 hker
  have e1 : eps l σ - 1 = algebraMap ℚ_[l] (Qbar l) ((c : ℚ_[l]) - 1) := by
    rw [map_sub, map_one]; rfl
  unfold Cg
  rw [e1, norm_algebraMap', norm_pow]
  have e2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [e2, norm_algebraMap', Padic.norm_p]
  have e3 : ‖(c : ℚ_[l]) - 1‖ = ‖c - 1‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
  rw [e3]
  refine hnorm.trans (le_of_eq ?_)
  rw [zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.Ord2.EpsDec
