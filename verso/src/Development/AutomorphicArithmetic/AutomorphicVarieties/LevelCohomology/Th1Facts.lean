import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

/- English proof (translation)
Establish `hm0 : Nat.lcm 4 n ≠ 0` using `Nat.lcm_ne_zero (by norm_num) hn.ne'`. Use `haveI : NeZero (Nat.lcm 4 n) := ⟨hm0⟩`. Establish `h2 : Nat.Coprime l 2` using `(Nat.coprime_primes hl Nat.prime_two).mpr hl2`. Establish `h4 : Nat.Coprime l 4`. Establish `e` using `Nat.Coprime.pow_right 2 h2`.

Evaluate the numerical expressions using `at e`. Conclude with `e`. Establish `hn' : Nat.Coprime l n` using `(Nat.Prime.coprime_iff_not_dvd hl).mpr hnd`. Establish `hc : Nat.Coprime l (Nat.lcm 4 n)` using `Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul 4 n) (Nat.Coprime.mul_right h4 hn')`. Establish `hue : ((ZMod.unitOfCoprime l hc : (ZMod (Nat.lcm 4 n))ˣ) : ZMod (Nat.lcm 4 n)) = (l : ZMod (Nat.lcm 4 n))` using `ZMod.coe_unitOfCoprime l hc`.

Establish `hord : orderOf (l : ZMod (Nat.lcm 4 n)) = orderOf (ZMod.unitOfCoprime l hc)`. Rewrite using `[← hue, orderOf_units]`. Use `⟨by rw [hord]; exact orderOf_pos _, ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow, pow_orderOf_eq_one, Nat.cast_one, sub_self]`.
-/
private theorem arith (l n : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hn : 0 < n) (hnd : ¬ l ∣ n) :
    0 < orderOf (l : ZMod (Nat.lcm 4 n)) ∧ Nat.lcm 4 n ∣ l ^ orderOf (l : ZMod (Nat.lcm 4 n)) - 1 := by
  have hm0 : Nat.lcm 4 n ≠ 0 := Nat.lcm_ne_zero (by norm_num) hn.ne'
  haveI : NeZero (Nat.lcm 4 n) := ⟨hm0⟩
  have h2 : Nat.Coprime l 2 := (Nat.coprime_primes hl Nat.prime_two).mpr hl2
  have h4 : Nat.Coprime l 4 := by
    have e := Nat.Coprime.pow_right 2 h2
    norm_num at e
    exact e
  have hn' : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hnd
  have hc : Nat.Coprime l (Nat.lcm 4 n) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul 4 n) (Nat.Coprime.mul_right h4 hn')
  have hue : ((ZMod.unitOfCoprime l hc : (ZMod (Nat.lcm 4 n))ˣ) : ZMod (Nat.lcm 4 n)) = (l : ZMod (Nat.lcm 4 n)) :=
    ZMod.coe_unitOfCoprime l hc
  have hord : orderOf (l : ZMod (Nat.lcm 4 n)) = orderOf (ZMod.unitOfCoprime l hc) := by
    rw [← hue, orderOf_units]
  refine ⟨by rw [hord]; exact orderOf_pos _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow,
    pow_orderOf_eq_one, Nat.cast_one, sub_self]

/- English proof (translation)
Introduce `O _ _ N _ ψ l hl hl2`. Take `⟨-, hmul, hone, hinv, hpow, hidem, -, -⟩` from `compAlg O N 2 Nat.prime_two`. Establish `hfin : 0 < orderOf ψ` using `orderOf_pos ψ`. Take `⟨hoK, -, hndvd, -, -, -, -⟩` from `partOrd _ l hl ψ hfin`. Establish `hkapOrd : orderOf (kap l ψ) = l ^ (orderOf ψ).factorization l` using `hoK`.

Establish `hc2k : comp 2 (kap l ψ) = 1`. Take `⟨k, hk⟩` from `(compOrd O N (kap l ψ) 2 Nat.prime_two).2.1`. Establish `hd : orderOf (comp 2 (kap l ψ)) ∣ orderOf (kap l ψ)` using `(hidem (kap l ψ)).2.1`. Rewrite `hd` using `[hk, hkapOrd]`. Establish `hk0 : k = 0`.

Assume the negation of the conclusion as `hk0`. Establish `h2 : 2 ∣ l ^ (orderOf ψ).factorization l` using `dvd_trans (dvd_pow_self 2 hk0) hd`. Establish `e` using `(Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp (Nat.prime_two.dvd_of_dvd_pow h2)`. Conclude with `hl2 e.symm`. Rewrite `hk` using `[hk0, pow_zero]`.

Conclude with `orderOf_eq_one_iff.mp hk`. Establish `hψ : th0 l ψ * kap l ψ = ψ` using `dirichletPrimeToLPart_mul_lPowerPart l ψ`. Establish `hc2 : comp 2 ψ = comp 2 (th0 l ψ)` using `by conv_lhs => rw [← hψ]`. Rewrite using `[hmul, hc2k, mul_one]`. Establish `hth1c : comp 2 (th1 l ψ) = 1` using `by show comp 2 (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) = 1`.

Rewrite using `[hmul, hinv, (hidem _).1, mul_inv_cancel]`. Establish `hth1pow : th1 l ψ ^ orderOf (th0 l ψ) = 1` using `by show (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) ^ orderOf (th0 l ψ) = 1`. Rewrite using `[mul_pow, inv_pow, ← hpow, pow_orderOf_eq_one, hone, inv_one, mul_one]`. Establish `hdvd1 : orderOf (th1 l ψ) ∣ orderOf (th0 l ψ)` using `orderOf_dvd_of_pow_eq_one hth1pow`. Establish `hnd1 : ¬ l ∣ orderOf (th1 l ψ)` using `fun h => hndvd (dvd_trans h hdvd1)`.

Establish `hpos1 : 0 < orderOf (th1 l ψ)` using `orderOf_pos _`. Take `⟨hf0, hdiv⟩` from `arith l (orderOf (th1 l ψ)) hl hl2 hpos1 hnd1`. Establish `hf : f0 l ψ = orderOf ((l : ZMod (Nat.lcm 4 (orderOf (th1 l ψ)))))` using `rfl`. Use `⟨?_, ⟨(orderOf ψ).factorization l, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ψ = comp 2 ψ * (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) * kap l ψ`.

Rewrite using `[hc2, mul_comm (comp 2 (th0 l ψ)) (th0 l ψ * _), inv_mul_cancel_right]`. Conclude with `hψ.symm`. Rewrite using `[← hkapOrd]`. Conclude with `pow_orderOf_eq_one _`. Establish `h1 : comp 2 (th1 l ψ ^ 2) = 1`.

Rewrite using `[hpow, hth1c, one_pow]`. Establish `h` using `((compCond O N (th1 l ψ ^ 2) 2 Nat.prime_two).2.1).mp h1`. Conclude with `Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)`. Rewrite using `[hf]`. Conclude with `hf0`.

Rewrite using `[hf]`. Conclude with `dvd_trans (Nat.dvd_lcm_left 4 _) hdiv`. Rewrite using `[hf]`. Conclude with `orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (Nat.dvd_lcm_right 4 _) hdiv)`. Establish `e` using `Nat.sub_dvd_pow_sub_pow l 1 (f0 l ψ)`.

Rewrite `e` using `[one_pow]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.X.th1Facts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) (l : ℕ), l.Prime → l ≠ 2 → ψ = psi2 ψ * th1 l ψ * kap l ψ ∧ (∃ s, kap l ψ ^ l ^ s = 1) ∧ Odd (th1 l ψ ^ 2).conductor ∧ 0 < f0 l ψ ∧ 4 ∣ l ^ f0 l ψ - 1 ∧ th1 l ψ ^ (l ^ f0 l ψ - 1) = 1 ∧ l - 1 ∣ l ^ f0 l ψ - 1 := by
  intro O _ _ N _ ψ l hl hl2
  obtain ⟨-, hmul, hone, hinv, hpow, hidem, -, -⟩ := compAlg O N 2 Nat.prime_two
  have hfin : 0 < orderOf ψ := orderOf_pos ψ
  obtain ⟨hoK, -, hndvd, -, -, -, -⟩ := partOrd _ l hl ψ hfin
  have hkapOrd : orderOf (kap l ψ) = l ^ (orderOf ψ).factorization l := hoK
  have hc2k : comp 2 (kap l ψ) = 1 := by
    obtain ⟨k, hk⟩ := (compOrd O N (kap l ψ) 2 Nat.prime_two).2.1
    have hd : orderOf (comp 2 (kap l ψ)) ∣ orderOf (kap l ψ) := (hidem (kap l ψ)).2.1
    rw [hk, hkapOrd] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ l ^ (orderOf ψ).factorization l := dvd_trans (dvd_pow_self 2 hk0) hd
      have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp (Nat.prime_two.dvd_of_dvd_pow h2)
      exact hl2 e.symm
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hψ : th0 l ψ * kap l ψ = ψ := dirichletPrimeToLPart_mul_lPowerPart l ψ
  have hc2 : comp 2 ψ = comp 2 (th0 l ψ) := by
    conv_lhs => rw [← hψ]
    rw [hmul, hc2k, mul_one]
  have hth1c : comp 2 (th1 l ψ) = 1 := by
    show comp 2 (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) = 1
    rw [hmul, hinv, (hidem _).1, mul_inv_cancel]
  have hth1pow : th1 l ψ ^ orderOf (th0 l ψ) = 1 := by
    show (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) ^ orderOf (th0 l ψ) = 1
    rw [mul_pow, inv_pow, ← hpow, pow_orderOf_eq_one, hone, inv_one, mul_one]
  have hdvd1 : orderOf (th1 l ψ) ∣ orderOf (th0 l ψ) := orderOf_dvd_of_pow_eq_one hth1pow
  have hnd1 : ¬ l ∣ orderOf (th1 l ψ) := fun h => hndvd (dvd_trans h hdvd1)
  have hpos1 : 0 < orderOf (th1 l ψ) := orderOf_pos _
  obtain ⟨hf0, hdiv⟩ := arith l (orderOf (th1 l ψ)) hl hl2 hpos1 hnd1
  have hf : f0 l ψ = orderOf ((l : ZMod (Nat.lcm 4 (orderOf (th1 l ψ))))) := rfl
  refine ⟨?_, ⟨(orderOf ψ).factorization l, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ψ = comp 2 ψ * (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) * kap l ψ
    rw [hc2, mul_comm (comp 2 (th0 l ψ)) (th0 l ψ * _), inv_mul_cancel_right]
    exact hψ.symm
  · rw [← hkapOrd]
    exact pow_orderOf_eq_one _
  · have h1 : comp 2 (th1 l ψ ^ 2) = 1 := by
      rw [hpow, hth1c, one_pow]
    have h := ((compCond O N (th1 l ψ ^ 2) 2 Nat.prime_two).2.1).mp h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  · rw [hf]
    exact hf0
  · rw [hf]
    exact dvd_trans (Nat.dvd_lcm_left 4 _) hdiv
  · rw [hf]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (Nat.dvd_lcm_right 4 _) hdiv)
  · have e := Nat.sub_dvd_pow_sub_pow l 1 (f0 l ψ)
    rwa [one_pow] at e
