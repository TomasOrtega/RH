import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CmDatumCharTwoAdicOrderBounds
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Take `⟨hd, χ₀, e⟩` from `χ.factorsThrough_conductor`. Establish `h0 : χ₀ ^ Nat.totient χ.conductor = 1`. Use `MulChar.ext (fun a => ?_)` and prove the remaining obligations. Rewrite using `[MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]`. Establish `h1 : DirichletCharacter.changeLevel hd χ₀ ^ Nat.totient χ.conductor = 1`.

Rewrite using `[← map_pow, h0, map_one]`. Rewrite `h1` using `[← e]`. Then use the resulting hypothesis.
-/
private theorem pow_totient_conductor {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient χ.conductor = 1 := by
  obtain ⟨hd, χ₀, e⟩ := χ.factorsThrough_conductor
  have h0 : χ₀ ^ Nat.totient χ.conductor = 1 := by
    refine MulChar.ext (fun a => ?_)
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
      ZMod.pow_totient, Units.val_one, map_one]
  have h1 : DirichletCharacter.changeLevel hd χ₀ ^ Nat.totient χ.conductor = 1 := by
    rw [← map_pow, h0, map_one]
  rwa [← e] at h1

/- English proof (translation)
Break down `Nat.eq_zero_or_pos c with rfl | hc` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Nat.totient_prime_pow Nat.prime_two hc]`. Simplify using `using Nat.pow_dvd_pow 2 (Nat.sub_le c 1)`.
-/
private theorem totient_two_pow_dvd (c : ℕ) : Nat.totient (2 ^ c) ∣ 2 ^ c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two hc]
    simpa using Nat.pow_dvd_pow 2 (Nat.sub_le c 1)

/- English proof (translation)
Introduce `h O _ _ ψ hψ l hl hl2 hlt`. Take `⟨-, -, -, hR1, -⟩` from `cmDatum_char_two_adic_order_bounds h O ψ hψ l hl hl2`. Take `⟨-, -, -, hopos, -⟩` from `hostIndex h`. Establish `hc2 : comp 2 ψ ^ (2 ^ c2 ψ) = 1`. Take `⟨-, -, -, hpow2, -⟩` from `compCond O h.N ψ 2 Nat.prime_two`.

Establish `ht` using `pow_totient_conductor (comp 2 ψ)`. Rewrite `ht` using `[show (comp 2 ψ).conductor = 2 ^ c2 ψ from hpow2.symm]`. Conclude with `orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one ht).trans (totient_two_pow_dvd _))`. Establish `hall : ψ ^ (2 * h.o * 2 ^ c2 ψ) = 1`. Apply `(compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ` to reduce the goal to its premises.

Introduce `p hp`. Establish `hpp` using `Nat.prime_of_mem_primeFactors hp`. Distinguish the cases in `h2p : p = 2`. Substitute `h2p` using the available equality. Rewrite using `[mul_comm, pow_mul, hc2, one_pow]`.

Establish `hd` using `((hostComp h O ψ hψ).2.2 p hpp h2p).1`. Rewrite using `[pow_mul, orderOf_dvd_iff_pow_eq_one.mp hd, one_pow]`. Establish `hmpos : 0 < 2 * h.o * 2 ^ c2 ψ` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.HV.vsOrd :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 → 2 ^ c2 ψ < h.R1 l ψ →
      orderOf ψ ≤ 2 * h.o * (16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o))) := by
  intro h O _ _ ψ hψ l hl hl2 hlt
  obtain ⟨-, -, -, hR1, -⟩ := cmDatum_char_two_adic_order_bounds h O ψ hψ l hl hl2
  obtain ⟨-, -, -, hopos, -⟩ := hostIndex h
  have hc2 : comp 2 ψ ^ (2 ^ c2 ψ) = 1 := by
    obtain ⟨-, -, -, hpow2, -⟩ := compCond O h.N ψ 2 Nat.prime_two
    have ht := pow_totient_conductor (comp 2 ψ)
    rw [show (comp 2 ψ).conductor = 2 ^ c2 ψ from hpow2.symm] at ht
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one ht).trans (totient_two_pow_dvd _))
  have hall : ψ ^ (2 * h.o * 2 ^ c2 ψ) = 1 := by
    apply (compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases h2p : p = 2
    · subst h2p
      rw [mul_comm, pow_mul, hc2, one_pow]
    · have hd := ((hostComp h O ψ hψ).2.2 p hpp h2p).1
      rw [pow_mul, orderOf_dvd_iff_pow_eq_one.mp hd, one_pow]
  have hmpos : 0 < 2 * h.o * 2 ^ c2 ψ := by positivity
  calc orderOf ψ ≤ 2 * h.o * 2 ^ c2 ψ := Nat.le_of_dvd hmpos (orderOf_dvd_of_pow_eq_one hall)
    _ ≤ _ := Nat.mul_le_mul_left _ (hlt.le.trans hR1)
