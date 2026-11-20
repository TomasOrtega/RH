import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nonvan
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Struct
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AlgK
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DescZRetr

open UpperTheory.V.FW

/- English proof (translation)
Simplify using `[toK]`.
-/
private theorem toK_of (k G : Type) [CommRing k] [Monoid G] (g : G) :
    toK k G (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of k G g := by
  simp [toK]

/- English proof (translation)
Introduce `l hl f c hf hc hc1 hcf`. Establish `hp : l.Prime` using `hl.out`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`. Rewrite `hf` using `[Nat.coprime_zero_left]`.

Conclude with `hp.one_lt.ne' hf`. Establish `ht : Nat.totient (f * l ^ ee l) ≠ 0` using `(Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hp.ne_zero)))).ne'`. Take `⟨a, m, hm, ham⟩` from `Nat.exists_eq_pow_mul_and_not_dvd ht l hp.one_lt.ne'`. Establish `hml : m.Coprime l` using `((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm`. Take `⟨n₀, h2, hnv⟩` from `nonvan l f c hf hc hc1 hcf`.

Use `⟨l ^ n₀ * l ^ a, n₀, h2, ?_⟩` and prove the remaining obligations. Introduce `n _ hn`. Establish `h : l ^ n₀ ∣ f * l ^ n` using `Dvd.dvd.mul_left (pow_dvd_pow l hn) f`. Take `⟨γ, p, hγ, hγ1, hidx, hpz, hpow, hpJ, hπ⟩` from `struct l f n hf (h2.trans hn)`. Take `⟨hπ1, hπ2⟩` from `hπ n₀ h hn`.

Use `⟨γ, hγ, hidx, ?_⟩` and prove the remaining obligations. Use `descZ l (AlgebraicClosure (ZMod l)) _ _ _ _ ?_` and prove the remaining obligations. Establish `key` using `algK l a m n n₀ (AlgebraicClosure (ZMod l)) _ _ p (piQ l n₀ h) γ (-1) (toK (AlgebraicClosure (ZMod l)) _ (thetaH (f * l ^ n) c)) hml hγ1 hpz (fun g => by rw [← ham]; exact hpow g) hpJ hπ1 hπ2 (fun χ hχ => hnv n h hn _ χ hχ)`. Simplify `key` using `only [map_pow, map_sub, map_add, map_one, toK_of]`.
-/
theorem UpperTheory.V.FW.memZ :
    ∀ (l : ℕ) [Fact l.Prime] (f c : ℕ), f.Coprime l → Odd c → 1 < c → c.Coprime (f * l) → ∃ N n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (n : ℕ) [NeZero (f * l ^ n)], n₀ ≤ n → ∃ γ : (ZMod (f * l ^ n))ˣ, (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l ∧ (Subgroup.zpowers γ).index = Nat.totient (f * l ^ ee l) ∧ (MonoidAlgebra.of ℤ _ γ - 1) ^ N ∈ Ideal.span {thetaH (f * l ^ n) c, 1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod (f * l ^ n))ˣ), (l : MonoidAlgebra ℤ (ZMod (f * l ^ n))ˣ)} := by
  intro l hl f c hf hc hc1 hcf
  have hp : l.Prime := hl.out
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    exact hp.one_lt.ne' hf
  have ht : Nat.totient (f * l ^ ee l) ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hp.ne_zero)))).ne'
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht l hp.one_lt.ne'
  have hml : m.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  obtain ⟨n₀, h2, hnv⟩ := nonvan l f c hf hc hc1 hcf
  refine ⟨l ^ n₀ * l ^ a, n₀, h2, ?_⟩
  intro n _ hn
  have h : l ^ n₀ ∣ f * l ^ n := Dvd.dvd.mul_left (pow_dvd_pow l hn) f
  obtain ⟨γ, p, hγ, hγ1, hidx, hpz, hpow, hpJ, hπ⟩ := struct l f n hf (h2.trans hn)
  obtain ⟨hπ1, hπ2⟩ := hπ n₀ h hn
  refine ⟨γ, hγ, hidx, ?_⟩
  refine descZ l (AlgebraicClosure (ZMod l)) _ _ _ _ ?_
  have key := algK l a m n n₀ (AlgebraicClosure (ZMod l)) _ _ p (piQ l n₀ h) γ (-1)
    (toK (AlgebraicClosure (ZMod l)) _ (thetaH (f * l ^ n) c)) hml hγ1 hpz
    (fun g => by rw [← ham]; exact hpow g) hpJ hπ1 hπ2
    (fun χ hχ => hnv n h hn _ χ hχ)
  simpa only [map_pow, map_sub, map_add, map_one, toK_of] using key
