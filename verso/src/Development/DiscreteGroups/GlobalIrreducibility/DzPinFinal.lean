import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzPinB
import Development.DiscreteGroups.GlobalIrreducibility.DzDigDef
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

noncomputable section

set_option linter.style.haveILetI false

namespace DiscreteGroups.sglob.DzType

open NumberField IsDedekindDomain

/- English proof (translation)
Introduce `g _ n hn2 hbig K _ _ hcard ψ₀ hψ₀ θ ξ hθ hξ hH`. Establish `hgp : g.Prime` using `Fact.out`. Establish `hg2` using `hgp.two_le`. Establish `hfin : Finite K` using `Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Use `letI : Fintype K := Fintype.ofFinite K`.

Establish `hK : Fintype.card K = g ^ n` using `by rw [← Nat.card_eq_fintype_card, hcard]`. Establish `hg2n : g ^ 2 ≤ g ^ n` using `Nat.pow_le_pow_right (by omega) hn2`. Establish `hg4 : 4 ≤ g ^ 2` using `by nlinarith`. Use `set N := g ^ n - 1 with hNdef`. Establish `hN1 : N + 1 = g ^ n` using `by omega`.

Establish `hN0 : 0 < N` using `by omega`. Establish `hN1lt : 1 < N` using `by omega`. Take `⟨Q, ω, Ω, hΩi, hdat⟩` from `DzPin.exists_setup g n (by omega) K hK ψ₀ hψ₀`. Take `⟨k, hk⟩` from `DzPin.exists_eq_pow_of_injective Ω θ hΩi`. Take `⟨k', hk'⟩` from `DzPin.exists_eq_pow_of_injective Ω ξ hΩi`.

Establish `hΩN : Ω ^ N = 1`. Use `MonoidHom.ext fun z => ?_` and prove the remaining obligations. Establish `hz : z ^ N = 1` using `Units.ext (by`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one, hNdef, ← hK]`. Conclude with `FiniteField.pow_card_sub_one_eq_one _ z.ne_zero)`.

Rewrite using `[MonoidHom.pow_apply, ← map_pow, hz, map_one, MonoidHom.one_apply]`. Establish `hreg : ∀ {η : Kˣ →* ℂˣ} {m : ℕ}, η = Ω ^ m → GlobalTheory.Published.IsRegularChar g n η → ∀ i j, i < n → j < n → m * g ^ i ≡ m * g ^ j [MOD g ^ n - 1] → i = j`. Introduce `η m hηm hr i j hi hj hm`. Use `hr i j hi hj ?_` and prove the remaining obligations. Rewrite using `[hηm, ← pow_mul, ← pow_mul]`.

Conclude with `DzPin.pow_eq_pow_of_modEq hΩN hm`. Establish `hmain : ∀ u b : ℕ, u.Coprime (g ^ n - 1) → (Nat.digits g ((u * k + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum + (Nat.digits g (u * k' % (g ^ n - 1))).sum = (Nat.digits g ((u * k' + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum + (Nat.digits g (u * k % (g ^ n - 1))).sum`. Introduce `u b hu`. Use `haveI : NeZero N := ⟨by omega⟩`. Use `set t0 := ((ZMod.unitOfCoprime u hu)⁻¹ : (ZMod N)ˣ).val.val with ht0def`.

Establish `h0 : u * t0 ≡ 1 [MOD N]`. Rewrite using `[← ZMod.natCast_eq_natCast_iff]`. Use `push_cast`. Rewrite using `[ht0def, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime u hu, Units.mul_inv]`. Use `set t := t0 + N * (t0 + 1) with htdef`.

Establish `htu : t * u ≡ 1 [MOD N]`. Establish `e : t * u = u * t0 + N * ((t0 + 1) * u)` using `by rw [htdef]; ring`. Unfold `Nat.ModEq`. Rewrite using `[e, Nat.add_mul_mod_self_left]`. Conclude with `h0`.

Establish `htN : t.Coprime N` using `Nat.coprime_of_mul_modEq_one u htu`. Establish `htg : t.Coprime g`. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]`. Introduce `hdt`. Establish `h1 : g ∣ t + 1`.

Establish `e : t + 1 = g ^ n * (t0 + 1)` using `by rw [← hN1, htdef]; ring`. Rewrite using `[e]`. Conclude with `Dvd.dvd.mul_right (dvd_pow_self g (by omega)) _`. Establish `h2 : g ∣ 1` using `(Nat.dvd_add_right hdt).mp h1`. Conclude with `hgp.one_lt.ne' (Nat.dvd_one.mp h2)`.

Take `⟨Φ, D, hΦi, hDω, hΦζ, hΦω⟩` from `hdat t (Nat.Coprime.mul_right htg htN)`. Establish `hG : ∀ (η : Kˣ →* ℂˣ) (a : ℕ), η = Ω ^ (t * a) → gs ψ₀ η⁻¹ = Φ (D.g a)`. Introduce `η a hη`. Conclude with `DzPin.gs_eq ψ₀ Φ D.ω D.ζ D.prim.pow_eq_one hΦζ η a (fun z => by`. Rewrite using `[hη, hDω, hΦω, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, pow_mul])`.

Use `set e := (g ^ n - 1) / (g - 1) with hedef`. Set `χ₀ : (ZMod g)ˣ →* ℂˣ` to `(Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ (t * b)`. Establish `hnm : nmChar K χ₀ = Ω ^ (e * (t * b))` using `DzPin.nm_eq hK Ω (t * b)`. Take `⟨r, hr, hrr⟩` from `hH χ₀`. Establish `h1 : θ * nmChar K χ₀ = Ω ^ (t * ((u * k + b * e) % N))`.

Rewrite using `[hnm, hk, ← pow_add]`. Conclude with `(DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm`. Establish `h2 : ξ = Ω ^ (t * (u * k' % N))`. Rewrite using `[hk']`. Conclude with `(DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm`.

Establish `h3 : ξ * nmChar K χ₀ = Ω ^ (t * ((u * k' + b * e) % N))`. Rewrite using `[hnm, hk', ← pow_add]`. Conclude with `(DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm`. Establish `h4 : θ = Ω ^ (t * (u * k % N))`. Rewrite using `[hk]`.

Conclude with `(DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm`. Rewrite `hrr` using `[hG _ _ h1, hG _ _ h2, hG _ _ h3, hG _ _ h4, ← map_mul, ← map_mul, ← map_pow, ← map_pow]`. Conclude with `DzPin.dsum_eq_of_pow_eq D (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0) hr (hΦi hrr)`. Take `⟨i, hi⟩` from `hD g n hgp hn2 hbig k k' (hreg hk hθ) (hreg hk' hξ) hmain`. Use `⟨i, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[hk', hk, DzPin.pow_eq_pow_of_modEq hΩN hi, MonoidHom.pow_apply, MonoidHom.pow_apply, map_pow, ← pow_mul, mul_comm]`.
-/
theorem lPin_of_dig (hD : Dig) : LPin := by
  intro g _ n hn2 hbig K _ _ hcard ψ₀ hψ₀ θ ξ hθ hξ hH
  classical
  have hgp : g.Prime := Fact.out
  have hg2 := hgp.two_le
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  have hg2n : g ^ 2 ≤ g ^ n := Nat.pow_le_pow_right (by omega) hn2
  have hg4 : 4 ≤ g ^ 2 := by nlinarith
  set N := g ^ n - 1 with hNdef
  have hN1 : N + 1 = g ^ n := by omega
  have hN0 : 0 < N := by omega
  have hN1lt : 1 < N := by omega
  obtain ⟨Q, ω, Ω, hΩi, hdat⟩ := DzPin.exists_setup g n (by omega) K hK ψ₀ hψ₀
  obtain ⟨k, hk⟩ := DzPin.exists_eq_pow_of_injective Ω θ hΩi
  obtain ⟨k', hk'⟩ := DzPin.exists_eq_pow_of_injective Ω ξ hΩi
  have hΩN : Ω ^ N = 1 := by
    refine MonoidHom.ext fun z => ?_
    have hz : z ^ N = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one, hNdef, ← hK]
      exact FiniteField.pow_card_sub_one_eq_one _ z.ne_zero)
    rw [MonoidHom.pow_apply, ← map_pow, hz, map_one, MonoidHom.one_apply]
  have hreg : ∀ {η : Kˣ →* ℂˣ} {m : ℕ}, η = Ω ^ m → GlobalTheory.Published.IsRegularChar g n η →
      ∀ i j, i < n → j < n → m * g ^ i ≡ m * g ^ j [MOD g ^ n - 1] → i = j := by
    intro η m hηm hr i j hi hj hm
    refine hr i j hi hj ?_
    rw [hηm, ← pow_mul, ← pow_mul]
    exact DzPin.pow_eq_pow_of_modEq hΩN hm
  have hmain : ∀ u b : ℕ, u.Coprime (g ^ n - 1) →
      (Nat.digits g ((u * k + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum +
          (Nat.digits g (u * k' % (g ^ n - 1))).sum =
        (Nat.digits g ((u * k' + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum +
          (Nat.digits g (u * k % (g ^ n - 1))).sum := by
    intro u b hu
    haveI : NeZero N := ⟨by omega⟩
    set t0 := ((ZMod.unitOfCoprime u hu)⁻¹ : (ZMod N)ˣ).val.val with ht0def
    have h0 : u * t0 ≡ 1 [MOD N] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [ht0def, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime u hu, Units.mul_inv]
    set t := t0 + N * (t0 + 1) with htdef
    have htu : t * u ≡ 1 [MOD N] := by
      have e : t * u = u * t0 + N * ((t0 + 1) * u) := by rw [htdef]; ring
      unfold Nat.ModEq
      rw [e, Nat.add_mul_mod_self_left]
      exact h0
    have htN : t.Coprime N := Nat.coprime_of_mul_modEq_one u htu
    have htg : t.Coprime g := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
      intro hdt
      have h1 : g ∣ t + 1 := by
        have e : t + 1 = g ^ n * (t0 + 1) := by rw [← hN1, htdef]; ring
        rw [e]
        exact Dvd.dvd.mul_right (dvd_pow_self g (by omega)) _
      have h2 : g ∣ 1 := (Nat.dvd_add_right hdt).mp h1
      exact hgp.one_lt.ne' (Nat.dvd_one.mp h2)
    obtain ⟨Φ, D, hΦi, hDω, hΦζ, hΦω⟩ := hdat t (Nat.Coprime.mul_right htg htN)
    have hG : ∀ (η : Kˣ →* ℂˣ) (a : ℕ), η = Ω ^ (t * a) → gs ψ₀ η⁻¹ = Φ (D.g a) := by
      intro η a hη
      exact DzPin.gs_eq ψ₀ Φ D.ω D.ζ D.prim.pow_eq_one hΦζ η a (fun z => by
        rw [hη, hDω, hΦω, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, pow_mul])
    set e := (g ^ n - 1) / (g - 1) with hedef
    let χ₀ : (ZMod g)ˣ →* ℂˣ := (Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ (t * b)
    have hnm : nmChar K χ₀ = Ω ^ (e * (t * b)) := DzPin.nm_eq hK Ω (t * b)
    obtain ⟨r, hr, hrr⟩ := hH χ₀
    have h1 : θ * nmChar K χ₀ = Ω ^ (t * ((u * k + b * e) % N)) := by
      rw [hnm, hk, ← pow_add]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm
    have h2 : ξ = Ω ^ (t * (u * k' % N)) := by
      rw [hk']
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm
    have h3 : ξ * nmChar K χ₀ = Ω ^ (t * ((u * k' + b * e) % N)) := by
      rw [hnm, hk', ← pow_add]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm
    have h4 : θ = Ω ^ (t * (u * k % N)) := by
      rw [hk]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm
    rw [hG _ _ h1, hG _ _ h2, hG _ _ h3, hG _ _ h4, ← map_mul, ← map_mul, ← map_pow,
      ← map_pow] at hrr
    exact DzPin.dsum_eq_of_pow_eq D (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0)
      (Nat.mod_lt _ hN0) hr (hΦi hrr)
  obtain ⟨i, hi⟩ := hD g n hgp hn2 hbig k k' (hreg hk hθ) (hreg hk' hξ) hmain
  refine ⟨i, fun z => ?_⟩
  rw [hk', hk, DzPin.pow_eq_pow_of_modEq hΩN hi, MonoidHom.pow_apply, MonoidHom.pow_apply, map_pow,
    ← pow_mul, mul_comm]

end DiscreteGroups.sglob.DzType
