import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

namespace GlobalTheory.CMVal.NormCongr

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `: Fact q.Prime` using `⟨hq⟩`. Use `P.isPrime` as an intermediate fact. Establish `: Finite (𝓞 K ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot`. Rewrite `h` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) q h`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx` using `[addOrderOf_zero]`. Conclude with `hq.one_lt.ne hx`. Establish `h1 : q • x = 0` using `by rw [← hx]; exact addOrderOf_nsmul_eq_zero x`.

Rewrite `h1` using `[nsmul_eq_mul]`. Establish `h2 : ((q : ℕ) : 𝓞 K ⧸ P.asIdeal) = 0` using `(mul_eq_zero.1 h1).resolve_right hx0`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h2`.
-/
theorem natCast_mem_of_prime_dvd (P : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 K) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

/- English proof (translation)
Use `Nat.coprime_of_dvd fun q hq h1 h2 => hk ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `h2`. Rewrite using `[Nat.cast_mul]`. Conclude with `P.asIdeal.mul_mem_right _ (natCast_mem_of_prime_dvd P hq h1)`.
-/
theorem coprime_absNorm_of_not_mem (P : HeightOneSpectrum (𝓞 K)) {k : ℕ} (hk : (k : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime (Ideal.absNorm P.asIdeal) k := by
  refine Nat.coprime_of_dvd fun q hq h1 h2 => hk ?_
  obtain ⟨c, rfl⟩ := h2
  rw [Nat.cast_mul]
  exact P.asIdeal.mul_mem_right _ (natCast_mem_of_prime_dvd P hq h1)

/- English proof (translation)
Rewrite using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 K) K) n]`.
-/
theorem val_natCast (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) = v.valuation K (algebraMap (𝓞 K) K (n : 𝓞 K)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 K) K) n]

/- English proof (translation)
Rewrite using `[val_natCast]`. Conclude with `v.valuation_le_one _`.
-/
theorem val_natCast_le_one (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) ≤ 1 := by
  rw [val_natCast]; exact v.valuation_le_one _

/- English proof (translation)
Rewrite using `[val_natCast]`. Conclude with `(v.valuation_lt_one_iff_mem _).2 h`.
-/
theorem val_natCast_lt_one (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (h : (n : 𝓞 K) ∈ v.asIdeal) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) < 1 := by
  rw [val_natCast]; exact (v.valuation_lt_one_iff_mem _).2 h

end GlobalTheory.CMVal.NormCongr

open GlobalTheory.CMVal.IdeleIdeal GlobalTheory.CMVal.Euler in

/- English proof (translation)
Introduce `K _ _ t k n hn hkn m hm hyp`. Use `set p : (Af K)ˣ := Units.map (algebraMap K (Af K)).toMonoidHom (Units.mk0 m hm) with hp`. Use `set a : (Af K)ˣ := t⁻¹ * p with ha`. Establish `haval : (a : Af K) = ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m`. Simplify using `[ha, hp]`.

Establish `hn0 : (n : K) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `hdiff : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((a : Af K) v - 1) ≤ Valued.v ((algebraMap K (Af K) (n : K)) v)`. Introduce `v`. Establish `h1` using `hyp v`. Rewrite `h1` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Establish `e : (a : Af K) - 1 = algebraMap K (Af K) (n : K) * (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1))`. Rewrite using `[← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, _root_.one_mul, haval]`. Establish `e2 : (a : Af K) v - 1 = ((a : Af K) - 1) v` using `by rw [sub_coord, one_coord]`. Rewrite using `[e2, e, mul_coord, map_mul]`. Conclude with `mul_le_of_le_one_right' h1`.

Establish `hint : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((a : Af K) v) ≤ 1`. Introduce `v`. Establish `e : (a : Af K) v = ((a : Af K) v - 1) + 1` using `by ring`. Rewrite using `[e]`. Use `(Valued.v.map_add _ _).trans (max_le ?_ (by rw [map_one]))` and prove the remaining obligations.

Conclude with `(hdiff v).trans (NormCongr.val_natCast_le_one v n)`. Establish `hunit : ∀ v : HeightOneSpectrum (𝓞 K), (k : 𝓞 K) ∈ v.asIdeal → Valued.v ((a : Af K) v) = 1`. Introduce `v hk`. Establish `hnv : (n : 𝓞 K) ∈ v.asIdeal`. Take `⟨c, rfl⟩` from `hkn`.

Rewrite using `[Nat.cast_mul]`. Conclude with `v.asIdeal.mul_mem_right _ hk`. Establish `hlt` using `(hdiff v).trans_lt (NormCongr.val_natCast_lt_one v hnv)`. Establish `e : (a : Af K) v = 1 + ((a : Af K) v - 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `Valuation.map_one_add_of_lt _ hlt`. Establish `hmod : modF p = modF t * modF a`. Rewrite using `[← IdeleModule.modF_mul, ha, _root_.mul_inv_cancel_left]`. Establish `hpr` using `IdeleModule.modF_princ (Units.mk0 m hm)`. Rewrite `hpr` using `[← hp, Units.val_mk0]`.

Establish `hb` using `modF_eq hint`. Use `⟨Ideal.absNorm (idealOf a), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hpos` using `IdeleModule.modF_pos a`. Rewrite `hpos` using `[hb]`. Break down `Nat.eq_zero_or_pos (Ideal.absNorm (idealOf a)) with h0 | h0` into its components or cases.

Rewrite `hpos` using `[h0]`. Simplify using `at hpos`. Conclude with `h0`. Unfold `idealOf`. Rewrite using `[map_finprod Ideal.absNorm (finite_pow a)]`.

Use `finprod_induction (fun x : ℕ => Nat.Coprime x k) (Nat.coprime_one_left k) (fun x y hx hy => Nat.Coprime.mul hx hy) fun w => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Break down `Nat.eq_zero_or_pos (ordAt a w) with h0 | h0` into its components or cases. Rewrite using `[h0, pow_zero]`. Conclude with `Nat.coprime_one_left k`.

Use `Nat.Coprime.pow_left _ (NormCongr.coprime_absNorm_of_not_mem w fun hk => ?_)` and prove the remaining obligations. Establish `h1` using `hunit w hk`. Establish `: ordAt a w = 0` using `by simp [ordAt, h1]`. Use linear arithmetic over natural numbers and integers. Establish `htpos` using `IdeleModule.modF_pos t`.

Rewrite `hpr` using `[hmod, hb]`. Establish `e : |((Algebra.norm ℚ m : ℚ) : ℝ)| = (|((Algebra.norm ℚ m : ℚ) : ℝ)|)⁻¹⁻¹` using `(inv_inv _).symm`. Rewrite using `[e, ← hpr, mul_inv, inv_inv, div_eq_mul_inv, _root_.mul_comm]`.
-/
theorem GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (k n : ℕ), 0 < n → k ∣ n → ∀ m : K, m ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) →
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ |((Algebra.norm ℚ m : ℚ) : ℝ)| = b / modF t := by
  intro K _ _ t k n hn hkn m hm hyp
  set p : (Af K)ˣ := Units.map (algebraMap K (Af K)).toMonoidHom (Units.mk0 m hm) with hp
  set a : (Af K)ˣ := t⁻¹ * p with ha
  have haval : (a : Af K) = ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m := by
    simp [ha, hp]
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'

  have hdiff : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((a : Af K) v - 1) ≤ Valued.v ((algebraMap K (Af K) (n : K)) v) := by
    intro v
    have h1 := hyp v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    have e : (a : Af K) - 1 = algebraMap K (Af K) (n : K) *
        (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) := by
      rw [← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, _root_.one_mul, haval]
    have e2 : (a : Af K) v - 1 = ((a : Af K) - 1) v := by rw [sub_coord, one_coord]
    rw [e2, e, mul_coord, map_mul]
    exact mul_le_of_le_one_right' h1
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((a : Af K) v) ≤ 1 := by
    intro v
    have e : (a : Af K) v = ((a : Af K) v - 1) + 1 := by ring
    rw [e]
    refine (Valued.v.map_add _ _).trans (max_le ?_ (by rw [map_one]))
    exact (hdiff v).trans (NormCongr.val_natCast_le_one v n)
  have hunit : ∀ v : HeightOneSpectrum (𝓞 K), (k : 𝓞 K) ∈ v.asIdeal → Valued.v ((a : Af K) v) = 1 := by
    intro v hk
    have hnv : (n : 𝓞 K) ∈ v.asIdeal := by
      obtain ⟨c, rfl⟩ := hkn
      rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hk
    have hlt := (hdiff v).trans_lt (NormCongr.val_natCast_lt_one v hnv)
    have e : (a : Af K) v = 1 + ((a : Af K) v - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hlt

  have hmod : modF p = modF t * modF a := by
    rw [← IdeleModule.modF_mul, ha, _root_.mul_inv_cancel_left]
  have hpr := IdeleModule.modF_princ (Units.mk0 m hm)
  rw [← hp, Units.val_mk0] at hpr
  have hb := modF_eq hint
  refine ⟨Ideal.absNorm (idealOf a), ?_, ?_, ?_⟩
  · have hpos := IdeleModule.modF_pos a
    rw [hb] at hpos
    rcases Nat.eq_zero_or_pos (Ideal.absNorm (idealOf a)) with h0 | h0
    · rw [h0] at hpos; simp at hpos
    · exact h0
  · unfold idealOf
    rw [map_finprod Ideal.absNorm (finite_pow a)]
    refine finprod_induction (fun x : ℕ => Nat.Coprime x k) (Nat.coprime_one_left k)
      (fun x y hx hy => Nat.Coprime.mul hx hy) fun w => ?_
    rw [map_pow]
    rcases Nat.eq_zero_or_pos (ordAt a w) with h0 | h0
    · rw [h0, pow_zero]; exact Nat.coprime_one_left k
    · refine Nat.Coprime.pow_left _ (NormCongr.coprime_absNorm_of_not_mem w fun hk => ?_)
      have h1 := hunit w hk
      have : ordAt a w = 0 := by simp [ordAt, h1]
      omega
  · have htpos := IdeleModule.modF_pos t
    rw [hmod, hb] at hpr
    have e : |((Algebra.norm ℚ m : ℚ) : ℝ)| = (|((Algebra.norm ℚ m : ℚ) : ℝ)|)⁻¹⁻¹ := (inv_inv _).symm
    rw [e, ← hpr, mul_inv, inv_inv, div_eq_mul_inv, _root_.mul_comm]
