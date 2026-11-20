import Mathlib
import GroundTheory.LocalFields.PadicExp
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.PrincipalUnitsModule
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.LocalFields.Examples
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open GroundTheory.LocalField ValuativeRel IsLocalRing

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Powers

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

/- English proof (translation)
Rewrite using `[mem_valBall, normalizedValuation_natCast_prime p]`.
-/
theorem natCast_prime_mem_valBall : (p : K) ∈ valBall K (absRamificationIndex K) := by
  rw [mem_valBall, normalizedValuation_natCast_prime p]

/- English proof (translation)
Establish `h` using `div_natCast_mem_valBall p hx hp.out.ne_zero`. Rewrite `h` using `[padicValNat_self, Nat.cast_one, mul_one, add_sub_cancel_right]`. Conclude with `h`.
-/
theorem div_natCast_prime_mem_valBall {a : ℤ} {x : K}
    (hx : x ∈ valBall K (a + absRamificationIndex K)) : x / p ∈ valBall K a := by
  have h := div_natCast_mem_valBall p hx hp.out.ne_zero
  rw [padicValNat_self, Nat.cast_one, mul_one, add_sub_cancel_right] at h
  exact h

/- English proof (translation)
Use `set e := absRamificationIndex K`. Establish `hn1 : 1 ≤ n` using `one_le_of_lt_sub_one_mul_nat p hn`. Establish `hp1 : (1 : ℤ) ≤ (p - 1 : ℤ)` using `by have := hp.out.two_le; omega`. Establish `hn' : (e : ℤ) < (p - 1 : ℤ) * ((n + e : ℕ) : ℤ)`. Establish `: (p - 1 : ℤ) * n ≤ (p - 1 : ℤ) * ((n + e : ℕ) : ℤ)` using `mul_le_mul_of_nonneg_left (by push_cast; omega) (by omega)`.

Use linear arithmetic over natural numbers and integers. Establish `hne : (n : ℤ) + e = ((n + e : ℕ) : ℤ)` using `by push_cast; ring`. Establish `hlogpow : ∀ u : unitFiltrationUnits K n, logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) = p * logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1)`. Introduce `u`. Establish `h` using `map_nsmul (logValBallHom p n hn) p (Additive.ofMul u)`.

Establish `h'` using `congrArg Subtype.val h`. Rewrite `h'` using `[← ofMul_pow]`. Rewrite `h'` using `[coe_logValBallHom]`. Simplify `h'` using `[coe_logValBallHom, nsmul_eq_mul]`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨u, hu, rfl⟩ set U : unitFiltrationUnits K n := ⟨u, hu⟩`. Establish `hU : ((U ^ p : unitFiltrationUnits K n) : Kˣ) = powMonoidHom p u` using `rfl`. Establish `hlog : logSeries ((((U ^ p : unitFiltrationUnits K n) : Kˣ) : K) - 1) ∈ valBall K ((n + e : ℕ) : ℤ)`. Rewrite using `[hlogpow U, ← hne, add_comm]`. Conclude with `mul_mem_valBall (natCast_prime_mem_valBall p) (logSeries_mem_valBall p (sub_one_mem_valBall_of_mem hn1 U) hn)`.

Establish `hexp` using `expSeries_logSeries p hn (U ^ p)`. Establish `hmem` using `expSeries_sub_one_mem p hlog hn'`. Rewrite `hmem` using `[hexp]`. Rewrite using `[← hU]`. Conclude with `(mem_unitFiltrationUnits_iff_valBall (by omega)).2 hmem`.

Introduce `w hw`. Establish `hwn : w ∈ unitFiltrationUnits K n` using `unitFiltrationUnits_antitone (by omega) hw`. Use `set W : unitFiltrationUnits K n := ⟨w, hwn⟩`. Establish `hy : logSeries (((w : Kˣ) : K) - 1) ∈ valBall K (n + e)`. Rewrite using `[hne]`.

Conclude with `logSeries_mem_valBall p ((mem_unitFiltrationUnits_iff_valBall (by omega)).1 hw) hn'`. Establish `hz : logSeries (((w : Kˣ) : K) - 1) / p ∈ valBall K n` using `div_natCast_prime_mem_valBall p hy`. Use `set u := expUnit p n hn ⟨_, hz⟩`. Use `⟨(u : Kˣ), u.2, ?_⟩` and prove the remaining obligations. Establish `hinj` using `logValBallHom_injective p n hn`.

Establish `key : logValBallHom p n hn (Additive.ofMul (u ^ p)) = logValBallHom p n hn (Additive.ofMul W)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_logValBallHom, coe_logValBallHom]`. Express the relevant statement in the definitionally equal form `logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) = _`. Rewrite using `[hlogpow u]`.

Establish `hu` using `congrArg Subtype.val (logValBallHom_expUnit p n hn ⟨_, hz⟩)`. Rewrite `hu` using `[coe_logValBallHom, toMul_ofMul]`. Establish `hu' : logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) = logSeries (((w : Kˣ) : K) - 1) / p` using `hu`. Rewrite using `[hu', toMul_ofMul]`. Establish `hp0 : (p : K) ≠ 0` using `Nat.cast_ne_zero.2 hp.out.ne_zero`.

Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression. Use `congrArg (fun v => ((Additive.toMul v : unitFiltrationUnits K n) : Kˣ)) (hinj key)` as an intermediate fact. Conclude with `this`.
-/
theorem map_pow_unitFiltrationUnits {n : ℕ}
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    (unitFiltrationUnits K n).map (powMonoidHom p) =
      unitFiltrationUnits K (n + absRamificationIndex K) := by
  set e := absRamificationIndex K
  have hn1 : 1 ≤ n := one_le_of_lt_sub_one_mul_nat p hn
  have hp1 : (1 : ℤ) ≤ (p - 1 : ℤ) := by have := hp.out.two_le; omega
  have hn' : (e : ℤ) < (p - 1 : ℤ) * ((n + e : ℕ) : ℤ) := by
    have : (p - 1 : ℤ) * n ≤ (p - 1 : ℤ) * ((n + e : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left (by push_cast; omega) (by omega)
    omega
  have hne : (n : ℤ) + e = ((n + e : ℕ) : ℤ) := by push_cast; ring

  have hlogpow : ∀ u : unitFiltrationUnits K n,
      logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) =
        p * logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := by
    intro u
    have h := map_nsmul (logValBallHom p n hn) p (Additive.ofMul u)
    have h' := congrArg Subtype.val h
    rw [← ofMul_pow] at h'
    rw [coe_logValBallHom] at h'
    simpa [coe_logValBallHom, nsmul_eq_mul] using h'
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    set U : unitFiltrationUnits K n := ⟨u, hu⟩
    have hU : ((U ^ p : unitFiltrationUnits K n) : Kˣ) = powMonoidHom p u := rfl

    have hlog : logSeries ((((U ^ p : unitFiltrationUnits K n) : Kˣ) : K) - 1) ∈
        valBall K ((n + e : ℕ) : ℤ) := by
      rw [hlogpow U, ← hne, add_comm]
      exact mul_mem_valBall (natCast_prime_mem_valBall p)
        (logSeries_mem_valBall p (sub_one_mem_valBall_of_mem hn1 U) hn)
    have hexp := expSeries_logSeries p hn (U ^ p)
    have hmem := expSeries_sub_one_mem p hlog hn'
    rw [hexp] at hmem
    rw [← hU]
    exact (mem_unitFiltrationUnits_iff_valBall (by omega)).2 hmem
  · intro w hw
    have hwn : w ∈ unitFiltrationUnits K n := unitFiltrationUnits_antitone (by omega) hw
    set W : unitFiltrationUnits K n := ⟨w, hwn⟩
    have hy : logSeries (((w : Kˣ) : K) - 1) ∈ valBall K (n + e) := by
      rw [hne]
      exact logSeries_mem_valBall p ((mem_unitFiltrationUnits_iff_valBall (by omega)).1 hw) hn'
    have hz : logSeries (((w : Kˣ) : K) - 1) / p ∈ valBall K n := div_natCast_prime_mem_valBall p hy
    set u := expUnit p n hn ⟨_, hz⟩
    refine ⟨(u : Kˣ), u.2, ?_⟩
    have hinj := logValBallHom_injective p n hn
    have key : logValBallHom p n hn (Additive.ofMul (u ^ p)) =
        logValBallHom p n hn (Additive.ofMul W) := by
      apply Subtype.ext
      rw [coe_logValBallHom, coe_logValBallHom]
      change logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) = _
      rw [hlogpow u]
      have hu := congrArg Subtype.val (logValBallHom_expUnit p n hn ⟨_, hz⟩)
      rw [coe_logValBallHom, toMul_ofMul] at hu
      have hu' : logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) =
          logSeries (((w : Kˣ) : K) - 1) / p := hu
      rw [hu', toMul_ofMul]
      have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
      field_simp
      rfl
    have := congrArg (fun v => ((Additive.toMul v : unitFiltrationUnits K n) : Kˣ)) (hinj key)
    exact this

/- English proof (translation)
Use `⟨absRamificationIndex K + 1, fun n hn => map_pow_unitFiltrationUnits p ?_⟩` and prove the remaining obligations. Establish `hp1 : (1 : ℤ) ≤ (p - 1 : ℤ)` using `by have := hp.out.two_le; omega`. Establish `: (n : ℤ) ≤ (p - 1 : ℤ) * n` using `le_mul_of_one_le_left (by omega) hp1`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_map_pow_unitFiltrationUnits :
    ∃ n₀, ∀ n ≥ n₀, (unitFiltrationUnits K n).map (powMonoidHom p) =
      unitFiltrationUnits K (n + absRamificationIndex K) := by
  refine ⟨absRamificationIndex K + 1, fun n hn => map_pow_unitFiltrationUnits p ?_⟩
  have hp1 : (1 : ℤ) ≤ (p - 1 : ℤ) := by have := hp.out.two_le; omega
  have : (n : ℤ) ≤ (p - 1 : ℤ) * n := le_mul_of_one_le_left (by omega) hp1
  omega

end Powers

section Residue

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

omit hp in

/- English proof (translation)
Introduce `h`. Apply `natCast_card_residueField_sub_one_ne_zero K` to reduce the goal to its premises. Conclude with `(CharP.cast_eq_zero_iff 𝓀[K] p _).2 h`.
-/
theorem not_dvd_card_residueField_sub_one : ¬ p ∣ Nat.card 𝓀[K] - 1 := by
  intro h
  apply natCast_card_residueField_sub_one_ne_zero K
  exact (CharP.cast_eq_zero_iff 𝓀[K] p _).2 h

/- English proof (translation)
Establish `h` using `pow_mem (unitsMulInvTeichmuller_mem v) (Nat.card 𝓀[K] - 1)`. Rewrite `h` using `[mul_pow, inv_pow, teichmuller_pow_card_sub_one, inv_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem pow_card_sub_one_mem_unitFiltration (v : 𝒪[K]ˣ) :
    v ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1 := by
  have h := pow_mem (unitsMulInvTeichmuller_mem v) (Nat.card 𝓀[K] - 1)
  rwa [mul_pow, inv_pow, teichmuller_pow_card_sub_one, inv_one, mul_one] at h

/- English proof (translation)
Establish `h` using `nsmul_prime_pow_mem_principalFiltration p (u := Additive.ofMul (⟨x, hx⟩ : unitFiltrationUnits K 1)) (by rw [principalFiltration_zero]; exact AddSubgroup.mem_top _) n`. Rewrite `h` using `[zero_add, mem_principalFiltration, toMul_nsmul, toMul_ofMul]`. Rewrite using `[mem_unitFiltrationUnits_iff_valBall (by omega)]`. Conclude with `h` after adjusting the coercions.
-/
theorem pow_prime_pow_mem_unitFiltrationUnits {x : Kˣ} (hx : x ∈ unitFiltrationUnits K 1) (n : ℕ) :
    x ^ p ^ n ∈ unitFiltrationUnits K (n + 1) := by
  have h := nsmul_prime_pow_mem_principalFiltration p
    (u := Additive.ofMul (⟨x, hx⟩ : unitFiltrationUnits K 1))
    (by rw [principalFiltration_zero]; exact AddSubgroup.mem_top _) n
  rw [zero_add, mem_principalFiltration, toMul_nsmul, toMul_ofMul] at h
  rw [mem_unitFiltrationUnits_iff_valBall (by omega)]
  exact_mod_cast h

/- English proof (translation)
Use `⟨Nat.card 𝓀[K] - 1, n, not_dvd_card_residueField_sub_one p, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨v, -, rfl⟩` from `hu`. Establish `h1 : unitsIncl K (v ^ (Nat.card 𝓀[K] - 1)) ∈ unitFiltrationUnits K 1` using `⟨_, pow_card_sub_one_mem_unitFiltration v, rfl⟩`. Establish `h2` using `pow_prime_pow_mem_unitFiltrationUnits p h1 n`. Rewrite `h2` using `[map_pow, ← pow_mul]`.

Conclude with `unitFiltrationUnits_antitone (by omega) h2`.
-/
theorem exists_pow_mem_unitFiltrationUnits (n : ℕ) :
    ∃ c j : ℕ, ¬ p ∣ c ∧ ∀ u ∈ unitFiltrationUnits K 0, u ^ (c * p ^ j) ∈ unitFiltrationUnits K n := by
  refine ⟨Nat.card 𝓀[K] - 1, n, not_dvd_card_residueField_sub_one p, fun u hu => ?_⟩
  obtain ⟨v, -, rfl⟩ := hu
  have h1 : unitsIncl K (v ^ (Nat.card 𝓀[K] - 1)) ∈ unitFiltrationUnits K 1 :=
    ⟨_, pow_card_sub_one_mem_unitFiltration v, rfl⟩
  have h2 := pow_prime_pow_mem_unitFiltrationUnits p h1 n
  rw [map_pow, ← pow_mul] at h2
  exact unitFiltrationUnits_antitone (by omega) h2

end Residue

section Norm

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]
  [Algebra.IsAlgebraic K Ω]

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

/- English proof (translation)
Establish `hirr` using `(IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec`. Establish `hv : normalizedValuation K (p : K) = normalizedValuation K (((baseUnif K : 𝒪[K]) : K) ^ absRamificationIndex K)`. Rewrite using `[normalizedValuation_natCast_prime p, map_pow, baseUnif, normalizedValuation_uniformizer hirr, ← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules. Establish `key : ∀ a b : K, normalizedValuation K a = normalizedValuation K b → nrm K (algebraMap K Ω a) = nrm K (algebraMap K Ω b)`.

Introduce `a b hab`. Establish `h1 : a ≤ᵥ b` using `(Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.le)`. Establish `h2 : b ≤ᵥ a` using `(Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.ge)`. Conclude with `le_antisymm ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle _ _).2 h1)) ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle _ _).2 h2))`. Establish `h` using `key _ _ hv`.

Rewrite `h` using `[map_natCast]`. Rewrite using `[h, map_pow, nrm_pow]`. Both sides reduce to the same expression.
-/
theorem nrm_natCast_prime_eq :
    nrm K (p : Ω) = baseUnifNrm K Ω ^ absRamificationIndex K := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  have hv : normalizedValuation K (p : K) =
      normalizedValuation K (((baseUnif K : 𝒪[K]) : K) ^ absRamificationIndex K) := by
    rw [normalizedValuation_natCast_prime p, map_pow, baseUnif, normalizedValuation_uniformizer hirr,
      ← WithZero.exp_nsmul]
    simp
  have key : ∀ a b : K, normalizedValuation K a = normalizedValuation K b →
      nrm K (algebraMap K Ω a) = nrm K (algebraMap K Ω b) := by
    intro a b hab
    have h1 : a ≤ᵥ b := (Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.le)
    have h2 : b ≤ᵥ a := (Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.ge)
    exact le_antisymm ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle _ _).2 h1))
      ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle _ _).2 h2))
  have h := key _ _ hv
  rw [map_natCast] at h
  rw [h, map_pow, nrm_pow]
  rfl

end Norm

section ResidueChar

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Use `(CharP.charP_iff_prime_eq_zero hp.out).mpr ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Establish `hq : ¬ ((1 : ℚ_[p]) ≤ᵥ (p : ℚ_[p]))`. Rewrite using `[Valuation.Compatible.vle_iff_le (v := Padic.mulValuation), GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one, Padic.norm_p]`. Conclude with `not_le.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))`.

Establish `hF : ¬ ((1 : F) ≤ᵥ (p : F))`. Introduce `h`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← ValuativeExtension.vle_iff_vle (A := ℚ_[p]) (B := F), map_one, map_natCast]`. Conclude with `h`.

Establish `e : (((p : 𝒪[F]) : F)) = (p : F)` using `by push_cast; rfl`. Rewrite using `[e, ← map_one (valuation F)]`. Conclude with `lt_of_not_ge fun h => hF ((Valuation.vle_iff_le (valuation F)).2 h)`.
-/
theorem charP_residueField_of_valuativeExtension (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra ℚ_[p] F]
    [ValuativeExtension ℚ_[p] F] : CharP 𝓀[F] p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hq : ¬ ((1 : ℚ_[p]) ≤ᵥ (p : ℚ_[p])) := by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
      GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one, Padic.norm_p]
    exact not_le.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hF : ¬ ((1 : F) ≤ᵥ (p : F)) := by
    intro h
    apply hq
    rw [← ValuativeExtension.vle_iff_vle (A := ℚ_[p]) (B := F), map_one, map_natCast]
    exact h
  have e : (((p : 𝒪[F]) : F)) = (p : F) := by push_cast; rfl
  rw [e, ← map_one (valuation F)]
  exact lt_of_not_ge fun h => hF ((Valuation.vle_iff_le (valuation F)).2 h)

end ResidueChar

end SenTateChar

end GroundTheory.PAdicHodge
