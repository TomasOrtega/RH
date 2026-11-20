import Mathlib
import GroundTheory.LocalFields.PrincipalUnitsModule

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Assume the negation of the conclusion as `hy`. Use `h (ord y + 1)` as an intermediate fact. Rewrite `this` using `[mem_valBall, normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_forall_mem_valBall {y : K} (h : ∀ N : ℤ, y ∈ valBall K N) : y = 0 := by
  by_contra hy
  have := h (ord y + 1)
  rw [mem_valBall, normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp] at this
  omega

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Conclude with `⟨0, by simp [hy]⟩`. Conclude with `⟨ord y, by rw [mem_valBall, normalizedValuation_eq_exp_ord hy]⟩`.
-/
theorem exists_mem_valBall (y : K) : ∃ M : ℤ, y ∈ valBall K M := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  · exact ⟨ord y, by rw [mem_valBall, normalizedValuation_eq_exp_ord hy]⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

/- English proof (translation)
Rewrite using `[mem_valBall, neg_zero, WithZero.exp_zero, ← map_one (normalizedValuation K), normalizedValuation_le_iff, map_one]`. Conclude with `CharZero.valuation_padicHom_padicInt_le_one K p t`.
-/
theorem padicHom_padicInt_mem_valBall_zero (t : ℤ_[p]) :
    CharZero.padicHom K p (t : ℚ_[p]) ∈ valBall K 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, ← map_one (normalizedValuation K),
    normalizedValuation_le_iff, map_one]
  exact CharZero.valuation_padicHom_padicInt_le_one K p t

include p in

/- English proof (translation)
Rewrite `hw` using `[mem_principalFiltration]`. Rewrite using `[padicLog_apply]`. Use `logSeries_mem_valBall p hw ?_` and prove the remaining obligations. Establish `hp2 : (2 : ℤ) ≤ p` using `by exact_mod_cast hp.out.two_le`. Establish `: (absRamificationIndex K : ℤ) ≤ k` using `by exact_mod_cast hk`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem padicLog_mem_valBall_of_mem {k : ℕ} (hk : absRamificationIndex K ≤ k)
    {w : Additive (unitFiltrationUnits K 1)} (hw : w ∈ principalFiltration K k) :
    padicLog K w ∈ valBall K (k + 1) := by
  rw [mem_principalFiltration] at hw
  rw [padicLog_apply]
  refine logSeries_mem_valBall p hw ?_
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have : (absRamificationIndex K : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_forall_mem_valBall fun N ↦ ?_` and prove the remaining obligations. Use `set e := absRamificationIndex K`. Establish `he` using `one_le_absRamificationIndex (K := K) p`. Take `⟨M, hM⟩` from `exists_mem_valBall (padicLog K u)`.

Use `set k : ℕ := N.toNat + M.natAbs + e + 1 with hk_def`. Use `set c : ℤ := ((a.appr k : ℕ) : ℤ)`. Establish `hac` using `dvd_sub_appr p k a`. Take `⟨t, ht⟩` from `hac`. Establish `hw` using `smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u`.

Establish `h1` using `padicLog_mem_valBall_of_mem p (by omega : e ≤ k) hw`. Rewrite `h1` using `[map_sub, map_zsmul, zsmul_eq_mul]`. Establish `h2 : CharZero.padicHom K p (a : ℚ_[p]) - (c : K) = ((p ^ k : ℕ) : K) * CharZero.padicHom K p (t : ℚ_[p])`. Use `congrArg (fun z : ℤ_[p] ↦ CharZero.padicHom K p (z : ℚ_[p])) ht` as an intermediate fact. Simplify using `only [PadicInt.coe_sub, PadicInt.coe_intCast, map_sub, map_intCast, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, map_mul, map_pow, map_natCast] at this`.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u ∈ valBall K (e * k + 0 + M)`. Rewrite using `[h2]`.

Conclude with `mul_mem_valBall (mul_mem_valBall (natCast_prime_pow_mem_valBall p k) (padicHom_padicInt_mem_valBall_zero p t)) hM`. Establish `heq : padicLog K (a • u) - CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u = (padicLog K (a • u) - (c : K) * padicLog K u) - (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u` using `by ring`. Rewrite using `[heq]`. Establish `hNt` using `Int.self_le_toNat N`. Establish `hMa` using `neg_abs_le M`.

Establish `hMa'` using `abs_nonneg M`. Establish `hN1 : N ≤ (k : ℤ) + 1` using `by rw [hk_def]; push_cast; omega`. Establish `hN2 : N ≤ (e : ℤ) * k + 0 + M`. Establish `: (k : ℤ) ≤ e * k`. Establish `: (1 : ℤ) ≤ e` using `by exact_mod_cast he`.

Use polynomial arithmetic with `[(by positivity : (0 : ℤ) ≤ k)]`. Rewrite `this`, the goal using `[hk_def]`. Move the coercions through the operations in `at this ⊢`. Use linear arithmetic over natural numbers and integers. Conclude with `sub_mem (valBall_antitone hN1 h1) (valBall_antitone hN2 h3)`.
-/
theorem padicLog_smul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (a • u) = CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_valBall fun N ↦ ?_
  set e := absRamificationIndex K
  have he := one_le_absRamificationIndex (K := K) p
  obtain ⟨M, hM⟩ := exists_mem_valBall (padicLog K u)
  set k : ℕ := N.toNat + M.natAbs + e + 1 with hk_def
  set c : ℤ := ((a.appr k : ℕ) : ℤ)
  have hac := dvd_sub_appr p k a
  obtain ⟨t, ht⟩ := hac
  have hw := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h1 := padicLog_mem_valBall_of_mem p (by omega : e ≤ k) hw
  rw [map_sub, map_zsmul, zsmul_eq_mul] at h1
  have h2 : CharZero.padicHom K p (a : ℚ_[p]) - (c : K) =
      ((p ^ k : ℕ) : K) * CharZero.padicHom K p (t : ℚ_[p]) := by
    have := congrArg (fun z : ℤ_[p] ↦ CharZero.padicHom K p (z : ℚ_[p])) ht
    simp only [PadicInt.coe_sub, PadicInt.coe_intCast, map_sub, map_intCast, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_natCast, map_mul, map_pow, map_natCast] at this
    rw [this]; push_cast; ring
  have h3 : (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u ∈
      valBall K (e * k + 0 + M) := by
    rw [h2]
    exact mul_mem_valBall (mul_mem_valBall (natCast_prime_pow_mem_valBall p k)
      (padicHom_padicInt_mem_valBall_zero p t)) hM
  have heq : padicLog K (a • u) - CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u =
      (padicLog K (a • u) - (c : K) * padicLog K u) -
        (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u := by ring
  rw [heq]
  have hNt := Int.self_le_toNat N
  have hMa := neg_abs_le M
  have hMa' := abs_nonneg M
  have hN1 : N ≤ (k : ℤ) + 1 := by rw [hk_def]; push_cast; omega
  have hN2 : N ≤ (e : ℤ) * k + 0 + M := by
    have : (k : ℤ) ≤ e * k := by
      have : (1 : ℤ) ≤ e := by exact_mod_cast he
      nlinarith [(by positivity : (0 : ℤ) ≤ k)]
    rw [hk_def] at this ⊢; push_cast at this ⊢; omega
  exact sub_mem (valBall_antitone hN1 h1) (valBall_antitone hN2 h3)

end GroundTheory.LocalField
