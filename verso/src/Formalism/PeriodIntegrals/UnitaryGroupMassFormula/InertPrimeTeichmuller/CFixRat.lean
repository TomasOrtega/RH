import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.NormLeOneOfIntegralInt

open NumberField

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Set `f : K →ₐ[ℚ] K` to `c.toRatAlgHom`. Set `e : K ≃ₐ[ℚ] K` to `AlgEquiv.ofBijective f (AlgHom.bijective f)`. Establish `hcard : Nat.card (K ≃ₐ[ℚ] K) ≤ 2`. Rewrite using `[← hK, Nat.card_congr (algEquivEquivAlgHom ℚ K).toEquiv]`. Conclude with `card_algHom_le_finrank ℚ K K`.

Establish `hpos : 0 < Nat.card (K ≃ₐ[ℚ] K)` using `Nat.card_pos`. Establish `h1 : e ^ Nat.card (K ≃ₐ[ℚ] K) = 1` using `pow_card_eq_one'`. Establish `he : e ^ 2 = 1`. Break down `(by omega : Nat.card (K ≃ₐ[ℚ] K) = 1 ∨ Nat.card (K ≃ₐ[ℚ] K) = 2) with h | h` into its components or cases. Rewrite `h1` using `[h, pow_one]`.

Rewrite using `[h1, one_pow]`. Rewrite `h1` using `[h]`. Then use the resulting hypothesis. Use `DFunLike.congr_fun he x` as an intermediate fact. Rewrite `this` using `[pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]`. Conclude with `this`.
-/
theorem c_invol (hK : Module.finrank ℚ K = 2) (c : K →+* K) (x : K) : c (c x) = x := by
  let f : K →ₐ[ℚ] K := c.toRatAlgHom
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofBijective f (AlgHom.bijective f)
  have hcard : Nat.card (K ≃ₐ[ℚ] K) ≤ 2 := by
    rw [← hK, Nat.card_congr (algEquivEquivAlgHom ℚ K).toEquiv]
    exact card_algHom_le_finrank ℚ K K
  have hpos : 0 < Nat.card (K ≃ₐ[ℚ] K) := Nat.card_pos
  have h1 : e ^ Nat.card (K ≃ₐ[ℚ] K) = 1 := pow_card_eq_one'
  have he : e ^ 2 = 1 := by
    rcases (by omega : Nat.card (K ≃ₐ[ℚ] K) = 1 ∨ Nat.card (K ≃ₐ[ℚ] K) = 2) with h | h
    · rw [h, pow_one] at h1; rw [h1, one_pow]
    · rwa [h] at h1
  have := DFunLike.congr_fun he x
  rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] at this
  exact this

/- English proof (translation)
Set `D : K →ₗ[ℚ] K` to `c.toRatAlgHom.toLinearMap - LinearMap.id`. Establish `hD : ∀ z, D z = c z - z` using `fun z => rfl`. Establish `hS : LinearMap.ker D ≠ ⊤`. Take `⟨x, hx⟩` from `hc`. Introduce `h`.

Establish `hm : x ∈ LinearMap.ker D` using `h ▸ Submodule.mem_top`. Rewrite `hm` using `[LinearMap.mem_ker, hD, sub_eq_zero]`. Conclude with `hx hm`. Establish `hlt : Module.finrank ℚ (LinearMap.ker D) < 2` using `hK ▸ Submodule.finrank_lt hS`. Establish `hle : (ℚ ∙ (1 : K)) ≤ LinearMap.ker D`.

Rewrite using `[Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hD, map_one, sub_self]`. Establish `heq : (ℚ ∙ (1 : K)) = LinearMap.ker D` using `Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton one_ne_zero]; omega)`. Establish `hyS : y ∈ LinearMap.ker D` using `by rw [LinearMap.mem_ker, hD, hy, sub_self]`. Rewrite `hyS` using `[← heq, Submodule.mem_span_singleton]`. Take `⟨r, hr⟩` from `hyS`.

Conclude with `⟨r, by rw [← hr, Rat.smul_def, mul_one]⟩`.
-/
theorem c_fix_rat (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) {y : K}
    (hy : c y = y) : ∃ r : ℚ, (r : K) = y := by
  let D : K →ₗ[ℚ] K := c.toRatAlgHom.toLinearMap - LinearMap.id
  have hD : ∀ z, D z = c z - z := fun z => rfl
  have hS : LinearMap.ker D ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hc
    intro h
    have hm : x ∈ LinearMap.ker D := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hD, sub_eq_zero] at hm
    exact hx hm
  have hlt : Module.finrank ℚ (LinearMap.ker D) < 2 :=
    hK ▸ Submodule.finrank_lt hS
  have hle : (ℚ ∙ (1 : K)) ≤ LinearMap.ker D := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hD, map_one, sub_self]
  have heq : (ℚ ∙ (1 : K)) = LinearMap.ker D :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton one_ne_zero]; omega)
  have hyS : y ∈ LinearMap.ker D := by rw [LinearMap.mem_ker, hD, hy, sub_self]
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨r, hr⟩ := hyS
  exact ⟨r, by rw [← hr, Rat.smul_def, mul_one]⟩

/- English proof (translation)
Establish `hfix : c ((a : K) + c a) = (a : K) + c a` using `by rw [map_add, c_invol hK c, add_comm]`. Take `⟨r, hr⟩` from `c_fix_rat hK c hc hfix`. Establish `hint : IsIntegral ℤ (algebraMap ℚ K r)`. Rewrite using `[eq_ratCast, hr]`. Use `(a + RingOfIntegers.mapRingHom c a).isIntegral_coe` as an intermediate fact.

Simplify `this` using `[RingOfIntegers.mapRingHom_apply]`. Rewrite `hint` using `[isIntegral_algebraMap_iff (algebraMap ℚ K).injective, IsIntegrallyClosed.isIntegral_iff]`. Take `⟨n, hn⟩` from `hint`. Use `⟨n, RingOfIntegers.ext ?_⟩` and prove the remaining obligations. Establish `h2 : ((a + RingOfIntegers.mapRingHom c a : 𝓞 K) : K) = (a : K) + c a`.

Simplify using `[RingOfIntegers.mapRingHom_apply]`. Rewrite using `[h2, ← hr, ← hn]`. Simplify using the standard rewrite rules.
-/
theorem add_c_int (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (a : 𝓞 K) :
    ∃ n : ℤ, a + RingOfIntegers.mapRingHom c a = (n : 𝓞 K) := by
  have hfix : c ((a : K) + c a) = (a : K) + c a := by rw [map_add, c_invol hK c, add_comm]
  obtain ⟨r, hr⟩ := c_fix_rat hK c hc hfix
  have hint : IsIntegral ℤ (algebraMap ℚ K r) := by
    rw [eq_ratCast, hr]
    have := (a + RingOfIntegers.mapRingHom c a).isIntegral_coe
    simpa [RingOfIntegers.mapRingHom_apply] using this
  rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective,
    IsIntegrallyClosed.isIntegral_iff] at hint
  obtain ⟨n, hn⟩ := hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  have h2 : ((a + RingOfIntegers.mapRingHom c a : 𝓞 K) : K) = (a : K) + c a := by
    simp [RingOfIntegers.mapRingHom_apply]
  rw [h2, ← hr, ← hn]
  simp

end PI.OkpW
