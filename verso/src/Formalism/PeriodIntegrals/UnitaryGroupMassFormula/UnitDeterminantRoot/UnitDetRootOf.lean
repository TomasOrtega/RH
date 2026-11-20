import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

/- English proof (translation)
Introduce `a b c d ha hd lam hlam hOK m _ _ Λa hSD hθ hi1 hi2`. Establish `hH : Hyp a b c d ha hd lam hlam m Λa` using `⟨hOK, hSD, hθ, hi1, hi2⟩`. Take `⟨γ, hγK, hγ0, n, hn, hγ⟩` from `h3 a b c d ha hd lam hlam m Λa hH`. Establish `hγc0 : conj γ ≠ 0` using `(map_ne_zero (starRingEnd ℂ)).mpr hγ0`. Establish `hβK : γ / conj γ ∈ KF b d` using `div_mem hγK (h6 b d γ hγK)`.

Establish `hββ : γ / conj γ * conj (γ / conj γ) = 1`. Rewrite using `[map_div₀, Complex.conj_conj]`. Clear the denominators using the available nonvanishing facts. Take `⟨κ, hκN, hκalg, hκσ⟩` from `h5 a b c d hOK (γ / conj γ) hβK hββ (4 * n) (by omega)`. Use `⟨κ, ?_, hκalg, hκσ, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hκN` using `[zero_pow (by omega), eq_comm, inv_eq_zero, div_eq_zero_iff]`. Conclude with `hκN.elim hγ0 hγc0`. Introduce `l _ ι δ hIso hidx1 hnl hidx2`. Establish `hA : admitted a b d ha hd lam hlam m Λa δ` using `⟨hIso, hidx1, hidx2⟩`.

Establish `hEq` using `h2 a b c d ha hd lam hlam m Λa hH l δ hA hnl`. Establish `hU` using `hγ l δ hA hEq`. Establish `n1` using `h4 l ι _ hU`. Establish `n2` using `h4 l ι _ (h7 l _ hU)`. Take `⟨-, hdd⟩` from `h1 a b c d ha hd lam hlam m Λa hH δ hA`.

Use `set D := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hD`. Establish `hD0 : D ≠ 0`. Introduce and unpack `h`. Rewrite `hdd` using `[h, zero_mul]`. Conclude with `zero_ne_one hdd`.

Establish `hDc : conj D = D⁻¹` using `eq_inv_of_mul_eq_one_right hdd`. Establish `hu0 : 0 < ‖ι D‖` using `norm_pos_iff.mpr ((map_ne_zero ι).mpr hD0)`. Establish `hDc0 : conj D ≠ 0` using `(map_ne_zero (starRingEnd ℂ)).mpr hD0`. Establish `n1' : ‖ι γ‖ = ‖ι D‖ ^ n`. Establish `e : γ = (γ / D ^ n) * D ^ n` using `by field_simp`.

Rewrite using `[e, map_mul, norm_mul, n1, one_mul, map_pow, norm_pow]`. Establish `n2' : ‖ι (conj γ)‖ = ‖ι D‖⁻¹ ^ n`. Establish `e : conj γ = conj (γ / D ^ n) * (conj D) ^ n`. Rewrite using `[map_div₀, map_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, map_mul, norm_mul, n2, one_mul, map_pow, norm_pow, hDc, map_inv₀, norm_inv]`. Establish `e3 : ‖ι κ‖ ^ (4 * n) = ‖ι (conj γ)‖ / ‖ι γ‖`. Rewrite using `[← norm_pow, ← map_pow, hκN, inv_div, map_div₀, norm_div]`. Establish `ht : (‖ι κ‖ ^ 2 * ‖ι D‖) ^ (2 * n) = 1`. Rewrite using `[mul_pow, ← pow_mul, show 2 * (2 * n) = 4 * n by ring, e3, n1', n2', inv_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `(pow_eq_one_iff_of_nonneg (by positivity) (by omega)).mp ht`.
-/
theorem unitDetRoot_of (h1 : DetInK) (h2 : LocalStd) (h3 : GlobalLUnit) (h4 : NormOne)
    (h5 : RootStep) (h6 : ConjMem) (h7 : ConjLUnit) : PI.UnitDetRoot := by
  intro a b c d ha hd lam hlam hOK m _ _ Λa hSD hθ hi1 hi2
  have hH : Hyp a b c d ha hd lam hlam m Λa := ⟨hOK, hSD, hθ, hi1, hi2⟩
  obtain ⟨γ, hγK, hγ0, n, hn, hγ⟩ := h3 a b c d ha hd lam hlam m Λa hH
  have hγc0 : conj γ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hγ0
  have hβK : γ / conj γ ∈ KF b d := div_mem hγK (h6 b d γ hγK)
  have hββ : γ / conj γ * conj (γ / conj γ) = 1 := by
    rw [map_div₀, Complex.conj_conj]
    field_simp
  obtain ⟨κ, hκN, hκalg, hκσ⟩ := h5 a b c d hOK (γ / conj γ) hβK hββ (4 * n) (by omega)
  refine ⟨κ, ?_, hκalg, hκσ, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega), eq_comm, inv_eq_zero, div_eq_zero_iff] at hκN
    exact hκN.elim hγ0 hγc0
  · intro l _ ι δ hIso hidx1 hnl hidx2
    have hA : admitted a b d ha hd lam hlam m Λa δ := ⟨hIso, hidx1, hidx2⟩
    have hEq := h2 a b c d ha hd lam hlam m Λa hH l δ hA hnl
    have hU := hγ l δ hA hEq
    have n1 := h4 l ι _ hU
    have n2 := h4 l ι _ (h7 l _ hU)
    obtain ⟨-, hdd⟩ := h1 a b c d ha hd lam hlam m Λa hH δ hA
    set D := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hD
    have hD0 : D ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hdd
      exact zero_ne_one hdd
    have hDc : conj D = D⁻¹ := eq_inv_of_mul_eq_one_right hdd
    have hu0 : 0 < ‖ι D‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hD0)
    have hDc0 : conj D ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hD0
    have n1' : ‖ι γ‖ = ‖ι D‖ ^ n := by
      have e : γ = (γ / D ^ n) * D ^ n := by field_simp
      rw [e, map_mul, norm_mul, n1, one_mul, map_pow, norm_pow]
    have n2' : ‖ι (conj γ)‖ = ‖ι D‖⁻¹ ^ n := by
      have e : conj γ = conj (γ / D ^ n) * (conj D) ^ n := by
        rw [map_div₀, map_pow]
        field_simp
      rw [e, map_mul, norm_mul, n2, one_mul, map_pow, norm_pow, hDc, map_inv₀, norm_inv]
    have e3 : ‖ι κ‖ ^ (4 * n) = ‖ι (conj γ)‖ / ‖ι γ‖ := by
      rw [← norm_pow, ← map_pow, hκN, inv_div, map_div₀, norm_div]
    have ht : (‖ι κ‖ ^ 2 * ‖ι D‖) ^ (2 * n) = 1 := by
      rw [mul_pow, ← pow_mul, show 2 * (2 * n) = 4 * n by ring, e3, n1', n2', inv_pow]
      field_simp
      ring
    exact (pow_eq_one_iff_of_nonneg (by positivity) (by omega)).mp ht

end PI.UnitaryGroupMassFormula.UnitDetRoot
