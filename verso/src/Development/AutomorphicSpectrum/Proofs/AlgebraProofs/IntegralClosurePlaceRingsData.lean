import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsPowPrincipal
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Use `hR z ⟨Polynomial.X ^ m - Polynomial.C ⟨z ^ m, h⟩, Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]`. Conclude with `sub_eq_zero.2 rfl`.
-/
theorem mem_of_pow_mem_of_integrally_closed {Ω : Type} [Field Ω] (R : Subring Ω)
    (hR : ∀ z : Ω, IsIntegral R z → z ∈ R) {z : Ω} {m : ℕ} (hm : 0 < m) (h : z ^ m ∈ R) :
    z ∈ R := by
  refine hR z ⟨Polynomial.X ^ m - Polynomial.C ⟨z ^ m, h⟩, Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  exact sub_eq_zero.2 rfl

/- English proof (translation)
Rewrite using `[map_pow, map_zpow₀, hπ, map_pow, hα, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using `only [smul_eq_mul, nsmul_eq_mul]`. Take the linear combination `-h`.
-/
theorem valuation_pow_zpow_eq_of_mul_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {π α : F} {n k : ℤ} {m M : ℕ} (hπ : v.valuation F π = WithZero.exp (-1 : ℤ))
    (hα : v.valuation F α = WithZero.exp (-k)) (h : n * M = m * k) :
    v.valuation F ((π ^ n) ^ M) = v.valuation F (α ^ m) := by
  rw [map_pow, map_zpow₀, hπ, map_pow, hα, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  linear_combination -h

/- English proof (translation)
Introduce `F Ω X _ _ _ φ R s pl r hR hgen hsp`. Take `⟨M, α, hM, hα0, hval⟩` from `exists_pow_principal F r`. Use `⟨M, α, hM, hα0, hval, fun x => ?_⟩` and prove the remaining obligations. Consider the cases of `hx : pl x with`. Consider the case `none`.

Take `⟨hφ, hs, -, hsi⟩` from `hgen x hx`. Establish `hαi : (φ α)⁻¹ ∈ R x`. Rewrite using `[← map_inv₀]`. Conclude with `hφ _`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[div_eq_mul_inv]`. Conclude with `(R x).mul_mem ((R x).pow_mem hs M) hαi`. Rewrite using `[div_eq_mul_inv, ← inv_pow]`. Conclude with `(R x).mul_mem (hφ α) ((R x).pow_mem hsi M)`. Consider the case `some v`.

Take `⟨hφ, m, n, π, hm, hn, hπ, hs0, h1, h2⟩` from `hsp x v hx`. Take `⟨k, hk, hαv⟩` from `hval v`. Establish `hkey : n * (M : ℤ) = m * k`. Establish `: ((n * M : ℤ) : ℚ) = ((m * k : ℤ) : ℚ)`. Use `push_cast`.

Rewrite using `[hn, hk]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Establish `hv` using `valuation_pow_zpow_eq_of_mul_eq v hπ hαv hkey`. Establish `hπ0 : π ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.coe_ne_zero hπ.symm`. Establish `hφπ : φ π ≠ 0` using `(map_ne_zero φ).2 hπ0`. Establish `hφα : φ α ≠ 0` using `(map_ne_zero φ).2 hα0`.

Establish `hP : φ π ^ n ≠ 0` using `zpow_ne_zero _ hφπ`. Establish `hβ : v.valuation F ((π ^ n) ^ M / α ^ m) = 1`. Rewrite using `[map_div₀, hv, div_self]`. Conclude with `(Valuation.ne_zero_iff _).2 (pow_ne_zero _ hα0)`. Establish `hβ1 : φ ((π ^ n) ^ M / α ^ m) ∈ R x` using `hφ _ hβ.le`.

Establish `hβ2 : φ ((π ^ n) ^ M / α ^ m)⁻¹ ∈ R x` using `hφ _ (by rw [map_inv₀, hβ, inv_one])`. Prove the components needed by the constructor for the conclusion. Apply `mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm` to reduce the goal to its premises. Establish `he : (s x ^ M / φ α) ^ m = (s x ^ m / φ π ^ n) ^ M * φ ((π ^ n) ^ M / α ^ m)`. Simplify using `only [map_div₀, map_pow, map_zpow₀]`.

Rewrite using `[div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, div_mul_div_comm, mul_comm (s x ^ (m * M)), mul_div_mul_left _ _ (pow_ne_zero _ hP)]`. Rewrite using `[he]`. Conclude with `(R x).mul_mem ((R x).pow_mem h1 M) hβ1`. Apply `mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm` to reduce the goal to its premises. Establish `he : (φ α / s x ^ M) ^ m = (φ π ^ n / s x ^ m) ^ M * φ ((π ^ n) ^ M / α ^ m)⁻¹`.

Simplify using `only [map_inv₀, map_div₀, map_pow, map_zpow₀]`. Rewrite using `[div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, inv_div, div_mul_div_comm, mul_comm ((φ π ^ n) ^ M), mul_div_mul_right _ _ (pow_ne_zero _ hP)]`. Rewrite using `[he]`. Conclude with `(R x).mul_mem ((R x).pow_mem h2 M) hβ2`.
-/
theorem exists_global_generator : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  intro F Ω X _ _ _ φ R s pl r hR hgen hsp
  obtain ⟨M, α, hM, hα0, hval⟩ := exists_pow_principal F r
  refine ⟨M, α, hM, hα0, hval, fun x => ?_⟩
  cases hx : pl x with
  | none =>
    obtain ⟨hφ, hs, -, hsi⟩ := hgen x hx
    have hαi : (φ α)⁻¹ ∈ R x := by
      rw [← map_inv₀]
      exact hφ _
    constructor
    · rw [div_eq_mul_inv]
      exact (R x).mul_mem ((R x).pow_mem hs M) hαi
    · rw [div_eq_mul_inv, ← inv_pow]
      exact (R x).mul_mem (hφ α) ((R x).pow_mem hsi M)
  | some v =>
    obtain ⟨hφ, m, n, π, hm, hn, hπ, hs0, h1, h2⟩ := hsp x v hx
    obtain ⟨k, hk, hαv⟩ := hval v
    have hkey : n * (M : ℤ) = m * k := by
      have : ((n * M : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
        push_cast
        rw [hn, hk]
        ring
      exact_mod_cast this
    have hv := valuation_pow_zpow_eq_of_mul_eq v hπ hαv hkey
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.coe_ne_zero hπ.symm
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    have hφα : φ α ≠ 0 := (map_ne_zero φ).2 hα0
    have hP : φ π ^ n ≠ 0 := zpow_ne_zero _ hφπ
    have hβ : v.valuation F ((π ^ n) ^ M / α ^ m) = 1 := by
      rw [map_div₀, hv, div_self]
      exact (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hα0)
    have hβ1 : φ ((π ^ n) ^ M / α ^ m) ∈ R x := hφ _ hβ.le
    have hβ2 : φ ((π ^ n) ^ M / α ^ m)⁻¹ ∈ R x := hφ _ (by rw [map_inv₀, hβ, inv_one])
    constructor
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (s x ^ M / φ α) ^ m = (s x ^ m / φ π ^ n) ^ M * φ ((π ^ n) ^ M / α ^ m) := by
        simp only [map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, div_mul_div_comm,
          mul_comm (s x ^ (m * M)), mul_div_mul_left _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h1 M) hβ1
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (φ α / s x ^ M) ^ m = (φ π ^ n / s x ^ m) ^ M * φ ((π ^ n) ^ M / α ^ m)⁻¹ := by
        simp only [map_inv₀, map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, inv_div, div_mul_div_comm,
          mul_comm ((φ π ^ n) ^ M), mul_div_mul_right _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h2 M) hβ2

end GlobalTheory.CompanionTheory.Ar.Flat
