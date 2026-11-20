import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldTarget
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.FinPlaceApproxPos

/- English proof (translation)
Take `⟨a₀, ha₀⟩` from `GlobalTheory.FinPlaceApprox.approx_target F T t M`. Use `set J : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ M with hJ`. Establish `hJ0 : J ≠ ⊥`. Rewrite using `[hJ, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Introduce `v _`.

Conclude with `pow_ne_zero _ v.ne_bot`. Use `set d : ℕ := Ideal.absNorm J with hd`. Establish `hd0 : d ≠ 0`. Rewrite using `[hd]`. Conclude with `fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)`.

Establish `hdJ : ((d : ℤ) : 𝓞 F) ∈ J`. Simplify `Ideal.absNorm_mem J` using `[hd]`. Establish `hJv : ∀ v ∈ T, J ≤ v.asIdeal ^ M` using `fun v hv => Ideal.prod_le_inf.trans (Finset.inf_le hv)`. Take `⟨B, hB⟩` from `(Set.finite_range (fun φ : F →+* ℝ => |φ a₀|)).bddAbove`. Use `set N : ℕ := ⌈B⌉₊ + 1 with hN`.

Use `⟨a₀ + (N * d : ℕ), fun v hv => ?_, fun φ => ?_⟩` and prove the remaining obligations. Establish `hmem : ((N * d : ℕ) : 𝓞 F) ∈ v.asIdeal ^ M`. Apply `hJv v hv` to reduce the goal to its premises. Establish `: ((N * d : ℕ) : 𝓞 F) = (N : 𝓞 F) * ((d : ℤ) : 𝓞 F)` using `by push_cast; ring`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ hdJ`. Establish `hval : v.valuation F ((N * d : ℕ) : F) ≤ WithZero.exp (-(M : ℤ))`. Establish `: ((N * d : ℕ) : F) = algebraMap (𝓞 F) F ((N * d : ℕ) : 𝓞 F)` using `by simp`. Rewrite using `[this, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(v.intValuation_le_pow_iff_mem _ _).2 hmem`.

Establish `: a₀ + ((N * d : ℕ) : F) - t v = (a₀ - t v) + ((N * d : ℕ) : F)` using `by ring`. Rewrite using `[this]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le (ha₀ v hv) hval)`. Establish `h1 : φ a₀ ≥ -B`. Use `hB ⟨φ, rfl⟩` as an intermediate fact.

Use `neg_abs_le (φ a₀)` as an intermediate fact. Simplify using `only at *`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdpos : (1 : ℝ) ≤ d` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0`. Establish `hNB : B < N`.

Rewrite using `[hN]`. Use `push_cast`. Conclude with `lt_of_le_of_lt (Nat.le_ceil B) (by linarith)`. Establish `hN0 : (0 : ℝ) ≤ N` using `by positivity`. Rewrite using `[map_add, map_natCast]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_approx_totally_positive (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ φ : F →+* ℝ, 0 < φ a := by
  classical
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.FinPlaceApprox.approx_target F T t M
  set J : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ M with hJ
  have hJ0 : J ≠ ⊥ := by
    rw [hJ, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  set d : ℕ := Ideal.absNorm J with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hdJ : ((d : ℤ) : 𝓞 F) ∈ J := by
    simpa [hd] using Ideal.absNorm_mem J
  have hJv : ∀ v ∈ T, J ≤ v.asIdeal ^ M := fun v hv =>
    Ideal.prod_le_inf.trans (Finset.inf_le hv)
  obtain ⟨B, hB⟩ := (Set.finite_range (fun φ : F →+* ℝ => |φ a₀|)).bddAbove
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  refine ⟨a₀ + (N * d : ℕ), fun v hv => ?_, fun φ => ?_⟩
  · have hmem : ((N * d : ℕ) : 𝓞 F) ∈ v.asIdeal ^ M := by
      apply hJv v hv
      have : ((N * d : ℕ) : 𝓞 F) = (N : 𝓞 F) * ((d : ℤ) : 𝓞 F) := by push_cast; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hdJ
    have hval : v.valuation F ((N * d : ℕ) : F) ≤ WithZero.exp (-(M : ℤ)) := by
      have : ((N * d : ℕ) : F) = algebraMap (𝓞 F) F ((N * d : ℕ) : 𝓞 F) := by simp
      rw [this, HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
    have : a₀ + ((N * d : ℕ) : F) - t v = (a₀ - t v) + ((N * d : ℕ) : F) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (ha₀ v hv) hval)
  · have h1 : φ a₀ ≥ -B := by
      have := hB ⟨φ, rfl⟩
      have := neg_abs_le (φ a₀)
      simp only at *
      linarith
    have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    have hNB : B < N := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil B) (by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [map_add, map_natCast]
    push_cast
    nlinarith

/- English proof (translation)
Introduce `F _ _ T t M` and use `exists_approx_totally_positive F T t M`.
-/
theorem approxpos_target : ∀ (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ),
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a :=
  fun F _ _ T t M => exists_approx_totally_positive F T t M

end GlobalTheory.FinPlaceApproxPos
