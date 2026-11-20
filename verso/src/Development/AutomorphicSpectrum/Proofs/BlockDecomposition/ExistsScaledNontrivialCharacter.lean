import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual

open ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CharConductor

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ a c ha hc`. Establish `hA : MulArchimedean (ValueGroupWithZero k)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨γ, hγ, hball⟩` from `GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ`. Establish `hc0 : valuation k c ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[map_eq_zero]`. Conclude with `hc (by rw [h0, AddChar.map_zero_eq_one])`. Take `⟨m, hm⟩` from `exists_pow_lt₀ ha (Units.mk0 (γ / valuation k c) (div_ne_zero hγ hc0))`. Rewrite `hm` using `[Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc0)]`. Establish `hex : ∃ r : ℕ, ∀ μ ∈ 𝒪[k], ψ (μ * a ^ r * c) = 1`.

Use `⟨m, fun μ hμ => hball _ ?_⟩` and prove the remaining obligations. Establish `hμ1 : valuation k μ ≤ 1` using `(Valuation.mem_integer_iff _ _).mp hμ`. Rewrite using `[map_mul, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hfind` using `Nat.find_spec hex`.

Establish `hpos : Nat.find hex ≠ 0`. Introduce `h0`. Rewrite `hfind` using `[h0]`. Conclude with `hc (by simpa using hfind 1 (one_mem _))`. Take `⟨r, hr⟩` from `Nat.exists_eq_succ_of_ne_zero hpos`.

Establish `hmin` using `Nat.find_min hex (m := r) (by omega)`. Use `push Not at hmin`. Take `⟨μ, hμ, hne⟩` from `hmin`. Use `⟨μ * a ^ r * c, hne, ⟨r, μ, hμ, rfl⟩, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h` using `hfind (s * μ) (mul_mem hs hμ)`.

Rewrite `h` using `[hr]`. Establish `e : s * a * (μ * a ^ r * c) = s * μ * a ^ (r + 1) * c` using `by ring`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_conductor_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k),
    valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧
      ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  intro k _ _ _ _ ψ hψ a c ha hc
  classical
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hc0 : valuation k c ≠ 0 := by
    intro h0
    rw [map_eq_zero] at h0
    exact hc (by rw [h0, AddChar.map_zero_eq_one])
  obtain ⟨m, hm⟩ := exists_pow_lt₀ ha (Units.mk0 (γ / valuation k c) (div_ne_zero hγ hc0))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc0)] at hm
  have hex : ∃ r : ℕ, ∀ μ ∈ 𝒪[k], ψ (μ * a ^ r * c) = 1 := by
    refine ⟨m, fun μ hμ => hball _ ?_⟩
    have hμ1 : valuation k μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
    rw [map_mul, map_mul, map_pow]
    calc valuation k μ * valuation k a ^ m * valuation k c
        ≤ 1 * valuation k a ^ m * valuation k c := by gcongr
      _ = valuation k a ^ m * valuation k c := by rw [one_mul]
      _ < γ := hm
  have hfind := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hfind
    exact hc (by simpa using hfind 1 (one_mem _))
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin := Nat.find_min hex (m := r) (by omega)
  push Not at hmin
  obtain ⟨μ, hμ, hne⟩ := hmin
  refine ⟨μ * a ^ r * c, hne, ⟨r, μ, hμ, rfl⟩, fun s hs => ?_⟩
  have h := hfind (s * μ) (mul_mem hs hμ)
  rw [hr] at h
  have e : s * a * (μ * a ^ r * c) = s * μ * a ^ (r + 1) * c := by ring
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CharConductor
