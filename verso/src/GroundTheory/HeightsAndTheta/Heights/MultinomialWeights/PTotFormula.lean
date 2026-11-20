import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intFl_apply (d : IndexData) (G : XPoly d) :
    intFl d G = flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N G := rfl

/- English proof (translation)
Rewrite using `[intFl_apply, hK d.f d.N k σ G hk1 hkN, mul_zero]`.
-/
theorem intFl_powerSum_mul (hK : RestTerms.FlagIntegralKillsPowerSums.Statement) (d : IndexData)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ d.N) (σ : Fin d.f) (G : XPoly d) :
    intFl d (RestTerms.blockPowerSum d.f d.N k σ * G) = 0 := by
  rw [intFl_apply, hK d.f d.N k σ G hk1 hkN, mul_zero]

def totalDeriv (d : IndexData) (τ : Fin d.f) : Derivation ℚ (XPoly d) (XPoly d) :=
  ∑ i : Fin d.N, pderiv (τ, i)

/- English proof (translation)
Rewrite using `[totalDeriv, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem totalDeriv_apply (d : IndexData) (τ : Fin d.f) (G : XPoly d) :
    totalDeriv d τ G = ∑ i : Fin d.N, pderiv (τ, i) G := by
  rw [totalDeriv, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

/- English proof (translation)
Rewrite using `[totalDeriv_apply]`. Simplify using `only [RestTerms.blockPowerSum, map_sum, Derivation.leibniz_pow, pderiv_X]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[nsmul_eq_mul, smul_eq_mul]`. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_` and prove the remaining obligations. Establish `: ((σ, i') : Fin d.f × Fin d.N) ≠ (τ, i)` using `fun e => h (congrArg Prod.fst e)`. Simplify using `[this]`.
-/
theorem totalDeriv_blockPowerSum (d : IndexData) (τ σ : Fin d.f) (k : ℕ) :
    totalDeriv d τ (RestTerms.blockPowerSum d.f d.N k σ) =
      if σ = τ then C (k : ℚ) * RestTerms.blockPowerSum d.f d.N (k - 1) τ else 0 := by
  classical
  rw [totalDeriv_apply]
  simp only [RestTerms.blockPowerSum, map_sum, Derivation.leibniz_pow, pderiv_X]
  split_ifs with h
  · subst h
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [nsmul_eq_mul, smul_eq_mul]
    · intro b _ hb
      simp [hb]
    · simp
  · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
    have : ((σ, i') : Fin d.f × Fin d.N) ≠ (τ, i) := fun e => h (congrArg Prod.fst e)
    simp [this]

/- English proof (translation)
Introduce `d τ F Q _ _ hdec`. Unfold `RestTerms.IsPowerSumDecomposition at hdec`. Substitute `hdec` using the available equality. Establish `hN` using `d.two_le_N`. Establish `key : ∀ k ∈ Icc 1 d.N, ∀ σ : Fin d.f, intFl d (totalDeriv d τ (RestTerms.blockPowerSum d.f d.N k σ * Q k σ)) = if σ = τ then (k : ℚ) * intFl d (RestTerms.blockPowerSum d.f d.N (k - 1) τ * Q k τ) else 0`.

Introduce `k hk σ`. Rewrite `hk` using `[Finset.mem_Icc]`. Rewrite using `[Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, intFl_powerSum_mul hK d hk.1 hk.2, zero_add, totalDeriv_blockPowerSum]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[show Q k σ * (C (k : ℚ) * RestTerms.blockPowerSum d.f d.N (k - 1) σ) = (k : ℚ) • (RestTerms.blockPowerSum d.f d.N (k - 1) σ * Q k σ) by`. Rewrite using `[smul_eq_C_mul]`. Use the proof step `ring, map_smul, smul_eq_mul]`. Rewrite using `[mul_zero, map_zero]`. Establish `h0 : RestTerms.blockPowerSum d.f d.N 0 τ = C (d.N : ℚ)`.

Simplify using `[RestTerms.blockPowerSum]`. Unfold `totalFl`. Rewrite using `[← totalDeriv_apply]`. Simplify using `only [map_sum]`. Rewrite using `[Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun σ _ => key k hk σ]`.

Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_eq_single 1]`. Rewrite using `[Nat.sub_self, h0, ← smul_eq_C_mul, map_smul, smul_eq_mul, Nat.cast_one, one_mul]`. Introduce `k hk hk1`. Rewrite `hk` using `[Finset.mem_Icc]`.

Rewrite using `[intFl_powerSum_mul hK d (k := k - 1) (by omega) (by omega), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h`.
-/
theorem TotFormula.proof (hK : RestTerms.FlagIntegralKillsPowerSums.Statement) :
    TotFormula.Statement := by
  intro d τ F Q _ _ hdec
  unfold RestTerms.IsPowerSumDecomposition at hdec
  subst hdec
  have hN := d.two_le_N
  have key : ∀ k ∈ Icc 1 d.N, ∀ σ : Fin d.f,
      intFl d (totalDeriv d τ (RestTerms.blockPowerSum d.f d.N k σ * Q k σ)) =
        if σ = τ then (k : ℚ) * intFl d (RestTerms.blockPowerSum d.f d.N (k - 1) τ * Q k τ)
        else 0 := by
    intro k hk σ
    rw [Finset.mem_Icc] at hk
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      intFl_powerSum_mul hK d hk.1 hk.2, zero_add, totalDeriv_blockPowerSum]
    split_ifs with h
    · subst h
      rw [show Q k σ * (C (k : ℚ) * RestTerms.blockPowerSum d.f d.N (k - 1) σ) =
          (k : ℚ) • (RestTerms.blockPowerSum d.f d.N (k - 1) σ * Q k σ) by
            rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]
    · rw [mul_zero, map_zero]
  have h0 : RestTerms.blockPowerSum d.f d.N 0 τ = C (d.N : ℚ) := by
    simp [RestTerms.blockPowerSum]
  unfold totalFl
  rw [← totalDeriv_apply]
  simp only [map_sum]
  rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun σ _ => key k hk σ]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single 1]
  · rw [Nat.sub_self, h0, ← smul_eq_C_mul, map_smul, smul_eq_mul, Nat.cast_one, one_mul]
  · intro k hk hk1
    rw [Finset.mem_Icc] at hk
    rw [intFl_powerSum_mul hK d (k := k - 1) (by omega) (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h

/- English proof (translation)
The claim follows from `TotFormula.proof RestTerms.FlagIntegralKillsPowerSums.full`.
-/
theorem TotFormula.full : TotFormula.Statement :=
  TotFormula.proof RestTerms.FlagIntegralKillsPowerSums.full

end GroundTheory.Heights₂.Heights.TheoremB
