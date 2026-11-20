import Mathlib
import GroundTheory.LocalFields.LubinTateReciprocity.Descent

noncomputable section

open MvPowerSeries ValuativeRel

namespace GroundTheory.LocalField

section Coeff

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/- English proof (translation)
Rewrite using `[PowerSeries.coeff, coeff_subst, finsum_eq_single _ (Finsupp.single 0 j)]`. Simplify using `[PowerSeries.coeff_X_pow]`. Introduce `d hd`. Distinguish the cases in `hd₁ : d 1 = 0`. Simplify using `[hd₁, PowerSeries.coeff_X_pow]`.

Introduce `h`. Apply the tactic sequence `exact absurd (by ext i; fin_cases i <;> simp [h, hd₁]) hd`. Simplify using `[hd₁]`. Conclude with `HasSubst.X_zero`.
-/
theorem coeff_formalGroup_Xzero (j : ℕ) :
    PowerSeries.coeff j F.Xzero = coeff (Finsupp.single 0 j) F.toPowerSeries := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (Finsupp.single 0 j)]
  · simp [PowerSeries.coeff_X_pow]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · simp [hd₁, PowerSeries.coeff_X_pow]
      intro h
      exact absurd (by ext i; fin_cases i <;> simp [h, hd₁]) hd
    · simp [hd₁]
  · exact HasSubst.X_zero

/- English proof (translation)
Establish `hdvd : (X 1 : MvPowerSeries (Fin 2) R) ∣ F.toPowerSeries - X 0`. Rewrite using `[X_dvd_iff]`. Introduce `m hm`. Establish `hm' : m = Finsupp.single 0 (m 0)`. Apply the tactic sequence `ext i; fin_cases i <;> simp [hm]`.

Rewrite using `[map_sub, hm', ← coeff_formalGroup_Xzero, F.Xzero_eq_X, PowerSeries.coeff_X, coeff_X]`. Distinguish the cases in `h : m 0 = 1`. Simplify using `[h]`. Establish `: Finsupp.single (0 : Fin 2) (m 0) ≠ Finsupp.single 0 1`. Introduce `e; exact h (by simpa using congrArg (fun d => d 0) e)`.

Simplify using `[h, this]`. Take `⟨G, hG⟩` from `hdvd`. Use `⟨G, ?_, hG⟩` and prove the remaining obligations. Establish `h` using `congrArg (coeff (Finsupp.single 1 1)) hG`. Rewrite using `[map_sub, F.lin_coeff_Y, coeff_X, if_neg (by`.

Introduce `e`. Simplify using `using congrArg (fun d => d 1) e)] at h`. Establish `e` using `coeff_add_monomial_mul (m := Finsupp.single (1 : Fin 2) 1) (n := 0) (φ := G) (1 : R)`. Rewrite `e` using `[add_zero, one_mul, ← X_def]`. Rewrite `h` using `[e, sub_zero]`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← h]`.
-/
theorem exists_sub_X_eq_X_mul :
    ∃ G : MvPowerSeries (Fin 2) R, constantCoeff G = 1 ∧ F.toPowerSeries - X 0 = X 1 * G := by
  have hdvd : (X 1 : MvPowerSeries (Fin 2) R) ∣ F.toPowerSeries - X 0 := by
    rw [X_dvd_iff]
    intro m hm
    have hm' : m = Finsupp.single 0 (m 0) := by
      ext i; fin_cases i <;> simp [hm]
    rw [map_sub, hm', ← coeff_formalGroup_Xzero, F.Xzero_eq_X, PowerSeries.coeff_X, coeff_X]
    by_cases h : m 0 = 1
    · simp [h]
    · have : Finsupp.single (0 : Fin 2) (m 0) ≠ Finsupp.single 0 1 := by
        intro e; exact h (by simpa using congrArg (fun d => d 0) e)
      simp [h, this]
  obtain ⟨G, hG⟩ := hdvd
  refine ⟨G, ?_, hG⟩
  have h := congrArg (coeff (Finsupp.single 1 1)) hG
  rw [map_sub, F.lin_coeff_Y, coeff_X, if_neg (by
    intro e; simpa using congrArg (fun d => d 1) e)] at h
  have e := coeff_add_monomial_mul (m := Finsupp.single (1 : Fin 2) 1) (n := 0) (φ := G) (1 : R)
  rw [add_zero, one_mul, ← X_def] at e
  rw [e, sub_zero] at h
  rw [← coeff_zero_eq_constantCoeff_apply, ← h]

end Coeff

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [IsValuativeTopology Ω]
  [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

/- English proof (translation)
Rewrite using `[psEval, tsum_eq_single 0]`. Simplify using `[psTerm]`. Introduce `d hd`. Simplify using `[psTerm, coeff_one, hd]`.
-/
theorem psEval_one {σ : Type*} (x : σ → Ω) : psEval (1 : MvPowerSeries σ 𝒪[K]) x = 1 := by
  classical
  rw [psEval, tsum_eq_single 0]
  · simp [psTerm]
  · intro d hd
    simp [psTerm, coeff_one, hd]

/- English proof (translation)
Take `⟨G, hG1, hG⟩` from `exists_sub_X_eq_X_mul F`. Establish `hx : ∀ i, valuation Ω ((![a, b] : Fin 2 → Ω) i) < 1`. Introduce `i`. Use `fin_cases i`. Use `exacts [ha, hb]`.

Establish `h1 : psEval F.toPowerSeries ![a, b] - a = b * psEval G ![a, b]`. Establish `e : F.toPowerSeries = X 0 + X 1 * G` using `by rw [← hG]; ring`. Rewrite using `[e, psEval_add' _ _ _ hx, psEval_mul' _ _ _ hx, psEval_X, psEval_X]`. Simplify using the standard rewrite rules. Establish `h2 : valuation Ω (psEval G ![a, b]) = 1`.

Establish `hG' : G = 1 + (G - 1)` using `by ring`. Establish `hc : constantCoeff (G - 1) = 0` using `by simp [hG1]`. Rewrite using `[hG', psEval_add' _ _ _ hx, psEval_one]`. Conclude with `Valuation.map_one_add_of_lt _ (valuation_psEval_lt_one' hc _ hx)`. Rewrite using `[h1, map_mul, h2, mul_one]`.
-/
theorem valuation_psEval_sub_left (F : FormalGroup 𝒪[K]) {a b : Ω} (ha : valuation Ω a < 1)
    (hb : valuation Ω b < 1) :
    valuation Ω (psEval F.toPowerSeries ![a, b] - a) = valuation Ω b := by
  obtain ⟨G, hG1, hG⟩ := exists_sub_X_eq_X_mul F
  have hx : ∀ i, valuation Ω ((![a, b] : Fin 2 → Ω) i) < 1 := by
    intro i; fin_cases i
    exacts [ha, hb]
  have h1 : psEval F.toPowerSeries ![a, b] - a = b * psEval G ![a, b] := by
    have e : F.toPowerSeries = X 0 + X 1 * G := by rw [← hG]; ring
    rw [e, psEval_add' _ _ _ hx, psEval_mul' _ _ _ hx, psEval_X, psEval_X]
    simp
  have h2 : valuation Ω (psEval G ![a, b]) = 1 := by
    have hG' : G = 1 + (G - 1) := by ring
    have hc : constantCoeff (G - 1) = 0 := by simp [hG1]
    rw [hG', psEval_add' _ _ _ hx, psEval_one]
    exact Valuation.map_one_add_of_lt _ (valuation_psEval_lt_one' hc _ hx)
  rw [h1, map_mul, h2, mul_one]

end Valuation

end GroundTheory.LocalField
