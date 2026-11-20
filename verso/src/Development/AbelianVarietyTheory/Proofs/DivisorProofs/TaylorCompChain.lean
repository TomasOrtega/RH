import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZeroStatement

set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 0`. Consider the case `insert i S hi ih`. Simplify using `only [Finset.sum_insert hi]`. Rewrite using `[(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 (f i) (fun z ↦ ∑ i ∈ S, f i z) (hf i) (Finset.analyticAt_fun_sum S fun j _ ↦ hf j), ih]`.
-/
theorem taylor_finset_sum_chain {ι : Type} (S : Finset ι) (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∑ i ∈ S, f i z) = ∑ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 0
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 (f i) (fun z ↦ ∑ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_sum S fun j _ ↦ hf j), ih]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 1`. Consider the case `insert i S hi ih`. Simplify using `only [Finset.prod_insert hi]`. Rewrite using `[GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht (f i) (fun z ↦ ∏ i ∈ S, f i z) (hf i) (Finset.analyticAt_fun_prod S fun j _ ↦ hf j), ih]`.
-/
theorem taylor_finset_prod_chain (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {ι : Type} (S : Finset ι)
    (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∏ i ∈ S, f i z) = ∏ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 1
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    rw [GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht (f i) (fun z ↦ ∏ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_prod S fun j _ ↦ hf j), ih]

end

/- English proof (translation)
Introduce `I _ _ D _ _ N t ht K _ _ Φ h hΦ h0 hh`. Establish `hk : ∀ k, AnalyticAt ℂ (fun z ↦ Φ z k) 0` using `fun k ↦ analyticAt_pi_iff.1 hΦ k`. Establish `hhΦ : AnalyticAt ℂ (fun z ↦ h (Φ z)) 0` using `AnalyticAt.comp (g := h) (f := Φ) (by rw [h0]; exact hh) hΦ`. Establish `hprod : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ ∏ a, Φ z (s a)) 0` using `fun k s ↦ Finset.analyticAt_fun_prod _ fun a _ ↦ hk (s a)`. Use `set c : (k : ℕ) → (Fin k → K) → ℂ := fun k s ↦ (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k h 0 fun a ↦ Pi.single (s a) 1 with hc`.

Establish `hP : (fun z ↦ taylor N (Φ z) h) = fun z ↦ ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)`. Use function extensionality and compare the values at `z`. Simplify using `only [taylor, smul_eq_mul, hc]`. Establish `hterm : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ c k s * ∏ a, Φ z (s a)) 0` using `fun k s ↦ analyticAt_const.mul (hprod k s)`. Establish `hin : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) 0` using `fun k ↦ Finset.analyticAt_fun_sum _ fun s _ ↦ hterm k s`.

Establish `hPa : AnalyticAt ℂ (fun z ↦ taylor N (Φ z) h) 0`. Rewrite using `[hP]`. Conclude with `Finset.analyticAt_fun_sum _ fun k _ ↦ hin k`. Establish `hra : AnalyticAt ℂ (fun z ↦ h (Φ z) - taylor N (Φ z) h) 0` using `hhΦ.sub hPa`. Establish `htend : Tendsto Φ (𝓝 0) (𝓝 0)`.

Use `hΦ.continuousAt.tendsto` as an intermediate fact. Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Establish `hO : Φ =O[𝓝 0] fun z : I → ℂ ↦ z`. Use `hΦ.differentiableAt.isBigO_sub` as an intermediate fact. Simplify `this` using `[h0]`.

Establish `hr : (fun z ↦ h (Φ z) - taylor N (Φ z) h) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)` using `((GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N h hh).1.comp_tendsto htend).trans (hO.norm_norm.pow (N + 1))`. Establish `hz : taylor N t (fun z ↦ h (Φ z) - taylor N (Φ z) h) = 0` using `(GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N _ hra).2 hr t`. Establish `hsplit : (fun z ↦ h (Φ z)) = fun z ↦ (h (Φ z) - taylor N (Φ z) h) + taylor N (Φ z) h`. Use function extensionality and compare the values at `z`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit, (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 _ _ hra hPa, hz, zero_add, hP, taylor_finset_sum_chain N t _ (fun k z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) hin]`. Use `conv_rhs => rw [taylor]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[taylor_finset_sum_chain N t _ (fun s z ↦ c k s * ∏ a, Φ z (s a)) (hterm k)]`. Use `Finset.sum_congr rfl fun s _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.1 _ _ (hprod k s), taylor_finset_prod_chain N t ht _ (fun a z ↦ Φ z (s a)) fun a ↦ hk (s a)]`.
-/
theorem taylor_comp_chain : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  intro I _ _ D _ _ N t ht K _ _ Φ h hΦ h0 hh
  have hk : ∀ k, AnalyticAt ℂ (fun z ↦ Φ z k) 0 := fun k ↦ analyticAt_pi_iff.1 hΦ k
  have hhΦ : AnalyticAt ℂ (fun z ↦ h (Φ z)) 0 := AnalyticAt.comp (g := h) (f := Φ) (by rw [h0]; exact hh) hΦ
  have hprod : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ ∏ a, Φ z (s a)) 0 := fun k s ↦
    Finset.analyticAt_fun_prod _ fun a _ ↦ hk (s a)
  set c : (k : ℕ) → (Fin k → K) → ℂ := fun k s ↦
    (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k h 0 fun a ↦ Pi.single (s a) 1 with hc
  have hP : (fun z ↦ taylor N (Φ z) h) =
      fun z ↦ ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a) := by
    funext z
    simp only [taylor, smul_eq_mul, hc]
  have hterm : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ c k s * ∏ a, Φ z (s a)) 0 := fun k s ↦
    analyticAt_const.mul (hprod k s)
  have hin : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) 0 := fun k ↦
    Finset.analyticAt_fun_sum _ fun s _ ↦ hterm k s
  have hPa : AnalyticAt ℂ (fun z ↦ taylor N (Φ z) h) 0 := by
    rw [hP]
    exact Finset.analyticAt_fun_sum _ fun k _ ↦ hin k
  have hra : AnalyticAt ℂ (fun z ↦ h (Φ z) - taylor N (Φ z) h) 0 := hhΦ.sub hPa
  have htend : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.continuousAt.tendsto
    rwa [h0] at this
  have hO : Φ =O[𝓝 0] fun z : I → ℂ ↦ z := by
    have := hΦ.differentiableAt.isBigO_sub
    simpa [h0] using this
  have hr : (fun z ↦ h (Φ z) - taylor N (Φ z) h) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1) :=
    ((GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N h hh).1.comp_tendsto htend).trans (hO.norm_norm.pow (N + 1))
  have hz : taylor N t (fun z ↦ h (Φ z) - taylor N (Φ z) h) = 0 := (GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N _ hra).2 hr t
  have hsplit : (fun z ↦ h (Φ z)) = fun z ↦ (h (Φ z) - taylor N (Φ z) h) + taylor N (Φ z) h := by
    funext z; ring
  rw [hsplit, (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 _ _ hra hPa, hz, zero_add, hP,
    taylor_finset_sum_chain N t _ (fun k z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) hin]
  conv_rhs => rw [taylor]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [taylor_finset_sum_chain N t _ (fun s z ↦ c k s * ∏ a, Φ z (s a)) (hterm k)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.1 _ _ (hprod k s),
    taylor_finset_prod_chain N t ht _ (fun a z ↦ Φ z (s a)) fun a ↦ hk (s a)]

end GlobalTheory.PeriodFamily
