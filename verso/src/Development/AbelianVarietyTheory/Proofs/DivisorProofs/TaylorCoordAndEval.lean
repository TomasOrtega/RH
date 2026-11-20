import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZeroStatement

open Filter Topology

namespace GlobalTheory.PeriodFamily

/- English proof (translation)
Establish `hd : (fun y : I → ℂ ↦ fderiv ℂ (fun z : I → ℂ ↦ z i) y) = fun _ ↦ ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : I ↦ ℂ) i := by`. Use function extensionality and compare the values at `y`. Conclude with `(hasFDerivAt_apply i y).fderiv`. Establish `h2 : ∀ (k : ℕ) (v : Fin (k + 1 + 1) → I → ℂ), iteratedFDeriv ℂ (k + 1 + 1) (fun z : I → ℂ ↦ z i) 0 v = 0`. Introduce `k v`.

Rewrite using `[iteratedFDeriv_succ_apply_right, hd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]`. Simplify using the standard rewrite rules. Establish `h1 : ∀ v : Fin 1 → I → ℂ, iteratedFDeriv ℂ 1 (fun z : I → ℂ ↦ z i) 0 v = v 0 i`. Introduce `v`. Rewrite using `[iteratedFDeriv_one_apply, congrFun hd 0]`.

Simplify using the standard rewrite rules. Unfold `taylor`. Consider the cases of `N with`. Consider the case `zero`. Use `ht fun _ ↦ i` as an intermediate fact.

Simplify using `at this`. Simplify using `[this]`. Consider the case `succ N`. Rewrite using `[Finset.sum_range_succ', Finset.sum_range_succ']`. Simplify using `only [h2, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, h1]`.

Rewrite using `[Finset.sum_eq_single (fun _ ↦ i)]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Establish `: s 0 ≠ i` using `fun h ↦ hs (funext fun a ↦ by rw [Fin.fin_one_eq_zero a, h])`. Simplify using `[Pi.single_eq_of_ne' this]`.

Simplify using the standard rewrite rules.
-/
theorem taylor_coord_of_nilpotent {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (i : I) :
    taylor N t (fun z ↦ z i) = t i := by
  have hd : (fun y : I → ℂ ↦ fderiv ℂ (fun z : I → ℂ ↦ z i) y) =
      fun _ ↦ ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i := by
    funext y
    exact (hasFDerivAt_apply i y).fderiv
  have h2 : ∀ (k : ℕ) (v : Fin (k + 1 + 1) → I → ℂ),
      iteratedFDeriv ℂ (k + 1 + 1) (fun z : I → ℂ ↦ z i) 0 v = 0 := by
    intro k v
    rw [iteratedFDeriv_succ_apply_right, hd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have h1 : ∀ v : Fin 1 → I → ℂ, iteratedFDeriv ℂ 1 (fun z : I → ℂ ↦ z i) 0 v = v 0 i := by
    intro v
    rw [iteratedFDeriv_one_apply, congrFun hd 0]
    simp
  unfold taylor
  cases N with
  | zero =>
    have := ht fun _ ↦ i
    simp at this
    simp [this]
  | succ N =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [h2, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, h1]
    rw [Finset.sum_eq_single (fun _ ↦ i)]
    · simp
    · intro s _ hs
      have : s 0 ≠ i := fun h ↦ hs (funext fun a ↦ by rw [Fin.fin_one_eq_zero a, h])
      simp [Pi.single_eq_of_ne' this]
    · simp

/- English proof (translation)
Introduce `I _ _ D _ _ N t ht`. Use `⟨taylor_coord_of_nilpotent N t ht, fun P ↦ ?_⟩` and prove the remaining obligations. Take `⟨hadd, -, hconst, -⟩` from `GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t`. Establish `hc : ∀ i, AnalyticAt ℂ (fun z : I → ℂ ↦ z i) 0` using `fun i ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i).analyticAt 0`. Establish `han : ∀ Q : MvPolynomial I ℂ, AnalyticAt ℂ (fun z : I → ℂ ↦ MvPolynomial.eval z Q) 0`.

Introduce `Q`. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using analyticAt_const`. Consider the case `add p q hp hq => simpa using hp.fun_add hq`. Consider the case `mul_X p i hp => simpa using hp.fun_mul (hc i)`.

Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hconst a`. Consider the case `add p q hp hq`. Simplify using `only [map_add]`. Rewrite using `[hadd _ _ (han p) (han q), hp, hq]`.

Consider the case `mul_X p i hp`. Simplify using `only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X]`. Rewrite using `[GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (han p) (hc i), hp, taylor_coord_of_nilpotent N t ht]`.
-/
theorem taylor_coord_and_eval : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  intro I _ _ D _ _ N t ht
  refine ⟨taylor_coord_of_nilpotent N t ht, fun P ↦ ?_⟩
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ i, AnalyticAt ℂ (fun z : I → ℂ ↦ z i) 0 := fun i ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i).analyticAt 0
  have han : ∀ Q : MvPolynomial I ℂ, AnalyticAt ℂ (fun z : I → ℂ ↦ MvPolynomial.eval z Q) 0 := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add p q hp hq => simpa using hp.fun_add hq
    | mul_X p i hp => simpa using hp.fun_mul (hc i)
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hconst a
  | add p q hp hq =>
    simp only [map_add]
    rw [hadd _ _ (han p) (han q), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X]
    rw [GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (han p) (hc i), hp, taylor_coord_of_nilpotent N t ht]

end GlobalTheory.PeriodFamily
