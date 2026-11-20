import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.TaylorMvLinear

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineRestr_hasSubst {K : Type*} [CommRing K] {n : Type*} [Finite n] (v : n → K) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    have : PowerSeries.constantCoeff (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K) = 0 := by simp
    exact this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem lineRestr_monomial {K : Type*} [CommRing K] {n : Type*} [Fintype n] (v : n → K) (d : n →₀ ℕ) :
    (d.prod fun s e => (PowerSeries.C (v s) * PowerSeries.X : PowerSeries K) ^ e)
      = PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem lineCoeff' : LineCoeff := by
  intro K _ n _ _ v T k
  unfold lineRestr
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst (lineRestr_hasSubst v)]
  have key : ∀ d : n →₀ ℕ, MvPowerSeries.coeff d T •
      MvPowerSeries.coeff (Finsupp.single () k)
        (d.prod fun s e => (PowerSeries.C (v s) * PowerSeries.X : PowerSeries K) ^ e)
      = if k = ∑ i, d i then MvPowerSeries.coeff d T * ∏ i, v i ^ d i else 0 := by
    intro d
    rw [lineRestr_monomial]
    have : MvPowerSeries.coeff (Finsupp.single () k)
        (PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) : PowerSeries K)
        = PowerSeries.coeff k (PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) : PowerSeries K) := rfl
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  rw [finsum_congr key]
  rw [finsum_eq_sum_of_support_subset (s := Finset.finsuppAntidiag Finset.univ k)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [if_pos hd.1.symm]
  · intro d hd
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hd
    obtain ⟨h, -⟩ := hd
    simp [Finset.mem_finsuppAntidiag, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LineUnique_of (h : LineCoeff) : LineUnique := by
  classical
  intro K _ _ n _ T T' hv
  ext ν
  set k := ∑ i, ν i with hk
  let p : MvPolynomial n K := ∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
    MvPolynomial.monomial μ (MvPowerSeries.coeff μ T)
  let q : MvPolynomial n K := ∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
    MvPolynomial.monomial μ (MvPowerSeries.coeff μ T')
  have hpq : p = q := by
    refine MvPolynomial.funext fun v => ?_
    have h1 := h K n v T k
    have h2 := h K n v T' k
    rw [hv v, h2] at h1
    simp only [p, q, map_sum, MvPolynomial.eval_monomial]
    simp only [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    exact h1.symm
  have hν : ν ∈ Finset.finsuppAntidiag Finset.univ k := by simp [Finset.mem_finsuppAntidiag, hk]
  have hc : ∀ S : MvPowerSeries n K, MvPolynomial.coeff ν (∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
      MvPolynomial.monomial μ (MvPowerSeries.coeff μ S)) = MvPowerSeries.coeff ν S := by
    intro S
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' _ ν, if_pos hν]
  rw [← hc T, ← hc T']
  exact congrArg _ hpq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineUnique' : LineUnique := LineUnique_of lineCoeff'

def cntVec {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) : n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (Finset.univ.filter fun j => f j = i).card

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cntVec_apply {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) (i : n) :
    cntVec f i = (Finset.univ.filter fun j => f j = i).card := rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cntVec_sum {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) :
    ∑ i, cntVec f i = k := by
  simp only [cntVec_apply]
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem cntVec_prod {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} {K : Type*} [CommMonoid K] (v : n → K)
    (f : Fin k → n) : ∏ i, v i ^ cntVec f i = ∏ j, v (f j) := by
  rw [← Finset.prod_fiberwise Finset.univ f (fun j => v (f j))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cntVec_apply, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]

/- English proof (translation)
Substitute using the available equality. Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem taylorMv_coeff {n : Type*} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) (k : ℕ) (ν : n →₀ ℕ)
    (h : ν.degree = k) :
    MvPowerSeries.coeff ν (taylorMv F) = ((k.factorial : ℕ) : ℂ)⁻¹ *
      ∑ f : Fin k → n with cntVec f = ν, iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by
  subst h
  change ((ν.degree.factorial : ℕ) : ℂ)⁻¹ * _ = _
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; ext i; exact h i
  · intro h i; exact (cntVec_apply f i).symm.trans (DFunLike.congr_fun h i)

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem multilinear_diag {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin k => n → ℂ) ℂ) (v : n → ℂ) :
    D (fun _ => v) = ∑ f : Fin k → n, (∏ j, v (f j)) * D fun j => Pi.single (f j) (1 : ℂ) := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℂ) : n → ℂ) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : D (fun _ => v) = D (fun _ : Fin k => ∑ i, v i • (Pi.single i (1 : ℂ) : n → ℂ)) := by
    rw [← hv]
  rw [h1, D.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [D.map_smul_univ (fun j => v (f j)) (fun j => Pi.single (f j) (1 : ℂ)), smul_eq_mul]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem iteratedDeriv_line {n : Type*} [Fintype n] (F : (n → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0) (v : n → ℂ)
    (k : ℕ) : iteratedDeriv k (fun t : ℂ => F (t • v)) 0 = iteratedFDeriv ℂ k F 0 fun _ => v := by
  let g : ℂ →L[ℂ] (n → ℂ) := ContinuousLinearMap.toSpanSingleton ℂ v
  let s : Set (n → ℂ) := {x | AnalyticAt ℂ F x}
  have hs : IsOpen s := isOpen_analyticAt ℂ F
  have hgs : IsOpen (g ⁻¹' s) := hs.preimage g.continuous
  have h0 : g 0 ∈ s := by simpa [s] using hF
  have hc : ContDiffOn ℂ (k : ℕ∞) F s :=
    AnalyticOnNhd.contDiffOn (fun x hx => hx) hs.uniqueDiffOn
  have := g.iteratedFDerivWithin_comp_right hc hs.uniqueDiffOn hgs.uniqueDiffOn h0 (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hgs h0, iteratedFDerivWithin_of_isOpen k hs h0] at this
  have hfg : (fun t : ℂ => F (t • v)) = F ∘ g := by
    ext t; simp [g]
  rw [iteratedDeriv_eq_iteratedFDeriv, hfg, this]
  simp [g]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem TaylorLine_of (h : LineCoeff) : TaylorLine := by
  intro n _ _ F hF v
  ext k
  rw [h ℂ n v (taylorMv F) k, Formalism.L2.Th1.F.taylor0, PowerSeries.coeff_mk, iteratedDeriv_line F hF v k,
    multilinear_diag]
  have h1 : ∀ ν ∈ Finset.finsuppAntidiag (Finset.univ : Finset n) k,
      MvPowerSeries.coeff ν (taylorMv F) * ∏ i, v i ^ ν i
      = ((k.factorial : ℕ) : ℂ)⁻¹ * ∑ f : Fin k → n with cntVec f = ν,
          (∏ j, v (f j)) * iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by
    intro ν hν
    rw [Finset.mem_finsuppAntidiag] at hν
    rw [taylorMv_coeff F k ν (by rw [Finsupp.degree_eq_sum]; exact hν.1), mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [← (Finset.mem_filter.1 hf).2, cntVec_prod, mul_comm]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
    Finset.sum_fiberwise_of_maps_to (fun f _ => by simp [Finset.mem_finsuppAntidiag, cntVec_sum]),
    div_eq_inv_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorLine' : TaylorLine := TaylorLine_of lineCoeff'

end Formalism.L2.Th1.H
