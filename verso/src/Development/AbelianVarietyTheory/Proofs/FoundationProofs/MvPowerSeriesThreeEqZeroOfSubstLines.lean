import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ Φ h`. Use extensionality with `d`. Use `set n := ∑ i, d i with hn`. Set `S : Finset (Fin 3 →₀ ℕ)` to `(Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)`. Establish `hS : ∀ e, e ∈ S ↔ ∑ i, e i = n`.

Introduce `e`. Simplify using `only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]`. Introduce `he i`. Express the relevant statement in the definitionally equal form `e i ≤ n`. Rewrite using `[← he]`.

Conclude with `Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Set `P : MvPolynomial (Fin 3) K` to `∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)`. Establish `hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P`. Introduce `t`. Establish `ha : MvPowerSeries.HasSubst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by`.

Rewrite using `[map_mul]`. Conclude with `mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))`. Establish `hprod : ∀ e : Fin 3 →₀ ℕ, (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) = PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s)`. Introduce `e`. Rewrite using `[Finsupp.prod_fintype _ _ (fun s => pow_zero _)]`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]`. Establish `h1 : PowerSeries.coeff n (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k)` using `MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)`. Rewrite using `[h1]`. Simplify using `only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := S) ?_]`.

Simplify using `only [P, map_sum, MvPolynomial.eval_monomial]`. Use `Finset.sum_congr rfl (fun e he => ?_)` and prove the remaining obligations. Rewrite using `[if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]`. Introduce `e he`. Rewrite `he` using `[Function.mem_support]`.

Rewrite using `[Finset.mem_coe, hS]`. Assume the negation of the conclusion as `hne`. Conclude with `he (by rw [if_neg (Ne.symm hne), mul_zero])`. Establish `hP : P = 0` using `MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])`. Establish `hd` using `congrArg (MvPolynomial.coeff d) hP`.

Simplify using `only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd`. Simplify using `using hd`.
-/
theorem mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by
  intro K _ _ Φ h
  ext d
  set n := ∑ i, d i with hn
  let S : Finset (Fin 3 →₀ ℕ) :=
    (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)
  have hS : ∀ e, e ∈ S ↔ ∑ i, e i = n := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
    intro he i
    change e i ≤ n
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  let P : MvPolynomial (Fin 3) K := ∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)
  have hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst
      (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P := by
    intro t
    have ha : MvPowerSeries.HasSubst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        rw [map_mul]; exact mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))
    have hprod : ∀ e : Fin 3 →₀ ℕ,
        (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) =
          PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s) := by
      intro e
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
    have h1 : PowerSeries.coeff n (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) =
        ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) :=
      MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)
    rw [h1]
    simp only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?_]
    · simp only [P, map_sum, MvPolynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
    · intro e he
      rw [Function.mem_support] at he
      rw [Finset.mem_coe, hS]
      by_contra hne
      exact he (by rw [if_neg (Ne.symm hne), mul_zero])
  have hP : P = 0 := MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])
  have hd := congrArg (MvPolynomial.coeff d) hP
  simp only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd
  simpa using hd

end GlobalTheory
