import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development

open MvPolynomial

noncomputable section

namespace PI.TOW.DegW

open PI.TO PI.TOW

variable {K : Type} [Field K] {n' k : ℕ}

/- English proof (translation)
Simplify using `only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]`.
-/
theorem multideg_add (a b : Fin n' × Fin k →₀ ℕ) (i : Fin n') :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

/- English proof (translation)
Take `⟨j₁, j₂⟩` from `j`. Apply the tactic sequence `by_cases h : j₁ = i <;> simp [multideg, Finsupp.single_apply, Prod.ext_iff, h]`.
-/
theorem multideg_single (j : Fin n' × Fin k) (i : Fin n') :
    multideg (Finsupp.single j 1) i = if j.1 = i then 1 else 0 := by
  obtain ⟨j₁, j₂⟩ := j
  by_cases h : j₁ = i <;> simp [multideg, Finsupp.single_apply, Prod.ext_iff, h]

/- English proof (translation)
Rewrite `hG` using `[Pol, MvPolynomial.mem_restrictSupport_iff]`. Rewrite using `[G.as_sum, map_sum, Finset.mul_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hdm : ∀ i, multideg m i = d i` using `hG hm`. Rewrite using `[MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul]`.

Distinguish the cases in `hmb : m (t, b) = 0`. Simplify using `[hmb]`. Establish `hle : Finsupp.single (t, b) 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hsplit : m = (m - Finsupp.single (t, b) 1) + Finsupp.single (t, b) 1` using `(tsub_add_cancel_of_le hle).symm`. Establish `hexp : ∀ i, multideg (Finsupp.single (t, a) 1 + (m - Finsupp.single (t, b) 1)) i = d i`. Introduce `i`. Establish `h1` using `multideg_add (m - Finsupp.single (t, b) 1) (Finsupp.single (t, b) 1) i`. Rewrite `h1` using `[← hsplit, hdm i, multideg_single]`.

Rewrite using `[multideg_add, multideg_single]`. Simplify using `only at h1 ⊢`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`. Rewrite using `[Pol, MvPolynomial.mem_restrictSupport_iff]`. Introduce `x hx`.

Establish `hx'` using `MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hx)`. Rewrite `hx'` using `[Finset.mem_singleton]`. Substitute `hx'` using the available equality. Conclude with `hexp`.
-/
theorem step_mem (t : Fin n') (a b : Fin k) (d : Fin n' → ℕ) (G : MvPolynomial (Fin n' × Fin k) K)
    (hG : G ∈ Pol K (ι := Fin n') k d) :
    X (t, a) * pderiv (t, b) G ∈ Pol K (ι := Fin n') k d := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG
  rw [G.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdm : ∀ i, multideg m i = d i := hG hm
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul]
  by_cases hmb : m (t, b) = 0
  · simp [hmb]
  have hle : Finsupp.single (t, b) 1 ≤ m := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : m = (m - Finsupp.single (t, b) 1) + Finsupp.single (t, b) 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hexp : ∀ i, multideg (Finsupp.single (t, a) 1 + (m - Finsupp.single (t, b) 1)) i = d i := by
    intro i
    have h1 := multideg_add (m - Finsupp.single (t, b) 1) (Finsupp.single (t, b) 1) i
    rw [← hsplit, hdm i, multideg_single] at h1
    rw [multideg_add, multideg_single]
    simp only at h1 ⊢
    split_ifs at h1 ⊢ <;> omega
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro x hx
  have hx' := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hx)
  rw [Finset.mem_singleton] at hx'
  subst hx'
  exact hexp

/- English proof (translation)
Introduce `K _ n' k d l G hG`. Proceed by induction on `l with`. Consider the case `nil => exact hG`. Consider the case `cons y l ih`. Simplify using `only [opWord, List.foldr_cons] at ih ⊢`.

Conclude with `step_mem y.1 y.2.1 y.2.2 d _ ih`.
-/
theorem stepDeg : StepDeg := by
  intro K _ n' k d l G hG
  induction l with
  | nil => exact hG
  | cons y l ih =>
    simp only [opWord, List.foldr_cons] at ih ⊢
    exact step_mem y.1 y.2.1 y.2.2 d _ ih

end PI.TOW.DegW
