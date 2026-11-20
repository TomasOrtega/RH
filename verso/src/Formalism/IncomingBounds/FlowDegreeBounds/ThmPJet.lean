import Formalism.IncomingBounds.DefsThmP

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section
variable {C : Type} [Field C]

/- English proof (translation)
Unfold `jetAt0`. Use `Finset.sum_subset hS fun m _ hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]`.
-/
theorem tpjet_jetAt0_superset {σ : Type} (P : MvPolynomial σ C) (G : MvPowerSeries σ C)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jetAt0 P G = ∑ m ∈ S, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]

/- English proof (translation)
Rewrite `ha` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_add]`. Rewrite using `[MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]`. Distinguish the cases in `hP : MvPolynomial.coeff a P = 0`. Use `right`. Rewrite `ha` using `[hP, zero_add]`. Then use the resulting hypothesis.

Conclude with `Or.inl hP`.
-/
private theorem mem_support_or_of_mem_support_add {σ : Type} (P Q : MvPolynomial σ C)
    (a : σ →₀ ℕ) (ha : a ∈ (P + Q).support) : a ∈ P.support ∨ a ∈ Q.support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at ha
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
  by_cases hP : MvPolynomial.coeff a P = 0
  · right
    rwa [hP, zero_add] at ha
  · exact Or.inl hP

/- English proof (translation)
Establish `h1 : (P + Q).support ⊆ P.support ∪ Q.support`. Introduce `a ha`. Conclude with `Finset.mem_union.2 (mem_support_or_of_mem_support_add P Q a ha)`. Establish `h2 : P.support ⊆ P.support ∪ Q.support`. Introduce `a ha`.

Conclude with `Finset.mem_union.2 (Or.inl ha)`. Establish `h3 : Q.support ⊆ P.support ∪ Q.support`. Introduce `a ha`. Conclude with `Finset.mem_union.2 (Or.inr ha)`. Rewrite using `[tpjet_jetAt0_superset (P + Q) G _ h1, tpjet_jetAt0_superset P G _ h2, tpjet_jetAt0_superset Q G _ h3, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tpjet_jetAt0_add {σ : Type} (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  classical
  have h1 : (P + Q).support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (mem_support_or_of_mem_support_add P Q a ha)
  have h2 : P.support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (Or.inl ha)
  have h3 : Q.support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (Or.inr ha)
  rw [tpjet_jetAt0_superset (P + Q) G _ h1, tpjet_jetAt0_superset P G _ h2,
    tpjet_jetAt0_superset Q G _ h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Unfold `jetAt0`. Simplify using the standard rewrite rules.
-/
theorem tpjet_jetAt0_zero {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  unfold jetAt0
  simp

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, Finset.sum_empty, tpjet_jetAt0_zero]`. Introduce `j t hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]`.
-/
theorem tpjet_jetAt0_sum {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, tpjet_jetAt0_zero]
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

end
end Formalism.IncomingBounds
