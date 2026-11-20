import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.IntMvPolynomialCoeffAbsSum

noncomputable def l1 {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  ∑ mo ∈ f.support, (coeff mo f).natAbs

variable {σ : Type*}

/- English proof (translation)
Unfold `l1`. Use `Finset.sum_subset h ?_` and prove the remaining obligations. Introduce `m _ hm`. Simplify using `[MvPolynomial.notMem_support_iff.1 hm]`.
-/
theorem intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    l1 f = ∑ mo ∈ s, (coeff mo f).natAbs := by
  unfold l1
  refine Finset.sum_subset h ?_
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.1 hm]

/- English proof (translation)
Rewrite using `[intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f + g) (f.support ∪ g.support) MvPolynomial.support_add, intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset f (f.support ∪ g.support) Finset.subset_union_left, intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset g (f.support …`. Use `Finset.sum_le_sum fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add]`. Conclude with `Int.natAbs_add_le _ _`.
-/
theorem intMvPolynomialCoeffAbsSum_add_le (f g : MvPolynomial σ ℤ) : l1 (f + g) ≤ l1 f + l1 g := by
  classical
  rw [intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f + g) (f.support ∪ g.support) MvPolynomial.support_add,
    intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset f (f.support ∪ g.support) Finset.subset_union_left,
    intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset g (f.support ∪ g.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [coeff_add]
  exact Int.natAbs_add_le _ _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [l1]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(intMvPolynomialCoeffAbsSum_add_le _ _).trans (Nat.add_le_add_left ih _)`.
-/
theorem intMvPolynomialCoeffAbsSum_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (Nat.add_le_add_left ih _)

/- English proof (translation)
Rewrite using `[intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset _ {m} MvPolynomial.support_monomial_subset]`. Simplify using the standard rewrite rules.
-/
theorem intMvPolynomialCoeffAbsSum_monomial (m : σ →₀ ℕ) (a : ℤ) : l1 (monomial m a) = a.natAbs := by
  classical
  rw [intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset _ {m} MvPolynomial.support_monomial_subset]
  simp

/- English proof (translation)
Establish `h : f * g = ∑ m ∈ f.support, ∑ k ∈ g.support, monomial (m + k) (coeff m f * coeff k g)` using `by conv_lhs => rw [f.as_sum, g.as_sum, Finset.sum_mul_sum]`. Simplify using `only [monomial_mul]`. Rewrite using `[h]`. Use `(intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_` and prove the remaining obligations. Use `conv_rhs => unfold l1`.

Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_le_sum fun m _ => (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_` and prove the remaining obligations. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Rewrite using `[intMvPolynomialCoeffAbsSum_monomial, Int.natAbs_mul]`.
-/
theorem intMvPolynomialCoeffAbsSum_mul_le (f g : MvPolynomial σ ℤ) : l1 (f * g) ≤ l1 f * l1 g := by
  have h : f * g = ∑ m ∈ f.support, ∑ k ∈ g.support,
      monomial (m + k) (coeff m f * coeff k g) := by
    conv_lhs => rw [f.as_sum, g.as_sum, Finset.sum_mul_sum]
    simp only [monomial_mul]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  conv_rhs => unfold l1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun m _ => (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [intMvPolynomialCoeffAbsSum_monomial, Int.natAbs_mul]

/- English proof (translation)
The claim follows from `intMvPolynomialCoeffAbsSum_monomial 0 a`.
-/
theorem intMvPolynomialCoeffAbsSum_C (a : ℤ) : l1 (C a : MvPolynomial σ ℤ) = a.natAbs := intMvPolynomialCoeffAbsSum_monomial 0 a

/- English proof (translation)
The claim follows from `intMvPolynomialCoeffAbsSum_monomial 0 1`.
-/
theorem intMvPolynomialCoeffAbsSum_one : l1 (1 : MvPolynomial σ ℤ) = 1 := intMvPolynomialCoeffAbsSum_monomial 0 1

/- English proof (translation)
The claim follows from `intMvPolynomialCoeffAbsSum_monomial _ 1`.
-/
theorem intMvPolynomialCoeffAbsSum_X (v : σ) : l1 (X v : MvPolynomial σ ℤ) = 1 := intMvPolynomialCoeffAbsSum_monomial _ 1

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [intMvPolynomialCoeffAbsSum_one]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `(intMvPolynomialCoeffAbsSum_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)`.
-/
theorem intMvPolynomialCoeffAbsSum_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intMvPolynomialCoeffAbsSum_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (intMvPolynomialCoeffAbsSum_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

/- English proof (translation)
Simplify using `using intMvPolynomialCoeffAbsSum_prod_le (Finset.range k) (fun _ => f)`.
-/
theorem intMvPolynomialCoeffAbsSum_pow_le (f : MvPolynomial σ ℤ) (k : ℕ) : l1 (f ^ k) ≤ l1 f ^ k := by
  simpa using intMvPolynomialCoeffAbsSum_prod_le (Finset.range k) (fun _ => f)

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `(intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ π : Equiv.Perm (Fin s), l1 ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) * ∏ i, (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)) (π i) i) ≤ 1`. Introduce `π`. Use `(intMvPolynomialCoeffAbsSum_mul_le _ _).trans ?_` and prove the remaining obligations.

Establish `h1 : l1 (((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) = 1`. Use `intMvPolynomialCoeffAbsSum_C (σ := σ) ((Equiv.Perm.sign π : ℤˣ) : ℤ)` as an intermediate fact. Rewrite `this` using `[Int.units_natAbs]`. Simplify using `using this`. Rewrite using `[h1, one_mul]`.

Use `(intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_` and prove the remaining obligations. Simplify using `[intMvPolynomialCoeffAbsSum_X]`. Use `(Finset.sum_le_sum fun π _ => this π).trans ?_` and prove the remaining obligations. Simplify using `[Fintype.card_perm]`.
-/
theorem intMvPolynomialCoeffAbsSum_det_X_le_factorial {s : ℕ} (v : Fin s → Fin s → σ) :
    l1 (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)).det ≤ s.factorial := by
  rw [Matrix.det_apply']
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  have : ∀ π : Equiv.Perm (Fin s), l1 ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) *
      ∏ i, (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)) (π i) i) ≤ 1 := by
    intro π
    refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ?_
    have h1 : l1 (((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) = 1 := by
      have := intMvPolynomialCoeffAbsSum_C (σ := σ) ((Equiv.Perm.sign π : ℤˣ) : ℤ)
      rw [Int.units_natAbs] at this
      simpa using this
    rw [h1, one_mul]
    refine (intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_
    simp [intMvPolynomialCoeffAbsSum_X]
  refine (Finset.sum_le_sum fun π _ => this π).trans ?_
  simp [Fintype.card_perm]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ]`. Use `he (Nat.le_succ n)` as an intermediate fact.

Simplify using `only [Nat.succ_eq_add_one] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_range_sub_succ_add_eq_of_antitone (e : ℕ → ℕ) (he : Antitone e) (n : ℕ) :
    ∑ i ∈ Finset.range n, (e i - e (i + 1)) + e n = e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := he (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at this
    omega

/- English proof (translation)
Set `e : ℕ → ℕ` to `fun i => if h : i < n then ν ⟨i, h⟩ else 0`. Establish `he : Antitone e`. Introduce `i j hij`. Simplify using `only [e]`. Use `split_ifs with h1 h2 h3`.

Conclude with `hν hij`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `h0 : e 0 ≤ R`.

Simplify using `only [e]`. Use `split_ifs`. Conclude with `hR _`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `sum_range_sub_succ_add_eq_of_antitone e he n`.

Establish `h2 : ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) = ∑ i ∈ Finset.range n, (e i - e (i + 1))`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => e i - e (i + 1)) n]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `[e, Formalism.GradedWeylDivisibility.nuNext]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_exponents_le {n : ℕ} (ν : Fin n → ℕ) (R : ℕ) (hν : Antitone ν) (hR : ∀ i, ν i ≤ R) :
    ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) ≤ R := by
  let e : ℕ → ℕ := fun i => if h : i < n then ν ⟨i, h⟩ else 0
  have he : Antitone e := by
    intro i j hij
    simp only [e]
    split_ifs with h1 h2 h3
    · exact hν hij
    · omega
    · omega
    · omega
  have h0 : e 0 ≤ R := by
    simp only [e]
    split_ifs
    · exact hR _
    · omega
  have h1 := sum_range_sub_succ_add_eq_of_antitone e he n
  have h2 : ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) = ∑ i ∈ Finset.range n, (e i - e (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => e i - e (i + 1)) n]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [e, Formalism.GradedWeylDivisibility.nuNext]
  omega

/- English proof (translation)
Introduce `n ν R hν hR`. Express the relevant statement in the definitionally equal form `l1 (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν) ≤ _`. Unfold `Formalism.GradedWeylDivisibility.hw`. Use `(intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_` and prove the remaining obligations. Use `le_trans (Finset.prod_le_prod' (g := fun s => n.factorial ^ (ν s - Formalism.GradedWeylDivisibility.nuNext ν s)) fun s _ => ?_) ?_` and prove the remaining obligations.

Use `(intMvPolynomialCoeffAbsSum_pow_le _ _).trans (Nat.pow_le_pow_left ?_ _)` and prove the remaining obligations. Unfold `Formalism.GradedWeylDivisibility.lpMinor`. Conclude with `(intMvPolynomialCoeffAbsSum_det_X_le_factorial _).trans (Nat.factorial_le s.isLt)`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Conclude with `Nat.pow_le_pow_right (Nat.factorial_pos n) (sum_exponents_le ν R hν hR)`.
-/
theorem highestWeightVector_coeff_natAbs_sum_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), Antitone ν → (∀ i, ν i ≤ R) → ∑ mo ∈ (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν).support, (coeff mo (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν)).natAbs ≤ (n.factorial) ^ R := by
  intro n ν R hν hR
  change l1 (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν) ≤ _
  unfold Formalism.GradedWeylDivisibility.hw
  refine (intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_
  refine le_trans (Finset.prod_le_prod' (g := fun s => n.factorial ^ (ν s - Formalism.GradedWeylDivisibility.nuNext ν s))
    fun s _ => ?_) ?_
  · refine (intMvPolynomialCoeffAbsSum_pow_le _ _).trans (Nat.pow_le_pow_left ?_ _)
    unfold Formalism.GradedWeylDivisibility.lpMinor
    exact (intMvPolynomialCoeffAbsSum_det_X_le_factorial _).trans (Nat.factorial_le s.isLt)
  · rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (Nat.factorial_pos n) (sum_exponents_le ν R hν hR)

end GlobalTheory.IntMvPolynomialCoeffAbsSum
