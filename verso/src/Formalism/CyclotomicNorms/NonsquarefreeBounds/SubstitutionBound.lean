import Formalism.CyclotomicNorms.StatementA

open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

namespace SubstitutionExponents

variable {r : ℕ}

def weight (n : Fin r → ℕ) (d : Fin r →₀ ℕ) : ℕ := ∑ i, d i * n i

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem prod_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (d : Fin r →₀ ℕ) :
    (d.prod fun s e => ((PowerSeries.X : PowerSeries k) ^ n s) ^ e) =
      PowerSeries.X ^ weight n d := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [weight, mul_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem hasSubst_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0) :
    MvPowerSeries.HasSubst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => ?_)
  rw [map_pow]
  have : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    MvPowerSeries.constantCoeff_X _
  rw [this, zero_pow (hn j)]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem coeff_subst_weight {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0)
    (F : MvPowerSeries (Fin r) k) (m : ℕ) :
    PowerSeries.coeff m
        (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) F : PowerSeries k) =
      finsum (fun d => if weight n d = m then MvPowerSeries.coeff d F else 0) := by
  change MvPowerSeries.coeff (Finsupp.single () m) _ = _
  rw [MvPowerSeries.coeff_subst (hasSubst_X_pow n hn)]
  congr 1
  ext d
  rw [prod_X_pow, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_X_pow, smul_eq_mul]
  by_cases h : weight n d = m
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

def revLex : (Fin r →₀ ℕ) → (Fin r →₀ ℕ) → Prop :=
  Finsupp.Lex (· > ·) (· < ·)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem revLex_wf : WellFounded (revLex (r := r)) :=
  Finsupp.Lex.wellFounded_of_finite _ wellFounded_lt

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sum_split (g : Fin r → ℕ) (j : Fin r) :
    ∑ i, g i = ∑ i ∈ univ.filter (· < j), g i + g j + ∑ i ∈ univ.filter (j < ·), g i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (· < j)]
  have h : univ.filter (fun i => ¬ i < j) = insert j (univ.filter (j < ·)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
    exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)
  rw [h, Finset.sum_insert (by simp), add_assoc]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem unique_of_min (n : Fin r → ℕ) (a : Fin r →₀ ℕ)
    (hn : ∀ j, ∑ i ∈ univ.filter (· < j), a i * n i < n j)
    (d : Fin r →₀ ℕ) (hmin : ¬ revLex d a) (hw : weight n d = weight n a) : d = a := by
  classical
  by_contra hne
  have hS : (univ.filter fun i => d i ≠ a i).Nonempty := by
    by_contra h
    apply hne
    ext i
    by_contra hi
    exact h ⟨i, by simp [hi]⟩
  set j := (univ.filter fun i => d i ≠ a i).max' hS with hj
  have hdj : d j ≠ a j := by
    have := Finset.max'_mem _ hS
    rw [← hj] at this
    simpa using this
  have habove : ∀ i, j < i → d i = a i := by
    intro i hi
    by_contra h
    have : i ≤ j := Finset.le_max' _ i (by simp [h])
    exact absurd hi (not_lt.2 this)
  have hlt : a j < d j := by
    rcases lt_or_gt_of_ne hdj with h | h
    · exact absurd ⟨j, fun i hi => habove i hi, h⟩ hmin
    · exact h
  have e1 := sum_split (fun i => d i * n i) j
  have e2 := sum_split (fun i => a i * n i) j
  have e3 : ∑ i ∈ univ.filter (j < ·), d i * n i = ∑ i ∈ univ.filter (j < ·), a i * n i :=
    Finset.sum_congr rfl (fun i hi => by rw [habove i (by simpa using hi)])
  have h4 := hn j
  have h5 : (a j + 1) * n j ≤ d j * n j := Nat.mul_le_mul_right _ hlt
  rw [add_mul, one_mul] at h5
  unfold weight at hw
  rw [e1, e2, e3] at hw
  omega

end SubstitutionExponents

end Formalism.CyclotomicNorms
