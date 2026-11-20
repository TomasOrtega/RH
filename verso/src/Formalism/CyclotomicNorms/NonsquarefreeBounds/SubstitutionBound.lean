import Formalism.CyclotomicNorms.StatementA

open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

namespace SubstitutionExponents

variable {r : ℕ}

def weight (n : Fin r → ℕ) (d : Fin r →₀ ℕ) : ℕ := ∑ i, d i * n i

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Repeatedly rewrite using `[← pow_mul]`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Simplify using `only [weight, mul_comm]`.
-/
theorem prod_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (d : Fin r →₀ ℕ) :
    (d.prod fun s e => ((PowerSeries.X : PowerSeries k) ^ n s) ^ e) =
      PowerSeries.X ^ weight n d := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [weight, mul_comm]

/- English proof (translation)
Use `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => ?_)` and prove the remaining obligations. Rewrite using `[map_pow]`. Establish `: MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0` using `MvPowerSeries.constantCoeff_X _`. Rewrite using `[this, zero_pow (hn j)]`.
-/
theorem hasSubst_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0) :
    MvPowerSeries.HasSubst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => ?_)
  rw [map_pow]
  have : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    MvPowerSeries.constantCoeff_X _
  rw [this, zero_pow (hn j)]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `MvPowerSeries.coeff (Finsupp.single () m) _ = _`. Rewrite using `[MvPowerSeries.coeff_subst (hasSubst_X_pow n hn)]`. Use `congr 1`. Use extensionality with `d`. Rewrite using `[prod_X_pow, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_X_pow, smul_eq_mul]`.

Distinguish the cases in `h : weight n d = m`. Simplify using `[h]`. Rewrite using `[if_neg (Ne.symm h), if_neg h, mul_zero]`.
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
The claim follows from `Finsupp.Lex.wellFounded_of_finite _ wellFounded_lt`.
-/
theorem revLex_wf : WellFounded (revLex (r := r)) :=
  Finsupp.Lex.wellFounded_of_finite _ wellFounded_lt

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not univ (· < j)]`. Establish `h : univ.filter (fun i => ¬ i < j) = insert j (univ.filter (j < ·))`. Use extensionality with `i`. Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, not_lt]`. Conclude with `le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)`.

Rewrite using `[h, Finset.sum_insert (by simp), add_assoc]`.
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
Assume the negation of the conclusion as `hne`. Establish `hS : (univ.filter fun i => d i ≠ a i).Nonempty`. Assume the negation of the conclusion as `h`. Apply `hne` to reduce the goal to its premises. Use extensionality with `i`.

Assume the negation of the conclusion as `hi`. Conclude with `h ⟨i, by simp [hi]⟩`. Use `set j := (univ.filter fun i => d i ≠ a i).max' hS with hj`. Establish `hdj : d j ≠ a j`. Use `Finset.max'_mem _ hS` as an intermediate fact.

Rewrite `this` using `[← hj]`. Simplify using `using this`. Establish `habove : ∀ i, j < i → d i = a i`. Introduce `i hi`. Assume the negation of the conclusion as `h`.

Establish `: i ≤ j` using `Finset.le_max' _ i (by simp [h])`. Conclude with `absurd hi (not_lt.2 this)`. Establish `hlt : a j < d j`. Break down `lt_or_gt_of_ne hdj with h | h` into its components or cases. Conclude with `absurd ⟨j, fun i hi => habove i hi, h⟩ hmin`.

Conclude with `h`. Establish `e1` using `sum_split (fun i => d i * n i) j`. Establish `e2` using `sum_split (fun i => a i * n i) j`. Establish `e3 : ∑ i ∈ univ.filter (j < ·), d i * n i = ∑ i ∈ univ.filter (j < ·), a i * n i` using `Finset.sum_congr rfl (fun i hi => by rw [habove i (by simpa using hi)])`. Establish `h4` using `hn j`.

Establish `h5 : (a j + 1) * n j ≤ d j * n j` using `Nat.mul_le_mul_right _ hlt`. Rewrite `h5` using `[add_mul, one_mul]`. Unfold `weight at hw`. Rewrite `hw` using `[e1, e2, e3]`. Use linear arithmetic over natural numbers and integers.
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
