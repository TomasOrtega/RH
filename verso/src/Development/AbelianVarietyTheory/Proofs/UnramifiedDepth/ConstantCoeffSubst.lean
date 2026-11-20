import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.PolyPairingAdjoint

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {κ : Type*}

def wt (R : Type*) [CommRing R] (A : κ →₀ ℕ) : R := A.prod fun _ e => (e.factorial : R)

def pair (P Q : MvPolynomial κ R) : R := ∑ A ∈ P.support, coeff A P * wt R A * coeff A Q

/- English proof (translation)
Unfold `wt`. Establish `h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support`. Introduce `x hx`. Rewrite `hx` using `[Finsupp.mem_support_iff]`. Distinguish the cases in `hxv : x = v`.

Simplify using `[hxv]`. Apply `Finset.mem_insert_of_mem` to reduce the goal to its premises. Rewrite using `[Finsupp.mem_support_iff]`. Simplify `hx` using `[Finsupp.single_apply, Ne.symm hxv]`. Establish `h2 : B.support ⊆ insert v B.support` using `Finset.subset_insert _ _`.

Rewrite using `[Finsupp.prod_of_support_subset _ h1 (fun _ e => (e.factorial : R)) (fun _ _ => by simp), Finsupp.prod_of_support_subset _ h2 (fun _ e => (e.factorial : R)) (fun _ _ => by simp), ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v B.support), ← Finset.mul_prod_erase _ (fun x => …`. Establish `h3 : ∏ x ∈ (insert v B.support).erase v, (((B + Finsupp.single v 1 : κ →₀ ℕ) x).factorial : R) = ∏ x ∈ (insert v B.support).erase v, ((B x).factorial : R)`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `x hx`. Establish `hxv : x ≠ v` using `Finset.ne_of_mem_erase hx`.

Simplify using `[Ne.symm hxv]`. Rewrite using `[h3]`. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wt_add_single (B : κ →₀ ℕ) (v : κ) :
    wt R (B + Finsupp.single v 1) = wt R B * ((B v : R) + 1) := by
  classical
  unfold wt
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    by_cases hxv : x = v
    · simp [hxv]
    · apply Finset.mem_insert_of_mem
      rw [Finsupp.mem_support_iff]
      simpa [Finsupp.single_apply, Ne.symm hxv] using hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert _ _
  rw [Finsupp.prod_of_support_subset _ h1 (fun _ e => (e.factorial : R)) (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ h2 (fun _ e => (e.factorial : R)) (fun _ _ => by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v B.support),
    ← Finset.mul_prod_erase _ (fun x => ((B x).factorial : R)) (Finset.mem_insert_self v B.support)]
  have h3 : ∏ x ∈ (insert v B.support).erase v,
        (((B + Finsupp.single v 1 : κ →₀ ℕ) x).factorial : R) =
      ∏ x ∈ (insert v B.support).erase v, ((B x).factorial : R) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/- English proof (translation)
Unfold `pair`. Apply `Finset.sum_subset hS` to reduce the goal to its premises. Introduce `A _ hA`. Rewrite `hA` using `[MvPolynomial.notMem_support_iff]`. Simplify using `[hA]`.
-/
theorem pair_eq_sum (P Q : MvPolynomial κ R) (S : Finset (κ →₀ ℕ)) (hS : P.support ⊆ S) :
    pair P Q = ∑ A ∈ S, coeff A P * wt R A * coeff A Q := by
  unfold pair
  apply Finset.sum_subset hS
  intro A _ hA
  rw [MvPolynomial.notMem_support_iff] at hA
  simp [hA]

/- English proof (translation)
Rewrite using `[pair_eq_sum (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add, pair_eq_sum P Q (P.support ∪ P'.support) Finset.subset_union_left, pair_eq_sum P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `A _`. Simplify using `only [coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_add_left (P P' Q : MvPolynomial κ R) : pair (P + P') Q = pair P Q + pair P' Q := by
  classical
  rw [pair_eq_sum (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
    pair_eq_sum P Q (P.support ∪ P'.support) Finset.subset_union_left,
    pair_eq_sum P' Q (P.support ∪ P'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  simp only [coeff_add]
  ring

/- English proof (translation)
Rewrite using `[← smul_eq_C_mul, pair_eq_sum (c • P) Q P.support MvPolynomial.support_smul, pair, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `A _`. Simplify using `only [coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_C_mul_left (c : R) (P Q : MvPolynomial κ R) : pair (C c * P) Q = c * pair P Q := by
  rw [← smul_eq_C_mul, pair_eq_sum (c • P) Q P.support MvPolynomial.support_smul,
    pair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[pair, pair, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `A _`. Simplify using `only [coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_C_mul_right (c : R) (P Q : MvPolynomial κ R) : pair P (C c * Q) = c * pair P Q := by
  rw [pair, pair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [coeff_C_mul]
  ring

/- English proof (translation)
Unfold `pair`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `A _`. Rewrite using `[coeff_sum, Finset.mul_sum]`.
-/
theorem pair_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial κ R)
    (f : α → MvPolynomial κ R) : pair P (∑ i ∈ s, f i) = ∑ i ∈ s, pair P (f i) := by
  unfold pair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [coeff_sum, Finset.mul_sum]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [pair]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_left, ih]`.
-/
theorem pair_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial κ R)
    (Q : MvPolynomial κ R) : pair (∑ i ∈ s, f i) Q = ∑ i ∈ s, pair (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_left, ih]

/- English proof (translation)
Rewrite using `[pair_eq_sum (C c) Q {0} (by`. Introduce `A hA`. Rewrite `hA` using `[MvPolynomial.mem_support_iff, coeff_C]`. Simplify using `only [Finset.mem_singleton]`. Assume the negation of the conclusion as `h`.

Conclude with `hA (if_neg (Ne.symm h)))]`. Simplify using `[wt, constantCoeff_eq]`.
-/
theorem pair_C_left (c : R) (Q : MvPolynomial κ R) : pair (C c) Q = c * constantCoeff Q := by
  classical
  rw [pair_eq_sum (C c) Q {0} (by
    intro A hA
    rw [MvPolynomial.mem_support_iff, coeff_C] at hA
    simp only [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (Ne.symm h)))]
  simp [wt, constantCoeff_eq]

/- English proof (translation)
Establish `hs : (P * X v).support ⊆ P.support.map (addRightEmbedding (Finsupp.single v 1))`. Introduce `A hA`. Rewrite `hA` using `[mem_support_iff, coeff_mul_X']`. Use `split_ifs at hA with h`. Rewrite using `[Finset.mem_map]`.

Use `⟨A - Finsupp.single v 1, mem_support_iff.mpr hA, ?_⟩` and prove the remaining obligations. Rewrite using `[addRightEmbedding_apply]`. Conclude with `Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp h)`. Conclude with `absurd rfl hA`. Rewrite using `[pair_eq_sum (P * X v) Q _ hs, Finset.sum_map, pair]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `B _`. Simplify using `only [addRightEmbedding_apply, coeff_mul_X, coeff_pderiv, wt_add_single]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_mul_X (P Q : MvPolynomial κ R) (v : κ) :
    pair (P * X v) Q = pair P (pderiv v Q) := by
  classical
  have hs : (P * X v).support ⊆ P.support.map (addRightEmbedding (Finsupp.single v 1)) := by
    intro A hA
    rw [mem_support_iff, coeff_mul_X'] at hA
    split_ifs at hA with h
    · rw [Finset.mem_map]
      refine ⟨A - Finsupp.single v 1, mem_support_iff.mpr hA, ?_⟩
      rw [addRightEmbedding_apply]
      exact Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp h)
    · exact absurd rfl hA
  rw [pair_eq_sum (P * X v) Q _ hs, Finset.sum_map, pair]
  apply Finset.sum_congr rfl
  intro B _
  simp only [addRightEmbedding_apply, coeff_mul_X, coeff_pderiv, wt_add_single]
  ring

variable [Fintype κ]

def subst (g : κ → κ → R) : MvPolynomial κ R →ₐ[R] MvPolynomial κ R :=
  aeval (fun i => ∑ j, (C (g i j) * X j : MvPolynomial κ R))

/- English proof (translation)
The claim follows from `aeval_X _ _`.
-/
theorem subst_X (g : κ → κ → R) (i : κ) : subst g (X i) = ∑ j, C (g i j) * X j := aeval_X _ _

/- English proof (translation)
Simplify using `[subst]`.
-/
theorem subst_C (g : κ → κ → R) (c : R) : subst g (C c) = C c := by simp [subst]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => rw [subst_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp => simp [subst_X]`.
-/
theorem constantCoeff_subst (g : κ → κ → R) (Q : MvPolynomial κ R) :
    constantCoeff (subst g Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [subst_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [subst_X]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp [subst_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]`. Consider the case `mul_X p k hp`. Establish `h1 : pderiv j (subst g (X k)) = C (g k j)`.

Rewrite using `[subst_X, map_sum, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[pderiv_X_of_ne hb]`. Simplify using the standard rewrite rules.

Establish `h2 : ∑ i, C (g i j) * subst g (p * pderiv i (X k)) = subst g p * C (g k j)`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[mul_comm]`. Introduce `b _ hb`. Simplify using `[pderiv_X_of_ne (Ne.symm hb)]`.

Simplify using the standard rewrite rules. Rewrite using `[map_mul, pderiv_mul, h1, hp, ← h2, Finset.sum_mul, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Simplify using `only [pderiv_mul, map_add, map_mul, mul_add, mul_assoc]`.
-/
theorem pderiv_subst (g : κ → κ → R) (j : κ) (Q : MvPolynomial κ R) :
    pderiv j (subst g Q) = ∑ i, C (g i j) * subst g (pderiv i Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [subst_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have h1 : pderiv j (subst g (X k)) = C (g k j) := by
      rw [subst_X, map_sum, Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [pderiv_X_of_ne hb]
      · simp
    have h2 : ∑ i, C (g i j) * subst g (p * pderiv i (X k)) = subst g p * C (g k j) := by
      rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb)]
      · simp
    rw [map_mul, pderiv_mul, h1, hp, ← h2, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pderiv_mul, map_add, map_mul, mul_add, mul_assoc]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on generalizing Q with`. Consider the case `C a => rw [subst_C, pair_C_left, pair_C_left, constantCoeff_subst]`. Consider the case `add p q hp hq => rw [map_add, pair_add_left, pair_add_left, hp, hq]`. Consider the case `mul_X p k hp`. Rewrite using `[pair_mul_X, pderiv_subst, pair_sum_right, map_mul, subst_X, Finset.mul_sum, pair_sum_left]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[pair_C_mul_right, hp, mul_left_comm, pair_C_mul_left, pair_mul_X]`.
-/
theorem pair_subst (g : κ → κ → R) (P Q : MvPolynomial κ R) :
    pair P (subst g Q) = pair (subst (fun i j => g j i) P) Q := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a => rw [subst_C, pair_C_left, pair_C_left, constantCoeff_subst]
  | add p q hp hq => rw [map_add, pair_add_left, pair_add_left, hp, hq]
  | mul_X p k hp =>
    rw [pair_mul_X, pderiv_subst, pair_sum_right, map_mul, subst_X, Finset.mul_sum, pair_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [pair_C_mul_right, hp, mul_left_comm, pair_C_mul_left, pair_mul_X]

/- English proof (translation)
Introduce `C _ _ κ _ _ g P Q`. Conclude with `pair_subst (fun i j => g i j) P Q`.
-/
theorem main :
  (∀ (C : Type) [Field C] [CharZero C] (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix κ κ C) (P Q : MvPolynomial κ C),
    (∑ A ∈ (P).support, MvPolynomial.coeff A (P) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) Q)) =
    (∑ A ∈ (MvPolynomial.aeval (fun i => ∑ j, (MvPolynomial.C (g j i) * MvPolynomial.X j : MvPolynomial κ C)) P).support, MvPolynomial.coeff A (MvPolynomial.aeval (fun i => ∑ j, (MvPolynomial.C (g j i) * MvPolynomial.X j : MvPolynomial κ C)) P) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q))) := by
  intro C _ _ κ _ _ g P Q
  exact pair_subst (fun i j => g i j) P Q

end GlobalTheory.PolyPairingAdjoint
