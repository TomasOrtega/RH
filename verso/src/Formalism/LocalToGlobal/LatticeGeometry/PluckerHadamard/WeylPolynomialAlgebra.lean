import Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.BlockVandermondeForms
import Formalism.DegreeFormula.PointDegree.FlagDeg

noncomputable section

open Finset MvPolynomial

namespace Formalism.L2.Geo

namespace WeylPolynomialAlgebra

section Polar

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

def Qp (ℓ : ι → R) (s : Finset ι) (k : ℕ) : R :=
  ∑ S ∈ s.powerset, (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k

/- English proof (translation)
Unfold `Qp`. Rewrite using `[Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]`. Establish `h1 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card + 1 - S.card) * (∑ i ∈ S, ℓ i) ^ k = -((-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k)`. Introduce `S hS`. Establish `hc : S.card ≤ s.card` using `Finset.card_le_card (Finset.mem_powerset.mp hS)`.

Rewrite using `[show s.card + 1 - S.card = (s.card - S.card) + 1 by omega, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card + 1 - (insert a S).card) * (∑ i ∈ insert a S, ℓ i) ^ k = (-1) ^ (s.card - S.card) * (ℓ a + ∑ i ∈ S, ℓ i) ^ k`. Introduce `S hS`. Establish `haS : a ∉ S` using `fun h => ha (Finset.mem_powerset.mp hS h)`.

Rewrite using `[Finset.card_insert_of_notMem haS, Finset.sum_insert haS, show s.card + 1 - (S.card + 1) = s.card - S.card by omega]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib, ← sub_eq_neg_add, ← Finset.sum_sub_distrib]`. Establish `h3 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card - S.card) * (ℓ a + ∑ i ∈ S, ℓ i) ^ k - (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k = ∑ m ∈ range k, (k.choose (m + 1) : R) * ℓ a ^ (m + 1) * ((-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ (k - 1 - m))`. Introduce `S _`. Rewrite using `[add_pow, Finset.sum_range_succ']`.

Simplify using `only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]`. Rewrite using `[mul_add, add_sub_cancel_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Establish `hm' : m < k` using `Finset.mem_range.mp hm`. Rewrite using `[show k - (m + 1) = k - 1 - m by omega]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h3, Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.
-/
theorem Qp_insert (ℓ : ι → R) (a : ι) (s : Finset ι) (ha : a ∉ s) (k : ℕ) :
    Qp ℓ (insert a s) k = ∑ m ∈ range k, (k.choose (m + 1) : R) * ℓ a ^ (m + 1) * Qp ℓ s (k - 1 - m) := by
  unfold Qp
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have h1 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card + 1 - S.card) * (∑ i ∈ S, ℓ i) ^ k =
      -((-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k) := by
    intro S hS
    have hc : S.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
    rw [show s.card + 1 - S.card = (s.card - S.card) + 1 by omega, pow_succ]
    ring
  have h2 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card + 1 - (insert a S).card) * (∑ i ∈ insert a S, ℓ i) ^ k =
      (-1) ^ (s.card - S.card) * (ℓ a + ∑ i ∈ S, ℓ i) ^ k := by
    intro S hS
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.card_insert_of_notMem haS, Finset.sum_insert haS,
      show s.card + 1 - (S.card + 1) = s.card - S.card by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib, ← sub_eq_neg_add,
    ← Finset.sum_sub_distrib]
  have h3 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card - S.card) * (ℓ a + ∑ i ∈ S, ℓ i) ^ k -
      (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k =
      ∑ m ∈ range k, (k.choose (m + 1) : R) * ℓ a ^ (m + 1) *
        ((-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ (k - 1 - m)) := by
    intro S _
    rw [add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    rw [mul_add, add_sub_cancel_right, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m < k := Finset.mem_range.mp hm
    rw [show k - (m + 1) = k - 1 - m by omega]
    ring
  rw [Finset.sum_congr rfl h3, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `k hk`. Establish `hk0 : k = 0` using `by simpa using hk`. Substitute `hk0` using the available equality.

Simplify using `[Qp]`. Consider the case `insert a s ha ih`. Introduce `k hk`. Rewrite `hk`, the goal using `[Finset.card_insert_of_notMem ha]`. Rewrite using `[Qp_insert ℓ a s ha k]`.

Distinguish the cases in `hks : k = s.card + 1`. Substitute `hks` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single 0]`. Rewrite using `[ih _ (by omega), if_pos (by omega), Finset.prod_insert ha, Nat.factorial_succ]`. Use `push_cast`.

Simplify using `only [Nat.choose_one_right, zero_add, pow_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `m hm hm0`. Use `Finset.mem_range.mp hm` as an intermediate fact.

Rewrite using `[ih _ (by omega), if_neg (by omega), mul_zero]`. Introduce `h`. Simplify using `at h`. Rewrite using `[if_neg hks]`. Use `Finset.sum_eq_zero (fun m hm => ?_)` and prove the remaining obligations.

Establish `hm' : m < k` using `Finset.mem_range.mp hm`. Rewrite using `[ih _ (by omega), if_neg (by omega), mul_zero]`.
-/
theorem Qp_eq (ℓ : ι → R) (s : Finset ι) : ∀ k ≤ s.card,
    Qp ℓ s k = if k = s.card then (s.card.factorial : R) * ∏ i ∈ s, ℓ i else 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp [Qp]
  | insert a s ha ih =>
    intro k hk
    rw [Finset.card_insert_of_notMem ha] at hk ⊢
    rw [Qp_insert ℓ a s ha k]
    by_cases hks : k = s.card + 1
    · subst hks
      rw [if_pos rfl, Finset.sum_eq_single 0]
      · rw [ih _ (by omega), if_pos (by omega), Finset.prod_insert ha, Nat.factorial_succ]
        push_cast
        simp only [Nat.choose_one_right, zero_add, pow_one]
        push_cast
        ring
      · intro m hm hm0
        have := Finset.mem_range.mp hm
        rw [ih _ (by omega), if_neg (by omega), mul_zero]
      · intro h; simp at h
    · rw [if_neg hks]
      refine Finset.sum_eq_zero (fun m hm => ?_)
      have hm' : m < k := Finset.mem_range.mp hm
      rw [ih _ (by omega), if_neg (by omega), mul_zero]

/- English proof (translation)
Use `Qp_eq ℓ s s.card le_rfl` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`. Conclude with `this.symm`.
-/
theorem polarization (ℓ : ι → R) (s : Finset ι) :
    (s.card.factorial : R) * ∏ i ∈ s, ℓ i =
      ∑ S ∈ s.powerset, (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ s.card := by
  have := Qp_eq ℓ s s.card le_rfl
  rw [if_pos rfl] at this
  exact this.symm

end Polar

section Apol

variable {σ : Type*}

def apol (P g : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ P.support, P.coeff m * g.coeff m * (m.prod fun _ e => (e.factorial : ℝ))

/- English proof (translation)
Unfold `apol`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem apol_add (P g h : MvPolynomial σ ℝ) : apol P (g + h) = apol P g + apol P h := by
  unfold apol; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun m _ => ?_); rw [coeff_add]; ring

/- English proof (translation)
Unfold `apol`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem apol_smul (P g : MvPolynomial σ ℝ) (c : ℝ) : apol P (c • g) = c * apol P g := by
  unfold apol; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun m _ => ?_); rw [coeff_smul, smul_eq_mul]; ring

/- English proof (translation)
Unfold `apol`. Take `⟨m, hm⟩` from `Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hP)`. Use `Finset.sum_pos (fun m hm => ?_) ⟨m, hm⟩` and prove the remaining obligations. Establish `h1 : P.coeff m ≠ 0` using `MvPolynomial.mem_support_iff.mp hm`. Establish `h2 : 0 < m.prod fun _ e => (e.factorial : ℝ)` using `Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _))`.

Establish `h3 : 0 < P.coeff m * P.coeff m` using `mul_self_pos.mpr h1`. Check the signs of the components of the expression.
-/
theorem apol_self_pos (P : MvPolynomial σ ℝ) (hP : P ≠ 0) : 0 < apol P P := by
  unfold apol
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hP)
  refine Finset.sum_pos (fun m hm => ?_) ⟨m, hm⟩
  have h1 : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h2 : 0 < m.prod fun _ e => (e.factorial : ℝ) :=
    Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _))
  have h3 : 0 < P.coeff m * P.coeff m := mul_self_pos.mpr h1
  positivity

end Apol

end WeylPolynomialAlgebra

namespace WeylPolynomialAlgebra

section ApolPow

variable {σ : Type*} [Fintype σ]

/- English proof (translation)
Unfold `apol`. Rewrite using `[MvPolynomial.eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Establish `hdeg : (m.sum fun _ e => e) = d`. Use `hP (MvPolynomial.mem_support_iff.mp hm)` as an intermediate fact.

Simplify `this` using `[Finsupp.degree, Finsupp.sum, Finsupp.weight_apply]`. Rewrite using `[coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]`. Establish `hspec` using `Nat.multinomial_spec m.support m`. Establish `hsum : ∑ i ∈ m.support, m i = d` using `by simpa [Finsupp.sum] using hdeg`. Rewrite `hspec` using `[hsum]`.

Simplify using `only [Finsupp.prod, Finsupp.multinomial_eq]`. Establish `hcast : (∏ i ∈ m.support, ((m i).factorial : ℝ)) * (Nat.multinomial m.support m : ℝ) = (d.factorial : ℝ)` using `by exact_mod_cast hspec`. Rewrite using `[← hcast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem apol_pow (P : MvPolynomial σ ℝ) (d : ℕ) (hP : P.IsHomogeneous d) (a : σ → ℝ) :
    apol P ((∑ i, a i • X i : MvPolynomial σ ℝ) ^ d) = (d.factorial : ℝ) * eval a P := by
  unfold apol
  rw [MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hdeg : (m.sum fun _ e => e) = d := by
    have := hP (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.degree, Finsupp.sum, Finsupp.weight_apply] using this
  rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
  have hspec := Nat.multinomial_spec m.support m
  have hsum : ∑ i ∈ m.support, m i = d := by simpa [Finsupp.sum] using hdeg
  rw [hsum] at hspec
  simp only [Finsupp.prod, Finsupp.multinomial_eq]
  have hcast : (∏ i ∈ m.support, ((m i).factorial : ℝ)) * (Nat.multinomial m.support m : ℝ) =
      (d.factorial : ℝ) := by exact_mod_cast hspec
  rw [← hcast]
  ring

end ApolPow

open Formalism.ShimuraLimitIdentity (Pol)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def idxS (Ψ : Type) [Fintype Ψ] (N j : ℕ) : Finset (Ψ × Fin N × Fin N) :=
  univ.filter (fun t => t.2.1 < t.2.2 ∧ (t.2.1.val < j ↔ t.2.2.val < j))

def idxC (Ψ : Type) [Fintype Ψ] (N j : ℕ) : Finset (Ψ × Fin N × Fin N) :=
  univ.filter (fun t => t.2.1 < t.2.2 ∧ ¬ (t.2.1.val < j ↔ t.2.2.val < j))

def ell (t : Ψ × Fin N × Fin N) : Pol Ψ N := X (t.1, t.2.1) - X (t.1, t.2.2)

def nuT (t : Ψ × Fin N × Fin N) : Ψ → Fin N → ℝ := fun τ i =>
  (if (τ, i) = (t.1, t.2.2) then 1 else 0) - (if (τ, i) = (t.1, t.2.1) then 1 else 0)

/- English proof (translation)
Unfold `Formalism.DegreeFormula.linRoot nuT ell`. Simplify using `only [map_sub, sub_mul, Finset.sum_sub_distrib, neg_sub]`. Establish `h : ∀ y : Ψ × Fin N, (∑ x : Ψ × Fin N, C (if (x.1, x.2) = y then (1 : ℝ) else 0) * X x) = X y`. Introduce `y`. Rewrite using `[Finset.sum_eq_single y]`.

Simplify using the standard rewrite rules. Introduce `b _ hb; rw [if_neg (by simpa using hb)]; simp`. Simplify using the standard rewrite rules. Rewrite using `[h, h]`.
-/
theorem linRoot_nuT (t : Ψ × Fin N × Fin N) : Formalism.DegreeFormula.linRoot (nuT t) = ell t := by
  unfold Formalism.DegreeFormula.linRoot nuT ell
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib, neg_sub]
  have h : ∀ y : Ψ × Fin N, (∑ x : Ψ × Fin N, C (if (x.1, x.2) = y then (1 : ℝ) else 0) * X x) = X y := by
    intro y
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; rw [if_neg (by simpa using hb)]; simp
    · simp
  rw [h, h]

/- English proof (translation)
Unfold `Formalism.DegreeFormula.linRoot`. Simplify using `only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, neg_add]`.
-/
theorem linRoot_add (l1 l2 : Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot (l1 + l2) = Formalism.DegreeFormula.linRoot l1 + Formalism.DegreeFormula.linRoot l2 := by
  unfold Formalism.DegreeFormula.linRoot
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, neg_add]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Formalism.DegreeFormula.linRoot]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linRoot_add, ih]`.
-/
theorem linRoot_sum {α : Type*} (s : Finset α) (l : α → Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot (∑ a ∈ s, l a) = ∑ a ∈ s, Formalism.DegreeFormula.linRoot (l a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.DegreeFormula.linRoot]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linRoot_add, ih]

/- English proof (translation)
Unfold `Formalism.DegreeFormula.linRoot`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_neg]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linRoot_smul (c : ℝ) (l : Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot (c • l) = C c * Formalism.DegreeFormula.linRoot l := by
  unfold Formalism.DegreeFormula.linRoot
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_neg]
  congr 1; refine Finset.sum_congr rfl (fun x _ => ?_); ring

/- English proof (translation)
Unfold `fibreVandermondeProduct blockVandermondePolynomial idxS ell`. Rewrite using `[map_one, one_mul, Finset.prod_filter, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Unfold `Formalism.ShimuraLimitIdentity.top smallBlock`.

Simplify using `only [Finset.prod_filter]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Distinguish the cases in `ha : a.val < j`. Establish `ha' : ¬ j ≤ a.val` using `by omega`.

Simplify using `only [ha, ha', if_true, if_false, mul_one]`. Use `Finset.prod_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hb : b.val < j`. Simplify using `[hb]`. Simplify using `[hb]`.

Establish `ha' : j ≤ a.val` using `by omega`. Simplify using `only [ha, ha', if_true, if_false, one_mul]`. Use `Finset.prod_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hb : j ≤ b.val`. Establish `hb' : ¬ b.val < j` using `by omega`.

Simplify using `[hb, hb']`. Establish `hb' : b.val < j` using `by omega`. Simplify using `[hb, hb']`.
-/
theorem fib_eq (j : ℕ) :
    fibreVandermondeProduct (Ψ := Ψ) (N := N) j 1 = ∏ t ∈ idxS Ψ N j, ell t := by
  classical
  unfold fibreVandermondeProduct blockVandermondePolynomial idxS ell
  rw [map_one, one_mul, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  unfold Formalism.ShimuraLimitIdentity.top smallBlock
  simp only [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  by_cases ha : a.val < j
  · have ha' : ¬ j ≤ a.val := by omega
    simp only [ha, ha', if_true, if_false, mul_one]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    by_cases hb : b.val < j
    · simp [hb]
    · simp [hb]
  · have ha' : j ≤ a.val := by omega
    simp only [ha, ha', if_true, if_false, one_mul]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    by_cases hb : j ≤ b.val
    · have hb' : ¬ b.val < j := by omega
      simp [hb, hb']
    · have hb' : b.val < j := by omega
      simp [hb, hb']

end WeylPolynomialAlgebra

namespace WeylPolynomialAlgebra

open Formalism.ShimuraLimitIdentity (Pol)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def eW (Ψ : Type) (N j : ℕ) : Ψ → Fin N → ℝ := fun _ i => if j ≤ i.val then -1 else 0

/- English proof (translation)
Unfold `Formalism.DegreeFormula.linRoot eW a0Mu smallBlock`. Rewrite using `[← Finset.sum_neg_distrib, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem linRoot_eW (j : ℕ) : Formalism.DegreeFormula.linRoot (eW Ψ N j) = a0Mu (Ψ := Ψ) (N := N) j := by
  unfold Formalism.DegreeFormula.linRoot eW a0Mu smallBlock
  rw [← Finset.sum_neg_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[MvPolynomial.C_mul', map_smul, smul_eq_mul]`.
-/
theorem degFlL_C_mul (a : ℝ) (P : Pol Ψ N) : degFlL Ψ N (C a * P) = a * degFlL Ψ N P := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

/- English proof (translation)
Use `set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef`. Use `set μ : Pol Ψ N := a0Mu j with hμ`. Use `set L : Pol Ψ N := Formalism.DegreeFormula.linRoot ν with hL`. Establish `hW : ∀ ε : ℝ, degFlL Ψ N ((μ + C ε * L) ^ D) = (D.factorial : ℝ) * Formalism.DegreeFormula.weylProd (eW Ψ N j + ε • ν)`. Introduce `ε`.

Establish `h` using `Formalism.DegreeFormula.flagDegFormula_statement Ψ N (eW Ψ N j + ε • ν)`. Unfold `Formalism.DegreeFormula.flagDeg at h`. Rewrite `h` using `[linRoot_add, linRoot_smul, linRoot_eW]`. Rewrite using `[degFlL_apply]`. Conclude with `h`.

Use `set PL : Polynomial ℝ := ∑ m ∈ range (D + 1), Polynomial.C ((D.choose m : ℝ) * degFlL Ψ N (μ ^ m * L ^ (D - m))) * Polynomial.X ^ (D - m) with hPLdef`. Establish `hPL : ∀ ε : ℝ, PL.eval ε = degFlL Ψ N ((μ + C ε * L) ^ D)`. Introduce `ε`. Rewrite using `[add_pow, map_sum, hPLdef, Polynomial.eval_finsetSum]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations.

Establish `e : μ ^ m * (C ε * L) ^ (D - m) * ((D.choose m : ℕ) : Pol Ψ N) = C (ε ^ (D - m) * (D.choose m : ℝ)) * (μ ^ m * L ^ (D - m))`. Rewrite using `[map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, degFlL_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Expand and normalize the polynomial expressions, which then agree.

Use `set F : Ψ × Fin N × Fin N → Polynomial ℝ := fun t => if t.2.1 < t.2.2 then Polynomial.C ((eW Ψ N j t.1 t.2.1 - eW Ψ N j t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) + Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1 with hFdef`. Use `set PR : Polynomial ℝ := Polynomial.C (D.factorial : ℝ) * ∏ t, F t with hPRdef`. Establish `hPR : ∀ ε : ℝ, PR.eval ε = (D.factorial : ℝ) * Formalism.DegreeFormula.weylProd (eW Ψ N j + ε • ν)`. Introduce `ε`. Rewrite using `[hPRdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Formalism.DegreeFormula.weylProd, Fintype.prod_prod_type]`.

Use `congr 1`. Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Simplify using `only [hFdef]`.

Use `split_ifs`. Simplify using `only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hPLR : PL = PR` using `Polynomial.funext (fun ε => by rw [hPL, hPR, hW])`.

Establish `hcL : PL.coeff k = (D.choose n : ℝ) * degFlL Ψ N (μ ^ n * L ^ k)`. Rewrite using `[hPLdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]`. Rewrite using `[Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one, show D - n = k by omega]`. Introduce `m hm hmn`. Use `Finset.mem_range.mp hm` as an intermediate fact.

Rewrite using `[Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]`. Introduce `h; exact absurd (Finset.mem_range.mpr (by omega)) h`. Establish `hsplit : ∀ t, F t = (if t ∈ idxS Ψ N j then Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1) * (if t ∈ idxC Ψ N j then Polynomial.C (1 / ((t.2.2 : ℝ) - t.2.1)) + Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomi …`. Introduce `t`. Simplify using `only [hFdef, idxS, idxC, Finset.mem_filter, Finset.mem_univ, true_and]`.

Distinguish the cases in `hab : t.2.1 < t.2.2`. Distinguish the cases in `hs : (t.2.1.val < j ↔ t.2.2.val < j)`. Establish `he : eW Ψ N j t.1 t.2.1 = eW Ψ N j t.1 t.2.2`. Unfold `eW`. Distinguish the cases in `h1 : j ≤ t.2.1.val`.

Establish `h2 : j ≤ t.2.2.val` using `by omega`. Simplify using `[h1, h2]`. Establish `h2 : ¬ j ≤ t.2.2.val` using `by omega`. Simplify using `[h1, h2]`. Simplify using `only [hab, hs, and_self, if_true, not_true, and_false, if_false, mul_one, he, sub_self, zero_div, map_zero, zero_add]`.

Establish `h1 : t.2.1.val < j`. Apply the tactic sequence `by_contra h; apply hs; have : (t.2.1 : ℕ) < t.2.2 := hab; constructor <;> intro h' <;> omega`. Establish `h2 : j ≤ t.2.2.val`. Apply the tactic sequence `by_contra h; apply hs; constructor <;> intro _ <;> omega`. Establish `he : eW Ψ N j t.1 t.2.1 - eW Ψ N j t.1 t.2.2 = 1`.

Unfold `eW; rw [if_neg (by omega), if_pos h2]; norm_num`. Simplify using `only [hab, hs, and_false, if_false, one_mul, not_false_eq_true, and_self, if_true, he]`. Simplify using `[hab]`. Establish `hcR : PR.coeff k = (D.factorial : ℝ) * ((∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1))`. Rewrite using `[hPRdef, Finset.prod_congr rfl (fun t _ => hsplit t), Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]`.

Use `set Q : Polynomial ℝ := ∏ t ∈ idxC Ψ N j, (Polynomial.C (1 / ((t.2.2 : ℝ) - t.2.1)) + Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X) with hQ`. Establish `hQ0 : Q.coeff 0 = ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)`. Rewrite using `[Polynomial.coeff_zero_eq_eval_zero, hQ, Polynomial.eval_prod]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `e : Polynomial.C (D.factorial : ℝ) * (Polynomial.C (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X ^ (idxS Ψ N j).card * Q) = Polynomial.C ((D.factorial : ℝ) * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * (Polynom …`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', if_pos hk.le, hk, Nat.sub_self, hQ0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hcL, hPLR, hcR]`.
-/
theorem weyl_coeff (j : ℕ) (ν : Ψ → Fin N → ℝ) (n k : ℕ) (hD : Formalism.DegreeFormula.dimFl Ψ N = n + k)
    (hk : (idxS Ψ N j).card = k) :
    ((Formalism.DegreeFormula.dimFl Ψ N).choose n : ℝ) * degFlL Ψ N (a0Mu j ^ n * Formalism.DegreeFormula.linRoot ν ^ k) =
      ((Formalism.DegreeFormula.dimFl Ψ N).factorial : ℝ) *
        ((∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
          ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) := by
  set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef
  set μ : Pol Ψ N := a0Mu j with hμ
  set L : Pol Ψ N := Formalism.DegreeFormula.linRoot ν with hL
  have hW : ∀ ε : ℝ, degFlL Ψ N ((μ + C ε * L) ^ D) =
      (D.factorial : ℝ) * Formalism.DegreeFormula.weylProd (eW Ψ N j + ε • ν) := by
    intro ε
    have h := Formalism.DegreeFormula.flagDegFormula_statement Ψ N (eW Ψ N j + ε • ν)
    unfold Formalism.DegreeFormula.flagDeg at h
    rw [linRoot_add, linRoot_smul, linRoot_eW] at h
    rw [degFlL_apply]; exact h

  set PL : Polynomial ℝ := ∑ m ∈ range (D + 1),
    Polynomial.C ((D.choose m : ℝ) * degFlL Ψ N (μ ^ m * L ^ (D - m))) * Polynomial.X ^ (D - m) with hPLdef
  have hPL : ∀ ε : ℝ, PL.eval ε = degFlL Ψ N ((μ + C ε * L) ^ D) := by
    intro ε
    rw [add_pow, map_sum, hPLdef, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have e : μ ^ m * (C ε * L) ^ (D - m) * ((D.choose m : ℕ) : Pol Ψ N) =
        C (ε ^ (D - m) * (D.choose m : ℝ)) * (μ ^ m * L ^ (D - m)) := by
      rw [map_mul, map_pow, map_natCast]; ring
    rw [e, degFlL_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

  set F : Ψ × Fin N × Fin N → Polynomial ℝ := fun t =>
    if t.2.1 < t.2.2 then Polynomial.C ((eW Ψ N j t.1 t.2.1 - eW Ψ N j t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) +
      Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1 with hFdef
  set PR : Polynomial ℝ := Polynomial.C (D.factorial : ℝ) * ∏ t, F t with hPRdef
  have hPR : ∀ ε : ℝ, PR.eval ε = (D.factorial : ℝ) * Formalism.DegreeFormula.weylProd (eW Ψ N j + ε • ν) := by
    intro ε
    rw [hPRdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Formalism.DegreeFormula.weylProd,
      Fintype.prod_prod_type]
    congr 1
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
    simp only [hFdef]
    split_ifs
    · simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    · simp
  have hPLR : PL = PR := Polynomial.funext (fun ε => by rw [hPL, hPR, hW])

  have hcL : PL.coeff k = (D.choose n : ℝ) * degFlL Ψ N (μ ^ n * L ^ k) := by
    rw [hPLdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one, show D - n = k by omega]
    · intro m hm hmn
      have := Finset.mem_range.mp hm
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hsplit : ∀ t, F t = (if t ∈ idxS Ψ N j then
      Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1) *
      (if t ∈ idxC Ψ N j then Polynomial.C (1 / ((t.2.2 : ℝ) - t.2.1)) +
        Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1) := by
    intro t
    simp only [hFdef, idxS, idxC, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hab : t.2.1 < t.2.2
    · by_cases hs : (t.2.1.val < j ↔ t.2.2.val < j)
      · have he : eW Ψ N j t.1 t.2.1 = eW Ψ N j t.1 t.2.2 := by
          unfold eW
          by_cases h1 : j ≤ t.2.1.val
          · have h2 : j ≤ t.2.2.val := by omega
            simp [h1, h2]
          · have h2 : ¬ j ≤ t.2.2.val := by omega
            simp [h1, h2]
        simp only [hab, hs, and_self, if_true, not_true, and_false, if_false, mul_one, he, sub_self, zero_div,
          map_zero, zero_add]
      · have h1 : t.2.1.val < j := by
          by_contra h; apply hs; have : (t.2.1 : ℕ) < t.2.2 := hab; constructor <;> intro h' <;> omega
        have h2 : j ≤ t.2.2.val := by
          by_contra h; apply hs; constructor <;> intro _ <;> omega
        have he : eW Ψ N j t.1 t.2.1 - eW Ψ N j t.1 t.2.2 = 1 := by
          unfold eW; rw [if_neg (by omega), if_pos h2]; norm_num
        simp only [hab, hs, and_false, if_false, one_mul, not_false_eq_true, and_self, if_true, he]
    · simp [hab]
  have hcR : PR.coeff k = (D.factorial : ℝ) *
      ((∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
        ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) := by
    rw [hPRdef, Finset.prod_congr rfl (fun t _ => hsplit t), Finset.prod_mul_distrib,
      Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter, Finset.prod_mul_distrib,
      Finset.prod_const, ← map_prod]
    set Q : Polynomial ℝ := ∏ t ∈ idxC Ψ N j, (Polynomial.C (1 / ((t.2.2 : ℝ) - t.2.1)) +
        Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X) with hQ
    have hQ0 : Q.coeff 0 = ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1) := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hQ, Polynomial.eval_prod]
      refine Finset.prod_congr rfl (fun t _ => ?_)
      simp
    have e : Polynomial.C (D.factorial : ℝ) *
        (Polynomial.C (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
          Polynomial.X ^ (idxS Ψ N j).card * Q) =
        Polynomial.C ((D.factorial : ℝ) * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
          (Polynomial.X ^ (idxS Ψ N j).card * Q) := by
      rw [map_mul]; ring
    rw [e, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', if_pos hk.le, hk, Nat.sub_self, hQ0]
    ring
  rw [← hcL, hPLR, hcR]

end WeylPolynomialAlgebra

namespace WeylPolynomialAlgebra

open Formalism.ShimuraLimitIdentity (Pol)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def apolL {σ : Type*} (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ where
  toFun := apol P
  map_add' := apol_add P
  map_smul' c g := by rw [apol_smul]; rfl

def PhiL (j n : ℕ) : Pol Ψ N →ₗ[ℝ] ℝ := (degFlL Ψ N).comp (LinearMap.mulLeft ℝ (a0Mu j ^ n))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem PhiL_apply (j n : ℕ) (g : Pol Ψ N) : PhiL j n g = degFlL Ψ N (a0Mu j ^ n * g) := rfl

/- English proof (translation)
Rewrite using `[MvPolynomial.C_mul', map_smul, smul_eq_mul]`.
-/
theorem PhiL_C_mul (j n : ℕ) (a : ℝ) (g : Pol Ψ N) : PhiL j n (C a * g) = a * PhiL j n g := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[MvPolynomial.C_mul', map_smul, smul_eq_mul]`.
-/
theorem apolL_C_mul {σ : Type*} (P : MvPolynomial σ ℝ) (a : ℝ) (g : MvPolynomial σ ℝ) :
    apolL P (C a * g) = a * apolL P g := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

/- English proof (translation)
Unfold `Formalism.DegreeFormula.linRoot`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]`.
-/
theorem linRoot_eq_smul (ν : Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot ν = ∑ x : Ψ × Fin N, (-ν x.1 x.2) • (X x : Pol Ψ N) := by
  unfold Formalism.DegreeFormula.linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]

/- English proof (translation)
The claim follows from `(isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)`.
-/
theorem ell_homog (t : Ψ × Fin N × Fin N) : (ell t : Pol Ψ N).IsHomogeneous 1 :=
  (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)

/- English proof (translation)
Use `IsHomogeneous.prod (idxS Ψ N j) (fun t => (ell t : Pol Ψ N)) (fun _ => 1) (fun t _ => ell_homog t)` as an intermediate fact. Simplify using `using this`.
-/
theorem fib_homog (j : ℕ) : (∏ t ∈ idxS Ψ N j, ell t : Pol Ψ N).IsHomogeneous (idxS Ψ N j).card := by
  have := IsHomogeneous.prod (idxS Ψ N j) (fun t => (ell t : Pol Ψ N)) (fun _ => 1) (fun t _ => ell_homog t)
  simpa using this

/- English proof (translation)
Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `t ht`. Establish `hab : t.2.1 < t.2.2` using `(Finset.mem_filter.mp ht).2.1`. Unfold `ell`. Rewrite using `[sub_ne_zero]`.

Introduce `h`. Use `MvPolynomial.X_injective (σ := Ψ × Fin N) (R := ℝ) h` as an intermediate fact. Simplify using `only [Prod.mk.injEq, true_and] at this`. Conclude with `absurd this hab.ne`.
-/
theorem fib_ne_zero (j : ℕ) : (∏ t ∈ idxS Ψ N j, ell t : Pol Ψ N) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro t ht
  have hab : t.2.1 < t.2.2 := (Finset.mem_filter.mp ht).2.1
  unfold ell
  rw [sub_ne_zero]
  intro h
  have := MvPolynomial.X_injective (σ := Ψ × Fin N) (R := ℝ) h
  simp only [Prod.mk.injEq, true_and] at this
  exact absurd this hab.ne

/- English proof (translation)
Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Simplify using `[ell]`.
-/
theorem eval_fib (j : ℕ) (v : Ψ × Fin N → ℝ) :
    eval v (∏ t ∈ idxS Ψ N j, ell t : Pol Ψ N) = ∏ t ∈ idxS Ψ N j, (v (t.1, t.2.1) - v (t.1, t.2.2)) := by
  rw [map_prod]; refine Finset.prod_congr rfl (fun t _ => ?_); simp [ell]

/- English proof (translation)
Establish `h2 : (∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j) : Pol Ψ N)).IsHomogeneous (∑ _τ : Ψ, (j.choose 2 + (N - j).choose 2))`. Use `IsHomogeneous.prod _ _ _ (fun τ _ => ?_)` and prove the remaining obligations. Use `(BlockVandermondeForms.vdm_homog τ (Formalism.ShimuraLimitIdentity.top N j)).mul (BlockVandermondeForms.vdm_homog τ (smallBlock N j))` as an intermediate fact. Rewrite `this` using `[BlockVandermondeForms.card_top N j hj, BlockVandermondeForms.card_smallBlock]`. Then use the resulting hypothesis. Establish `hf : fibreVandermondeProduct (Ψ` using `Ψ) (N := N) j 1 = ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j)) := by`.

Unfold `fibreVandermondeProduct`. Rewrite using `[map_one, one_mul]`. Establish `hk` using `(fib_homog (Ψ := Ψ) (N := N) j).inj_right (by rw [← fib_eq, hf]; exact h2) (fib_ne_zero j)`. Rewrite using `[hk]`. Simplify using `only [Finset.sum_const, Finset.card_univ, smul_eq_mul, a0n, Formalism.DegreeFormula.dimFl]`.

Establish `hN : N = j + (N - j)` using `by omega`. Establish `e2 : N * (N - 1) / 2 = N.choose 2` using `(Nat.choose_two_right N).symm`. Rewrite using `[e2]`. Use `conv_lhs => rw [hN]`. Rewrite using `[BlockVandermondeForms.add_choose_two]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dim_split (j : ℕ) (hj : j ≤ N) :
    Formalism.DegreeFormula.dimFl Ψ N = a0n Ψ N j + (idxS Ψ N j).card := by
  have h2 : (∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j) : Pol Ψ N)).IsHomogeneous
      (∑ _τ : Ψ, (j.choose 2 + (N - j).choose 2)) := by
    refine IsHomogeneous.prod _ _ _ (fun τ _ => ?_)
    have := (BlockVandermondeForms.vdm_homog τ (Formalism.ShimuraLimitIdentity.top N j)).mul (BlockVandermondeForms.vdm_homog τ (smallBlock N j))
    rwa [BlockVandermondeForms.card_top N j hj, BlockVandermondeForms.card_smallBlock] at this
  have hf : fibreVandermondeProduct (Ψ := Ψ) (N := N) j 1 = ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j)) := by
    unfold fibreVandermondeProduct; rw [map_one, one_mul]
  have hk := (fib_homog (Ψ := Ψ) (N := N) j).inj_right (by rw [← fib_eq, hf]; exact h2) (fib_ne_zero j)
  rw [hk]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, a0n, Formalism.DegreeFormula.dimFl]
  have hN : N = j + (N - j) := by omega
  have e2 : N * (N - 1) / 2 = N.choose 2 := (Nat.choose_two_right N).symm
  rw [e2]
  conv_lhs => rw [hN]
  rw [BlockVandermondeForms.add_choose_two]
  ring

end WeylPolynomialAlgebra

open WeylPolynomialAlgebra

/- English proof (translation)
Rewrite using `[div_mul_eq_mul_div, eq_div_iff hf]`. Take the linear combination `(-(K * e * f)) * hs`.
-/
theorem mul_eq_sign_rearrange (K e s f : ℝ) (hf : f ≠ 0) (hs : s * s = 1) : K * e = K * s / f * (f * s * e) := by
  rw [div_mul_eq_mul_div, eq_div_iff hf]
  linear_combination (-(K * e * f)) * hs

/- English proof (translation)
Introduce `Ψ _ _ N j hj`. Use `set n := a0n Ψ N j`. Use `set k := (idxS Ψ N j).card with hkdef`. Use `set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef`. Establish `hD : D = n + k` using `dim_split j hj`.

Use `set fib : Formalism.ShimuraLimitIdentity.Pol Ψ N := ∏ t ∈ idxS Ψ N j, ell t with hfib`. Use `set K0 : ℝ := (D.factorial : ℝ) * (∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) * (∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) / (D.choose n : ℝ) with hK0`. Establish `hpos : ∀ s : Finset (Ψ × Fin N × Fin N), (∀ t ∈ s, t.2.1 < t.2.2) → 0 < ∏ t ∈ s, 1 / ((t.2.2 : ℝ) - t.2.1)`. Introduce `s hs`. Use `Finset.prod_pos (fun t ht => ?_)` and prove the remaining obligations.

Establish `: (t.2.1 : ℝ) < t.2.2` using `by exact_mod_cast (hs t ht)`. Conclude with `one_div_pos.mpr (by linarith)`. Establish `hK0pos : 0 < K0`. Establish `h1` using `hpos (idxS Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)`. Establish `h2` using `hpos (idxC Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)`.

Establish `h3 : (0 : ℝ) < (D.choose n : ℝ)` using `by exact_mod_cast Nat.choose_pos (by omega)`. Establish `h4 : (0 : ℝ) < (D.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos D`. Check the signs of the components of the expression. Establish `hPhi : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = K0 * eval (fun x => ν x.1 x.2) fib`. Introduce `ν`.

Establish `hw` using `weyl_coeff j ν n k hD hkdef.symm`. Rewrite using `[PhiL_apply, eval_fib]`. Establish `hc : (D.choose n : ℝ) ≠ 0` using `by exact_mod_cast (Nat.choose_pos (by omega)).ne'`. Establish `e : ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1) = (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)) * ∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `hw` using `[e]`. Rewrite using `[hK0]`. Clear the denominators using the available nonvanishing facts.

Combine the linear relations using `[hw]`. Establish `hApol : ∀ ν : Ψ → Fin N → ℝ, apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) = (k.factorial : ℝ) * (-1) ^ k * eval (fun x => ν x.1 x.2) fib`. Introduce `ν`. Use `show apol fib _ = _`. Rewrite using `[linRoot_eq_smul, apol_pow fib k (fib_homog j), eval_fib, eval_fib]`.

Establish `e : ∏ t ∈ idxS Ψ N j, (-ν t.1 t.2.1 - -ν t.1 t.2.2) = (-1) ^ k * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)`. Rewrite using `[hkdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Use `set c : ℝ := K0 * (-1) ^ k / (k.factorial : ℝ) with hc`. Establish `hkf : (k.factorial : ℝ) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos k).ne'`. Establish `hagree : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = c * apolL fib (Formalism.DegreeFormula.linRoot ν ^ k)`. Introduce `ν`.

Rewrite using `[hPhi, hApol, hc]`. Establish `h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; norm_num`. Conclude with `mul_eq_sign_rearrange K0 _ _ _ hkf h1`. Establish `hpol` using `polarization (fun t => (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) (idxS Ψ N j)`. Establish `hsumS : ∀ S : Finset (Ψ × Fin N × Fin N), (∑ t ∈ S, (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) = Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t)`.

Introduce `S`. Rewrite using `[linRoot_sum]`. Conclude with `Finset.sum_congr rfl (fun t _ => (linRoot_nuT t).symm)`. Establish `hcast : ∀ S : Finset (Ψ × Fin N × Fin N), ((-1 : Formalism.ShimuraLimitIdentity.Pol Ψ N) ^ ((idxS Ψ N j).card - S.card)) = C ((-1 : ℝ) ^ ((idxS Ψ N j).card - S.card))`. Introduce `S`.

Rewrite using `[map_pow, map_neg, map_one]`. Rewrite `hpol` using `[← hfib]`. Simplify using `only [hsumS, hcast] at hpol`. Rewrite using `[show (((idxS Ψ N j).card.factorial : ℕ) : Formalism.ShimuraLimitIdentity.Pol Ψ N) = C ((k.factorial : ℕ) : ℝ) by`. Rewrite `hpol` using `[map_natCast]]`.

Establish `hP` using `congrArg (PhiL j n) hpol`. Establish `hA` using `congrArg (apolL fib) hpol`. Rewrite `hP` using `[PhiL_C_mul, map_sum]`. Rewrite `hA` using `[apolL_C_mul, map_sum]`. Simplify using `only [PhiL_C_mul, apolL_C_mul, ← hkdef, hagree] at hP hA`.

Establish `hmain : PhiL j n fib = c * apolL fib fib`. Establish `e1 : ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) * (c * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k)) = c * ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT …`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun S _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hP` using `[e1, ← hA]`. Establish `: (k.factorial : ℝ) * PhiL j n fib = (k.factorial : ℝ) * (c * apolL fib fib)` using `by rw [hP]; ring`. Conclude with `mul_left_cancel₀ hkf this`. Establish `hapos : 0 < apolL fib fib` using `apol_self_pos fib (fib_ne_zero j)`. Establish `hcne : c ≠ 0`.

Rewrite using `[hc]; have : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)`. Conclude with `div_ne_zero (mul_ne_zero hK0pos.ne' this) hkf`. Establish `hJ : degFlL Ψ N (a0JP (Ψ` using `Ψ) (N := N) j n 1) = PhiL j n fib := by`. Rewrite using `[PhiL_apply, hfib, ← fib_eq]`. Both sides reduce to the same expression.

Rewrite using `[hJ, hmain]`. Conclude with `mul_ne_zero hcne hapos.ne'`.
-/
theorem flag_integral_nonzero : FlagIntegralNonzero := by
  intro Ψ _ _ N j hj
  set n := a0n Ψ N j
  set k := (idxS Ψ N j).card with hkdef
  set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef
  have hD : D = n + k := dim_split j hj
  set fib : Formalism.ShimuraLimitIdentity.Pol Ψ N := ∏ t ∈ idxS Ψ N j, ell t with hfib

  set K0 : ℝ := (D.factorial : ℝ) * (∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) *
    (∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) / (D.choose n : ℝ) with hK0
  have hpos : ∀ s : Finset (Ψ × Fin N × Fin N), (∀ t ∈ s, t.2.1 < t.2.2) →
      0 < ∏ t ∈ s, 1 / ((t.2.2 : ℝ) - t.2.1) := by
    intro s hs
    refine Finset.prod_pos (fun t ht => ?_)
    have : (t.2.1 : ℝ) < t.2.2 := by exact_mod_cast (hs t ht)
    exact one_div_pos.mpr (by linarith)
  have hK0pos : 0 < K0 := by
    have h1 := hpos (idxS Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have h2 := hpos (idxC Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have h3 : (0 : ℝ) < (D.choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have h4 : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos D
    positivity

  have hPhi : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) =
      K0 * eval (fun x => ν x.1 x.2) fib := by
    intro ν
    have hw := weyl_coeff j ν n k hD hkdef.symm
    rw [PhiL_apply, eval_fib]
    have hc : (D.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have e : ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1) =
        (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)) * ∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1) := by
      rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl (fun t _ => ?_); ring
    rw [e] at hw
    rw [hK0]
    field_simp
    linarith [hw]

  have hApol : ∀ ν : Ψ → Fin N → ℝ, apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) =
      (k.factorial : ℝ) * (-1) ^ k * eval (fun x => ν x.1 x.2) fib := by
    intro ν
    show apol fib _ = _
    rw [linRoot_eq_smul, apol_pow fib k (fib_homog j), eval_fib, eval_fib]
    have e : ∏ t ∈ idxS Ψ N j, (-ν t.1 t.2.1 - -ν t.1 t.2.2) =
        (-1) ^ k * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) := by
      rw [hkdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun t _ => ?_); ring
    rw [e]; ring

  set c : ℝ := K0 * (-1) ^ k / (k.factorial : ℝ) with hc
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hagree : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = c * apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) := by
    intro ν
    rw [hPhi, hApol, hc]
    have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    exact mul_eq_sign_rearrange K0 _ _ _ hkf h1

  have hpol := polarization (fun t => (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) (idxS Ψ N j)
  have hsumS : ∀ S : Finset (Ψ × Fin N × Fin N), (∑ t ∈ S, (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) =
      Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) := by
    intro S; rw [linRoot_sum]; exact Finset.sum_congr rfl (fun t _ => (linRoot_nuT t).symm)
  have hcast : ∀ S : Finset (Ψ × Fin N × Fin N), ((-1 : Formalism.ShimuraLimitIdentity.Pol Ψ N) ^ ((idxS Ψ N j).card - S.card)) =
      C ((-1 : ℝ) ^ ((idxS Ψ N j).card - S.card)) := by
    intro S; rw [map_pow, map_neg, map_one]
  rw [← hfib] at hpol
  simp only [hsumS, hcast] at hpol
  rw [show (((idxS Ψ N j).card.factorial : ℕ) : Formalism.ShimuraLimitIdentity.Pol Ψ N) = C ((k.factorial : ℕ) : ℝ) by
    rw [map_natCast]] at hpol
  have hP := congrArg (PhiL j n) hpol
  have hA := congrArg (apolL fib) hpol
  rw [PhiL_C_mul, map_sum] at hP
  rw [apolL_C_mul, map_sum] at hA
  simp only [PhiL_C_mul, apolL_C_mul, ← hkdef, hagree] at hP hA
  have hmain : PhiL j n fib = c * apolL fib fib := by
    have e1 : ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) *
        (c * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k)) =
        c * ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) *
          apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun S _ => ?_); ring
    rw [e1, ← hA] at hP
    have : (k.factorial : ℝ) * PhiL j n fib = (k.factorial : ℝ) * (c * apolL fib fib) := by rw [hP]; ring
    exact mul_left_cancel₀ hkf this
  have hapos : 0 < apolL fib fib := apol_self_pos fib (fib_ne_zero j)
  have hcne : c ≠ 0 := by
    rw [hc]; have : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact div_ne_zero (mul_ne_zero hK0pos.ne' this) hkf
  have hJ : degFlL Ψ N (a0JP (Ψ := Ψ) (N := N) j n 1) = PhiL j n fib := by
    rw [PhiL_apply, hfib, ← fib_eq]; rfl
  rw [hJ, hmain]
  exact mul_ne_zero hcne hapos.ne'

end Formalism.L2.Geo
