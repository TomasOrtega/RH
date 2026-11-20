import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerMonomial
import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialMemWeightSpaceIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

structure MonomialGradedLattice (p : ℕ) {K : Type} [Field K] {σ : Type} (Q : MvPolynomial σ K → Prop) : Prop where
  zero : Q 0
  add : ∀ F G, Q F → Q G → Q (F + G)
  lin : ∀ u : MvPolynomial σ K →ₗ[K] MvPolynomial σ K,
    (∀ m c, Q (monomial m c) → Q (u (monomial m c))) → ∀ F, Q F → Q (u F)
  step : ∀ (m m' : σ →₀ ℕ) (c : K) (z : ℤ), Q (monomial m c) →
    (z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) →
    Q (monomial m' (c * (z : K)))

section

variable {K : Type} [Field K] [CharZero K] {σ : Type}

/- English proof (translation)
Introduce `k x hx`. Use `show Q (((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) x)`. Use `hQ.lin ((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) ?_ x hx` and prove the remaining obligations. Introduce `m c hmc`. Use `set mj : ℕ → (σ →₀ ℕ) := fun j => (m.update w (m w - j)).update v (m v + j) with hmj`.

Establish `hmjw : ∀ j, mj j w = m w - j` using `fun j => by`. Simplify using `[hmj, Finsupp.update_apply, Ne.symm hvw]`. Establish `hmjv : ∀ j, mj j v = m v + j` using `fun j => by`. Simplify using `[hmj, Finsupp.update_apply]`. Establish `hmjo : ∀ j i, i ≠ v → i ≠ w → mj j i = m i` using `fun j i hiv hiw => by`.

Simplify using `[hmj, Finsupp.update_apply, hiv, hiw]`. Establish `hT : ∀ j, (polarizationOperator K v w ^ j) (monomial m c) = monomial (mj j) (c * ((m w).descFactorial j : K))`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`.

Establish `h0 : mj 0 = m`. Use extensionality with `i`. Distinguish the cases in `hiv : i = v`. Rewrite using `[hiv, hmjv]`. Both sides reduce to the same expression.

Distinguish the cases in `hiw : i = w`. Rewrite using `[hiw, hmjw]`. Both sides reduce to the same expression. Conclude with `hmjo 0 i hiv hiw`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Consider the case `succ j ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih]`. Use `show X v * pderiv w (monomial (mj j) (c * ((m w).descFactorial j : K))) = _`. Rewrite using `[MvPolynomial.pderiv_monomial, hmjw, show (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) 1 from rfl, MvPolynomial.monomial_mul, one_mul]`.

Distinguish the cases in `hj : j < m w`. Establish `hexp : Finsupp.single v 1 + (mj j - Finsupp.single w 1) = mj (j + 1)`. Use extensionality with `i`. Distinguish the cases in `hiv : i = v`. Rewrite using `[hiv]`.

Apply the tactic sequence `simp [hmjv, Finsupp.single_apply, hvw, Ne.symm hvw] <;> omega`. Distinguish the cases in `hiw : i = w`. Rewrite using `[hiw]`. Apply the tactic sequence `simp [hmjw, Finsupp.single_apply, hvw, Ne.symm hvw] <;> omega`. Simplify using `[hmjo j i hiv hiw, hmjo (j + 1) i hiv hiw, Finsupp.single_apply, Ne.symm hiv, Ne.symm hiw]`.

Rewrite using `[hexp, Nat.descFactorial_succ, Nat.cast_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (m w).descFactorial (j + 1) = 0` using `Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)`. Establish `h2 : m w - j = 0` using `by omega`.

Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules. Establish `hk : (k.factorial : K) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`. Establish `hval : ((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) (monomial m c) = monomial (mj k) (c * (((ε ^ k * ((m w).choose k : ℤ) : ℤ)) : K))`. Rewrite using `[smul_pow, LinearMap.smul_apply, LinearMap.smul_apply, hT k, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, Nat.descFactorial_eq_factorial_mul_choose]`.

Use `congr 1`. Simplify using `only [smul_eq_mul]`. Use `push_cast`. Rewrite using `[inv_mul_eq_iff_eq_mul₀ hk]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hval]`. Use `hQ.step m (mj k) c _ hmc ?_` and prove the remaining obligations. Distinguish the cases in `hkw : k ≤ m w`. Use `right`. Establish `hz : padicValInt p (ε ^ k * ((m w).choose k : ℤ)) = padicValNat p ((m w).choose k)`.

Simplify using `[padicValInt, Int.natAbs_mul, Int.natAbs_pow, hε]`. Rewrite using `[hz]`. Use `set s : Finset σ := m.support ∪ {v, w} with hs`. Establish `hvs : v ∈ s` using `by simp [hs]`. Establish `hws : w ∈ s.erase v` using `by simp [hs, Ne.symm hvw]`.

Establish `hsub1 : m.support ⊆ s` using `Finset.subset_union_left`. Establish `hsub2 : (mj k).support ⊆ s`. Introduce `i hi`. Rewrite `hi` using `[Finsupp.mem_support_iff]`. Distinguish the cases in `hiv : i = v`.

Rewrite using `[hiv]`. Simplify using `[hs]`. Distinguish the cases in `hiw : i = w`. Rewrite using `[hiw]`. Simplify using `[hs]`.

Rewrite `hi` using `[hmjo k i hiv hiw]`. Conclude with `Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hi)`. Establish `hE : expFact m = (m v).factorial * ((m w).factorial * ∏ i ∈ (s.erase v).erase w, (m i).factorial)`. Unfold `expFact`. Rewrite using `[Finsupp.prod_of_support_subset m hsub1 (fun _ k => k.factorial) (fun _ _ => rfl), ← Finset.mul_prod_erase s _ hvs, ← Finset.mul_prod_erase (s.erase v) _ hws]`.

Establish `hE' : expFact (mj k) = (m v + k).factorial * ((m w - k).factorial * ∏ i ∈ (s.erase v).erase w, (m i).factorial)`. Unfold `expFact`. Rewrite using `[Finsupp.prod_of_support_subset (mj k) hsub2 (fun _ k => k.factorial) (fun _ _ => rfl), ← Finset.mul_prod_erase s _ hvs, ← Finset.mul_prod_erase (s.erase v) _ hws, hmjv, hmjw]`. Use `congr 2`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hiw : i ≠ w` using `Finset.ne_of_mem_erase hi`. Establish `hiv : i ≠ v` using `Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)`. Rewrite using `[hmjo k i hiv hiw]`. Establish `hid : expFact m * (m v + k).choose k = expFact (mj k) * (m w).choose k`. Establish `e1` using `Nat.choose_mul_factorial_mul_factorial (show k ≤ m v + k by omega)`.

Rewrite `e1` using `[Nat.add_sub_cancel]`. Establish `e2` using `Nat.choose_mul_factorial_mul_factorial hkw`. Rewrite using `[hE, hE', ← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hEpos : expFact m ≠ 0`.

Rewrite using `[hE]`. Check the signs of the components of the expression. Establish `hE'pos : expFact (mj k) ≠ 0`. Rewrite using `[hE']`. Check the signs of the components of the expression.

Establish `hC1 : (m v + k).choose k ≠ 0` using `(Nat.choose_pos (by omega)).ne'`. Establish `hC2 : (m w).choose k ≠ 0` using `(Nat.choose_pos hkw).ne'`. Establish `hv` using `congrArg (padicValNat p) hid`. Rewrite `hv` using `[padicValNat.mul hEpos hC1, padicValNat.mul hE'pos hC2]`. Use linear arithmetic over natural numbers and integers.

Use `left`. Establish `: (m w).choose k = 0` using `Nat.choose_eq_zero_of_lt (by omega)`. Simplify using `[this]`.
-/
theorem divided_powers_preserve_polarization (p : ℕ) [Fact p.Prime] (Q : MvPolynomial σ K → Prop) (hQ : MonomialGradedLattice p Q) (ε : ℤ)
    (hε : ε.natAbs = 1) (v w : σ) (hvw : v ≠ w) : DividedPowersPreserve Q ((ε : K) • polarizationOperator K v w) := by
  classical
  intro k x hx
  show Q (((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) x)
  refine hQ.lin ((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) ?_ x hx
  intro m c hmc

  set mj : ℕ → (σ →₀ ℕ) := fun j => (m.update w (m w - j)).update v (m v + j) with hmj
  have hmjw : ∀ j, mj j w = m w - j := fun j => by
    simp [hmj, Finsupp.update_apply, Ne.symm hvw]
  have hmjv : ∀ j, mj j v = m v + j := fun j => by
    simp [hmj, Finsupp.update_apply]
  have hmjo : ∀ j i, i ≠ v → i ≠ w → mj j i = m i := fun j i hiv hiw => by
    simp [hmj, Finsupp.update_apply, hiv, hiw]
  have hT : ∀ j, (polarizationOperator K v w ^ j) (monomial m c) =
      monomial (mj j) (c * ((m w).descFactorial j : K)) := by
    intro j
    induction j with
    | zero =>
      have h0 : mj 0 = m := by
        ext i
        by_cases hiv : i = v
        · rw [hiv, hmjv]
          rfl
        · by_cases hiw : i = w
          · rw [hiw, hmjw]
            rfl
          · exact hmjo 0 i hiv hiw
      rw [h0]
      simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      show X v * pderiv w (monomial (mj j) (c * ((m w).descFactorial j : K))) = _
      rw [MvPolynomial.pderiv_monomial, hmjw,
        show (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) 1 from rfl,
        MvPolynomial.monomial_mul, one_mul]
      by_cases hj : j < m w
      · have hexp : Finsupp.single v 1 + (mj j - Finsupp.single w 1) = mj (j + 1) := by
          ext i
          by_cases hiv : i = v
          · rw [hiv]
            simp [hmjv, Finsupp.single_apply, hvw, Ne.symm hvw] <;> omega
          · by_cases hiw : i = w
            · rw [hiw]
              simp [hmjw, Finsupp.single_apply, hvw, Ne.symm hvw] <;> omega
            · simp [hmjo j i hiv hiw, hmjo (j + 1) i hiv hiw, Finsupp.single_apply, Ne.symm hiv,
                Ne.symm hiw]
        rw [hexp, Nat.descFactorial_succ, Nat.cast_mul]
        congr 1
        ring
      · have h1 : (m w).descFactorial (j + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h2 : m w - j = 0 := by omega
        rw [h1, h2]
        simp
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hval : ((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) (monomial m c) =
      monomial (mj k) (c * (((ε ^ k * ((m w).choose k : ℤ) : ℤ)) : K)) := by
    rw [smul_pow, LinearMap.smul_apply, LinearMap.smul_apply, hT k, MvPolynomial.smul_monomial,
      MvPolynomial.smul_monomial, Nat.descFactorial_eq_factorial_mul_choose]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    rw [inv_mul_eq_iff_eq_mul₀ hk]
    ring
  rw [hval]
  refine hQ.step m (mj k) c _ hmc ?_
  by_cases hkw : k ≤ m w
  · right
    have hz : padicValInt p (ε ^ k * ((m w).choose k : ℤ)) = padicValNat p ((m w).choose k) := by
      simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow, hε]
    rw [hz]
    set s : Finset σ := m.support ∪ {v, w} with hs
    have hvs : v ∈ s := by simp [hs]
    have hws : w ∈ s.erase v := by simp [hs, Ne.symm hvw]
    have hsub1 : m.support ⊆ s := Finset.subset_union_left
    have hsub2 : (mj k).support ⊆ s := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi
      by_cases hiv : i = v
      · rw [hiv]
        simp [hs]
      · by_cases hiw : i = w
        · rw [hiw]
          simp [hs]
        · rw [hmjo k i hiv hiw] at hi
          exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hi)
    have hE : expFact m = (m v).factorial * ((m w).factorial *
        ∏ i ∈ (s.erase v).erase w, (m i).factorial) := by
      unfold expFact
      rw [Finsupp.prod_of_support_subset m hsub1 (fun _ k => k.factorial) (fun _ _ => rfl),
        ← Finset.mul_prod_erase s _ hvs, ← Finset.mul_prod_erase (s.erase v) _ hws]
    have hE' : expFact (mj k) = (m v + k).factorial * ((m w - k).factorial *
        ∏ i ∈ (s.erase v).erase w, (m i).factorial) := by
      unfold expFact
      rw [Finsupp.prod_of_support_subset (mj k) hsub2 (fun _ k => k.factorial) (fun _ _ => rfl),
        ← Finset.mul_prod_erase s _ hvs, ← Finset.mul_prod_erase (s.erase v) _ hws, hmjv, hmjw]
      congr 2
      refine Finset.prod_congr rfl fun i hi => ?_
      have hiw : i ≠ w := Finset.ne_of_mem_erase hi
      have hiv : i ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      rw [hmjo k i hiv hiw]
    have hid : expFact m * (m v + k).choose k = expFact (mj k) * (m w).choose k := by
      have e1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ m v + k by omega)
      rw [Nat.add_sub_cancel] at e1
      have e2 := Nat.choose_mul_factorial_mul_factorial hkw
      rw [hE, hE', ← e1, ← e2]
      ring
    have hEpos : expFact m ≠ 0 := by
      rw [hE]
      positivity
    have hE'pos : expFact (mj k) ≠ 0 := by
      rw [hE']
      positivity
    have hC1 : (m v + k).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hC2 : (m w).choose k ≠ 0 := (Nat.choose_pos hkw).ne'
    have hv := congrArg (padicValNat p) hid
    rw [padicValNat.mul hEpos hC1, padicValNat.mul hE'pos hC2] at hv
    omega
  · left
    have : (m w).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]`. Simplify using `[hx, ih]`.

Use `first`. Consider the case `done`. Consider the case `module`. Consider the case `(rw [mul_comm, mul_smul]; module)`.
-/
theorem list_prod_eigen_shift {V : Type*} [AddCommGroup V] [Module K V] (E : Module.End K V) (x : V) (w : K)
    (hx : E x = w • x) (k : ℕ) :
    ((List.range k).map fun j : ℕ => E - (j : K) • (1 : Module.End K V)).prod x =
      (∏ j ∈ Finset.range k, (w - (j : K))) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp [hx, ih]
    first
      | done
      | module
      | (rw [mul_comm, mul_smul]; module)

/- English proof (translation)
Establish `h1 : (∏ j ∈ Finset.range k, (w - (j : ℤ))) = (k.factorial : ℤ) * Ring.choose w k`. Rewrite using `[← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose]`. Use `first`. Consider the case `rw [nsmul_eq_mul]`. Consider the case `rw [smul_eq_mul]`.

Consider the case `simp`. Establish `h2` using `congrArg (Int.cast (R := K)) h1`. Move the coercions through the operations in `at h2`. Conclude with `h2`.
-/
theorem prod_range_sub_eq_factorial_choose (w : ℤ) (k : ℕ) :
    (∏ j ∈ Finset.range k, ((w : K) - (j : K))) = (k.factorial : K) * ((Ring.choose w k : ℤ) : K) := by
  have h1 : (∏ j ∈ Finset.range k, (w - (j : ℤ))) = (k.factorial : ℤ) * Ring.choose w k := by
    rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose]
    first
      | rw [nsmul_eq_mul]
      | rw [smul_eq_mul]
      | simp
  have h2 := congrArg (Int.cast (R := K)) h1
  push_cast at h2
  exact h2

end

section

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}

open Classical in

def letterPolarization (K : Type) [Field K] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) :
    Module.End K (MvPolynomial (ι × Fin n) K) :=
  if l ∈ S then (if LL.vec l then polarizationOperator K (l, a) (l, b) else -(polarizationOperator K (l, b) (l, a))) else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gl_operator_eq_sum_letters (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    glOps K n LL S a b = ∑ l : ι, letterPolarization K LL S a b l := rfl

/- English proof (translation)
Establish `hne : ∀ x y : Fin n, ((l, x) : ι × Fin n) ≠ (l', y)` using `fun x y hxy => h (congrArg Prod.fst hxy)`. Establish `hc : ∀ x y x' y' : Fin n, Commute (polarizationOperator K (l, x) (l, y)) (polarizationOperator K (l', x') (l', y'))` using `fun x y x' y' => polarization_commute _ _ _ _ (hne _ _) (hne _ _) (hne _ _).symm`. Unfold `letterPolarization`. Distinguish the cases in `h1 : l ∈ S`. Distinguish the cases in `h2 : l' ∈ S`.

Rewrite using `[if_pos h1, if_pos h2]`. Apply the tactic sequence `by_cases v1 : LL.vec l = true <;> by_cases v2 : LL.vec l' = true`. Rewrite using `[if_pos v1, if_pos v2]`. Conclude with `hc _ _ _ _`. Rewrite using `[if_pos v1, if_neg v2]`.

Conclude with `(hc _ _ _ _).neg_right`. Rewrite using `[if_neg v1, if_pos v2]`. Conclude with `(hc _ _ _ _).neg_left`. Rewrite using `[if_neg v1, if_neg v2]`. Conclude with `(hc _ _ _ _).neg_left.neg_right`.

Rewrite using `[if_neg h2]`. Conclude with `Commute.zero_right _`. Rewrite using `[if_neg h1]`. Conclude with `Commute.zero_left _`.
-/
theorem letter_polarization_commute (LL : Letters ι) (S : Set ι) (a b : Fin n) (l l' : ι) (h : l ≠ l') :
    Commute (letterPolarization K LL S a b l) (letterPolarization K LL S a b l') := by
  have hne : ∀ x y : Fin n, ((l, x) : ι × Fin n) ≠ (l', y) := fun x y hxy => h (congrArg Prod.fst hxy)
  have hc : ∀ x y x' y' : Fin n, Commute (polarizationOperator K (l, x) (l, y)) (polarizationOperator K (l', x') (l', y')) :=
    fun x y x' y' => polarization_commute _ _ _ _ (hne _ _) (hne _ _) (hne _ _).symm
  unfold letterPolarization
  by_cases h1 : l ∈ S
  · by_cases h2 : l' ∈ S
    · rw [if_pos h1, if_pos h2]
      by_cases v1 : LL.vec l = true <;> by_cases v2 : LL.vec l' = true
      · rw [if_pos v1, if_pos v2]
        exact hc _ _ _ _
      · rw [if_pos v1, if_neg v2]
        exact (hc _ _ _ _).neg_right
      · rw [if_neg v1, if_pos v2]
        exact (hc _ _ _ _).neg_left
      · rw [if_neg v1, if_neg v2]
        exact (hc _ _ _ _).neg_left.neg_right
    · rw [if_neg h2]
      exact Commute.zero_right _
  · rw [if_neg h1]
    exact Commute.zero_left _

/- English proof (translation)
Unfold `letterPolarization`. Use `split_ifs with h1 h2`. Use `divided_powers_preserve_polarization p Q hQ 1 rfl (l, a) (l, b) (by simp [hab])` as an intermediate fact. Simplify using `using this`. Use `divided_powers_preserve_polarization p Q hQ (-1) rfl (l, b) (l, a) (by simp [Ne.symm hab])` as an intermediate fact.

Simplify using `using this`. Unfold `DividedPowersPreserve`. Introduce `k x hx`. Break down `k with _ | k` into its components or cases. Simplify using `using hx`.

Simplify using `using hQ.zero`.
-/
theorem divided_powers_preserve_letter (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (ι × Fin n) K → Prop) (hQ : MonomialGradedLattice p Q)
    (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (l : ι) : DividedPowersPreserve Q (letterPolarization K LL S a b l) := by
  unfold letterPolarization
  split_ifs with h1 h2
  · have := divided_powers_preserve_polarization p Q hQ 1 rfl (l, a) (l, b) (by simp [hab])
    simpa using this
  · have := divided_powers_preserve_polarization p Q hQ (-1) rfl (l, b) (l, a) (by simp [Ne.symm hab])
    simpa using this
  · unfold DividedPowersPreserve
    intro k x hx
    rcases k with _ | k
    · simpa using hx
    · simpa using hQ.zero

/- English proof (translation)
Rewrite using `[gl_operator_eq_sum_letters]`. Establish `key : ∀ s : Finset ι, DividedPowersPreserve Q (∑ l ∈ s, letterPolarization K LL S a b l)`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_empty]`.

Unfold `DividedPowersPreserve`. Introduce `k x hx`. Break down `k with _ | k` into its components or cases. Simplify using `using hx`. Simplify using `using hQ.zero`.

Introduce `l s hl ih`. Rewrite using `[Finset.sum_insert hl]`. Use `divided_powers_preserve_add Q hQ.zero hQ.add _ _ ?_ (divided_powers_preserve_letter p Q hQ LL S a b hab l) ih` and prove the remaining obligations. Conclude with `Commute.sum_right _ _ _ fun l' hl' => letter_polarization_commute LL S a b l l' (by rintro rfl; exact hl hl')`. Conclude with `key Finset.univ`.
-/
theorem divided_powers_preserve_gl_operator (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (ι × Fin n) K → Prop) (hQ : MonomialGradedLattice p Q)
    (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) : DividedPowersPreserve Q (glOps K n LL S a b) := by
  classical
  rw [gl_operator_eq_sum_letters]
  have key : ∀ s : Finset ι, DividedPowersPreserve Q (∑ l ∈ s, letterPolarization K LL S a b l) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty]
      unfold DividedPowersPreserve
      intro k x hx
      rcases k with _ | k
      · simpa using hx
      · simpa using hQ.zero
    · intro l s hl ih
      rw [Finset.sum_insert hl]
      refine divided_powers_preserve_add Q hQ.zero hQ.add _ _ ?_ (divided_powers_preserve_letter p Q hQ LL S a b hab l) ih
      exact Commute.sum_right _ _ _ fun l' hl' => letter_polarization_commute LL S a b l l' (by rintro rfl; exact hl hl')
  exact key Finset.univ

/- English proof (translation)
Break down `hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩` into its components or cases. Conclude with `divided_powers_preserve_gl_operator p Q hQ LL S a b hab k F hF`. Use `hQ.lin (binomE (glOps K n LL S) a k) ?_ F hF` and prove the remaining obligations. Introduce `m c hmc`. Use `set w : ℤ := ∑ l : ι, (if l ∈ S then (if LL.vec l then ((m (l, a) : ℕ) : ℤ) else -((m (l, a) : ℕ) : ℤ)) else 0) with hw`.

Establish `heig : glOps K n LL S a a (monomial m c) = (w : K) • monomial m c`. Rewrite using `[gl_operator_eq_sum_letters, LinearMap.sum_apply, hw]`. Use `push_cast`. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Unfold `letterPolarization polarizationOperator`. Use `split_ifs`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, LinearMap.coe_toAddHom]`. Express the relevant statement in the definitionally equal form `X (l, a) * (pderiv (l, a)) ((monomial m) c) = _`. Rewrite using `[MvPolynomial.X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]`.

Simplify using `only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Express the relevant statement in the definitionally equal form `-(X (l, a) * (pderiv (l, a)) ((monomial m) c)) = _`. Rewrite using `[MvPolynomial.X_mul_pderiv_monomial, neg_smul, Nat.cast_smul_eq_nsmul]`. Simplify using the standard rewrite rules. Establish `hprod` using `list_prod_eigen_shift (glOps K n LL S a a) (monomial m c) (w : K) heig k`.

Rewrite `hprod` using `[prod_range_sub_eq_factorial_choose w k]`. Establish `hk : (k.factorial : K) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`. Establish `key : binomE (glOps K n LL S) a k (monomial m c) = monomial m (c * ((Ring.choose w k : ℤ) : K))`. Unfold `binomE`. Rewrite using `[LinearMap.smul_apply, hprod, smul_smul, ← mul_assoc, inv_mul_cancel₀ hk, one_mul, MvPolynomial.smul_monomial]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `hQ.step m m c (Ring.choose w k) hmc (Or.inr (by omega))`.
-/
theorem integral_generators_preserve_lattice (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (ι × Fin n) K → Prop) (hQ : MonomialGradedLattice p Q)
    (LL : Letters ι) (S : Set ι) (u : Module.End K (MvPolynomial (ι × Fin n) K))
    (hu : u ∈ UZgens (glOps K n LL S)) (F : MvPolynomial (ι × Fin n) K) (hF : Q F) : Q (u F) := by
  classical
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · exact divided_powers_preserve_gl_operator p Q hQ LL S a b hab k F hF
  · refine hQ.lin (binomE (glOps K n LL S) a k) ?_ F hF
    intro m c hmc
    set w : ℤ := ∑ l : ι, (if l ∈ S then (if LL.vec l then ((m (l, a) : ℕ) : ℤ) else -((m (l, a) : ℕ) : ℤ))
      else 0) with hw
    have heig : glOps K n LL S a a (monomial m c) = (w : K) • monomial m c := by
      rw [gl_operator_eq_sum_letters, LinearMap.sum_apply, hw]
      push_cast
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold letterPolarization polarizationOperator
      split_ifs
      · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply,
          LinearMap.coe_toAddHom]
        change X (l, a) * (pderiv (l, a)) ((monomial m) c) = _
        rw [MvPolynomial.X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]
      · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
        change -(X (l, a) * (pderiv (l, a)) ((monomial m) c)) = _
        rw [MvPolynomial.X_mul_pderiv_monomial, neg_smul, Nat.cast_smul_eq_nsmul]
      · simp
    have hprod := list_prod_eigen_shift (glOps K n LL S a a) (monomial m c) (w : K) heig k
    rw [prod_range_sub_eq_factorial_choose w k] at hprod
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have key : binomE (glOps K n LL S) a k (monomial m c) = monomial m (c * ((Ring.choose w k : ℤ) : K)) := by
      unfold binomE
      rw [LinearMap.smul_apply, hprod, smul_smul, ← mul_assoc, inv_mul_cancel₀ hk, one_mul,
        MvPolynomial.smul_monomial]
      congr 1
      ring
    rw [key]
    exact hQ.step m m c (Ring.choose w k) hmc (Or.inr (by omega))

end

/- English proof (translation)
Use `haveI := hchar`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Introduce `n ι _ LL S u hu`. Take `⟨h0, hadd, _, _, _, hlin, hstep, hint, hmono, hiff⟩` from `h (ι × Fin n)`. Use `⟨fun F hF => ?_, fun F hF => ?_⟩` and prove the remaining obligations.

Establish `hQ : MonomialGradedLattice p (fun F : MvPolynomial (ι × Fin n) (KK O) => F ∈ IntPol O (ι × Fin n))`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hiff]`. Introduce `m`. Conclude with `⟨0, by simp⟩`.

Introduce `F G hF hG`. Rewrite `hF`, `hG`, the goal using `[hiff]`. Introduce `m`. Take `⟨a, ha⟩` from `hF m`. Take `⟨b, hb⟩` from `hG m`.

Conclude with `⟨a + b, by rw [MvPolynomial.coeff_add, ha, hb, map_add]⟩`. Introduce `u' hu' F hF`. Use `hint u' (fun m => ?_) F hF` and prove the remaining obligations. Establish `h1` using `hmono m 1`. Simplify using `only [Int.cast_one] at h1`.

Conclude with `hu' m 1 h1`. Introduce `m m' c z hmc _`. Rewrite `hmc`, the goal using `[hiff]`. Take `⟨o, ho⟩` from `hmc m`. Rewrite `ho` using `[MvPolynomial.coeff_monomial, if_pos rfl]`.

Introduce `m''`. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs`. Conclude with `⟨o * z, by rw [ho, map_mul, map_intCast]⟩`. Conclude with `⟨0, by simp⟩`.

Conclude with `integral_generators_preserve_lattice p _ hQ LL S u hu F hF`. Establish `hQ : MonomialGradedLattice p (fun F : MvPolynomial (ι × Fin n) (KK O) => InBB (O` using `O) p F) := ⟨h0, hadd, hlin, hstep⟩`. Conclude with `integral_generators_preserve_lattice p _ hQ LL S u hu F hF`.
-/
theorem char_zero_stability_of_closure {p : ℕ} (hp : p.Prime) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hchar : CharZero (KK O)) (h : FockLatticeClosure p O) : IntegralFormGeneratorsPreserveLattices p O := by
  classical
  haveI := hchar
  haveI : Fact p.Prime := ⟨hp⟩
  intro n ι _ LL S u hu
  obtain ⟨h0, hadd, _, _, _, hlin, hstep, hint, hmono, hiff⟩ := h (ι × Fin n)
  refine ⟨fun F hF => ?_, fun F hF => ?_⟩
  ·
    have hQ : MonomialGradedLattice p (fun F : MvPolynomial (ι × Fin n) (KK O) => F ∈ IntPol O (ι × Fin n)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hiff]
        intro m
        exact ⟨0, by simp⟩
      · intro F G hF hG
        rw [hiff] at hF hG ⊢
        intro m
        obtain ⟨a, ha⟩ := hF m
        obtain ⟨b, hb⟩ := hG m
        exact ⟨a + b, by rw [MvPolynomial.coeff_add, ha, hb, map_add]⟩
      · intro u' hu' F hF
        refine hint u' (fun m => ?_) F hF
        have h1 := hmono m 1
        simp only [Int.cast_one] at h1
        exact hu' m 1 h1
      · intro m m' c z hmc _
        rw [hiff] at hmc ⊢
        obtain ⟨o, ho⟩ := hmc m
        rw [MvPolynomial.coeff_monomial, if_pos rfl] at ho
        intro m''
        rw [MvPolynomial.coeff_monomial]
        split_ifs
        · exact ⟨o * z, by rw [ho, map_mul, map_intCast]⟩
        · exact ⟨0, by simp⟩
    exact integral_generators_preserve_lattice p _ hQ LL S u hu F hF
  · have hQ : MonomialGradedLattice p (fun F : MvPolynomial (ι × Fin n) (KK O) => InBB (O := O) p F) :=
      ⟨h0, hadd, hlin, hstep⟩
    exact integral_generators_preserve_lattice p _ hQ LL S u hu F hF

end Formalism.MainNotions.G.GLWeightTheory
