import Formalism.GradedWeylDivisibility.StatementB

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lhwinHt (r n : ℕ) : Fin r × Fin n → ℤ := fun v => (v.1.val : ℤ)

def LhwinShift {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (lhwinHt r n) (P.coeff k) (μ + k * δ)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Use `IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Establish `e : μ + μ' + (k : ℤ) * δ = (μ + (x.1 : ℤ) * δ) + (μ' + (x.2 : ℤ) * δ)`.

Rewrite using `[← hx']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(hP x.1).mul (hQ x.2)`.
-/
theorem lhwinShift_mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LhwinShift P μ δ) (hQ : LhwinShift Q μ' δ) : LhwinShift (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + (k : ℤ) * δ = (μ + (x.1 : ℤ) * δ) + (μ' + (x.2 : ℤ) * δ) := by
    rw [← hx']; push_cast; ring
  rw [e]
  exact (hP x.1).mul (hQ x.2)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_one]`. Use `split_ifs with h`. Establish `hk : k = 0` using `by omega`. Substitute `hk` using the available equality.

Simplify using `using isWeightedHomogeneous_one R (lhwinHt r n)`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem lhwinShift_one {R : Type*} [CommRing R] {r n : ℕ} (δ : ℤ) :
    LhwinShift (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (lhwinHt r n)
  · exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => rw [pow_zero, zero_smul]`. Conclude with `lhwinShift_one δ`. Consider the case `succ e ih => rw [pow_succ, succ_nsmul]`. Conclude with `lhwinShift_mul ih hP`.
-/
theorem lhwinShift_pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LhwinShift P μ δ) (e : ℕ) : LhwinShift (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact lhwinShift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact lhwinShift_mul ih hP

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (lhwinShift_one (R := R) (r := r) (n := n) δ)`. Consider the case `insert i s his IH`. Rewrite using `[Finset.prod_insert his, Finset.sum_insert his]`. Conclude with `lhwinShift_mul (h i (Finset.mem_insert_self _ _)) (IH fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem lhwinShift_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LhwinShift (P i) (μ i) δ) : LhwinShift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (lhwinShift_one (R := R) (r := r) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact lhwinShift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.algebraMap_apply, Polynomial.coeff_C]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[MvPolynomial.algebraMap_eq]`.

Simplify using `using isWeightedHomogeneous_C (lhwinHt r n) c`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem lhwinShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) (δ : ℤ) :
    LhwinShift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (lhwinHt r n) c
  · exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Introduce `k`. Establish `hX : IsWeightedHomogeneous (lhwinHt r n) (X v : MvPolynomial (Fin r × Fin n) R) (lhwinHt r n v)` using `isWeightedHomogeneous_X R _ v`. Establish `hXa : IsWeightedHomogeneous (lhwinHt r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R) (lhwinHt r n (a, v.2))` using `isWeightedHomogeneous_X R _ (a, v.2)`. Rewrite using `[Polynomial.coeff_add]`. Use `IsWeightedHomogeneous.add ?_ ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.coeff_C] split_ifs with h`. Substitute `h` using the available equality. Simplify using `using hX`. Conclude with `isWeightedHomogeneous_zero R _ _`. Use `split_ifs with hb`.

Rewrite using `[mul_comm, Polynomial.coeff_C_mul_X] split_ifs with h`. Substitute `h` using the available equality. Establish `e : lhwinHt r n v + ((1 : ℕ) : ℤ) * ((a.val : ℤ) - b.val) = lhwinHt r n (a, v.2)`. Simplify using `[lhwinHt, hb]`. Rewrite using `[e]`.

Conclude with `hXa`. Conclude with `isWeightedHomogeneous_zero R _ _`. Rewrite using `[Polynomial.coeff_zero]`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem lhwinShift_gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    LhwinShift (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (lhwinHt r n v) ((a.val : ℤ) - b.val) := by
  intro k
  have hX : IsWeightedHomogeneous (lhwinHt r n) (X v : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (lhwinHt r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : lhwinHt r n v + ((1 : ℕ) : ℤ) * ((a.val : ℤ) - b.val) = lhwinHt r n (a, v.2) := by
          simp [lhwinHt, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Unfold `rowGen`. Rewrite using `[aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]`. Use `lhwinShift_mul (lhwinShift_algebraMap c _) ?_` and prove the remaining obligations. Unfold `Finsupp.prod Finsupp.sum`. Conclude with `lhwinShift_prod _ _ _ _ fun v _ => lhwinShift_pow (lhwinShift_gen a b v) _`.
-/
theorem lhwinShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LhwinShift (rowGen R a b (monomial d c)) (Finsupp.weight (lhwinHt r n) d)
      ((a.val : ℤ) - b.val) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine lhwinShift_mul (lhwinShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact lhwinShift_prod _ _ _ _ fun v _ => lhwinShift_pow (lhwinShift_gen a b v) _

/- English proof (translation)
Unfold `rowDiv`. Use `conv => enter [2, 1, 2]`. Rewrite using `[f.as_sum]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations.

Use `lhwinShift_rowGen_monomial R a b d (coeff d f) k` as an intermediate fact. Rewrite `this` using `[hf (mem_support_iff.mp hd)]`. Then use the resulting hypothesis.
-/
theorem lhwin_rowDiv_shift (R : Type*) [CommRing R] {r n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (lhwinHt r n) f H) :
    IsWeightedHomogeneous (lhwinHt r n) (rowDiv R a b k f) (H + k * ((a.val : ℤ) - b.val)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := lhwinShift_rowGen_monomial R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Simplify using `only [map_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]`. Consider the case `single v c`.

Simplify using `[Finsupp.weight_apply, lhwinHt, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]`.
-/
theorem lhwin_weight_ht {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lhwinHt r n) d =
      ∑ a : Fin r, (a.val : ℤ) * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, lhwinHt, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]

/- English proof (translation)
Rewrite using `[lhwin_weight_ht]`. Conclude with `Finset.sum_nonneg fun a _ => by positivity`.
-/
theorem lhwin_weight_nonneg {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    0 ≤ Finsupp.weight (lhwinHt r n) d := by
  rw [lhwin_weight_ht]
  exact Finset.sum_nonneg fun a _ => by positivity

/- English proof (translation)
Take `⟨d, hd⟩` from `ne_zero_iff.mp hg`. Rewrite using `[← hz hd]`. Conclude with `lhwin_weight_nonneg d`.
-/
theorem lhwin_nonneg {R : Type*} [CommRing R] {r n : ℕ} {g : MvPolynomial (Fin r × Fin n) R} {z : ℤ}
    (hg : g ≠ 0) (hz : IsWeightedHomogeneous (lhwinHt r n) g z) : 0 ≤ z := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hg
  rw [← hz hd]
  exact lhwin_weight_nonneg d

/- English proof (translation)
Establish `hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ IsWeightedHomogeneous (lhwinHt r n) v (N : ℤ)`. Take `⟨f, hfM, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨d, hd⟩` from `ne_zero_iff.mp hf0`. Use `⟨∑ a : Fin r, a.val * Finsupp.weight (rowW r n) d a, weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) d) f, h2 r n M hM f hfM _, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Use `congrArg (coeff d) h` as an intermediate fact. Rewrite `this` using `[coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero]`. Then use the resulting hypothesis. Introduce `e he`. Rewrite `he` using `[coeff_weightedHomogeneousComponent]`.

Use `split_ifs at he with hμ`. Rewrite using `[lhwin_weight_ht, hμ]`. Use `push_cast`. Both sides reduce to the same expression. Conclude with `absurd rfl he`.

Take `⟨v, hvM, hv0, hvH⟩` from `Nat.find_spec hex`. Use `⟨v, hvM, hv0, fun a b hab k hk => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`. Establish `hH` using `lhwin_rowDiv_shift ℚ _ a b k v hvH`. Establish `hnn` using `lhwin_nonneg hne' hH`.

Establish `hab' : (a.val : ℤ) < b.val` using `by exact_mod_cast (Fin.lt_def.mp hab)`. Establish `hk' : (1 : ℤ) ≤ k` using `by exact_mod_cast hk`. Establish `hlt : ((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmin` using `Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val)).toNat) (by omega)`.

Apply `hmin` to reduce the goal to its premises. Use `⟨_, hM a b k v hvM, hne', ?_⟩` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg hnn]`. Conclude with `hH`.
-/
theorem lhwin_exists_killed (h2 : RowDivClosedGraded) {r n : ℕ}
    (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℚ a b k v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ IsWeightedHomogeneous (lhwinHt r n) v (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf0
    refine ⟨∑ a : Fin r, a.val * Finsupp.weight (rowW r n) d a,
      weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) d) f,
      h2 r n M hM f hfM _, ?_, ?_⟩
    · intro h
      apply hd
      have := congrArg (coeff d) h
      rwa [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    · intro e he
      rw [coeff_weightedHomogeneousComponent] at he
      split_ifs at he with hμ
      · rw [lhwin_weight_ht, hμ]; push_cast; rfl
      · exact absurd rfl he
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab k hk => ?_⟩
  by_contra hne'
  have hH := lhwin_rowDiv_shift ℚ _ a b k v hvH
  have hnn := lhwin_nonneg hne' hH
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hlt : ((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b k v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

end Formalism.GradedWeylDivisibility
