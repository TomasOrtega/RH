import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Simplify using `[dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]`.
-/
theorem rowdiv_mem_dualWeyl_iff (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def CoeffHom {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ : Fin n → ℕ) : Prop :=
  ∀ k, IsWeightedHomogeneous (colW r n) (P.coeff k) μ

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Conclude with `IsWeightedHomogeneous.sum _ _ _ fun x _ => (hP x.1).mul (hQ x.2)`.
-/
theorem CoeffHom.mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' : Fin n → ℕ}
    (hP : CoeffHom P μ) (hQ : CoeffHom Q μ') : CoeffHom (P * Q) (μ + μ') := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun x _ => (hP x.1).mul (hQ x.2)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_one]`. Use `split_ifs`. Conclude with `isWeightedHomogeneous_one R _`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem CoeffHom.one {R : Type*} [CommRing R] {r n : ℕ} :
    CoeffHom (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one R _
  · exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => rw [pow_zero, zero_smul]`. Conclude with `CoeffHom.one`. Consider the case `succ e ih => rw [pow_succ, succ_nsmul]`. Conclude with `ih.mul hP`.
-/
theorem CoeffHom.pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ : Fin n → ℕ}
    (hP : CoeffHom P μ) (e : ℕ) : CoeffHom (P ^ e) (e • μ) := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact CoeffHom.one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (CoeffHom.one (R := R) (r := r) (n := n))`. Consider the case `insert i s his IH`. Rewrite using `[Finset.prod_insert his, Finset.sum_insert his]`. Conclude with `(h i (Finset.mem_insert_self _ _)).mul (IH fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem CoeffHom.prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin n → ℕ)
    (h : ∀ i ∈ s, CoeffHom (P i) (μ i)) : CoeffHom (∏ i ∈ s, P i) (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CoeffHom.one (R := R) (r := r) (n := n))
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.algebraMap_apply, Polynomial.coeff_C]`. Use `split_ifs`. Rewrite using `[MvPolynomial.algebraMap_eq]`. Conclude with `isWeightedHomogeneous_C _ _`.

Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem CoeffHom.algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    CoeffHom (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs
  · rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  · exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Introduce `k`. Establish `hX : IsWeightedHomogeneous (colW r n) (X v : MvPolynomial (Fin r × Fin n) R) (colW r n v)` using `isWeightedHomogeneous_X R _ v`. Establish `hXa : IsWeightedHomogeneous (colW r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R) (colW r n v)` using `isWeightedHomogeneous_X R _ (a, v.2)`. Rewrite using `[Polynomial.coeff_add]`. Use `IsWeightedHomogeneous.add ?_ ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.coeff_C] split_ifs`. Conclude with `hX`. Conclude with `isWeightedHomogeneous_zero R _ _`. Use `split_ifs`. Rewrite using `[mul_comm, Polynomial.coeff_C_mul_X] split_ifs`.

Conclude with `hXa`. Conclude with `isWeightedHomogeneous_zero R _ _`. Rewrite using `[Polynomial.coeff_zero]`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem CoeffHom.gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    CoeffHom (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (colW r n v) := by
  intro k
  have hX : IsWeightedHomogeneous (colW r n) (X v : MvPolynomial (Fin r × Fin n) R) (colW r n v) :=
    isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (colW r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (colW r n v) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Unfold `rowGen`. Rewrite using `[aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]`. Use `(CoeffHom.algebraMap c).mul ?_` and prove the remaining obligations. Unfold `Finsupp.prod Finsupp.sum`. Conclude with `CoeffHom.prod _ _ _ fun v _ => (CoeffHom.gen a b v).pow _`.
-/
theorem CoeffHom.rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    CoeffHom (rowGen R a b (monomial d c)) (Finsupp.weight (colW r n) d) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine (CoeffHom.algebraMap c).mul ?_
  unfold Finsupp.prod Finsupp.sum
  exact CoeffHom.prod _ _ _ fun v _ => (CoeffHom.gen a b v).pow _

/- English proof (translation)
Unfold `rowDiv`. Use `conv => enter [2, 1, 2]`. Rewrite using `[f.as_sum]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations.

Use `CoeffHom.rowGen_monomial R a b d (coeff d f) k` as an intermediate fact. Rewrite `this` using `[hf (mem_support_iff.mp hd)]`. Then use the resulting hypothesis.
-/
theorem rowDiv_homog (R : Type*) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) :
    IsWeightedHomogeneous (colW r n) (rowDiv R a b k f) ν := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := CoeffHom.rowGen_monomial R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

def rowGenO (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R]
      Polynomial (MvPolynomial (Option (Fin r × Fin n)) R) :=
  aeval fun o => Option.elim o (Polynomial.C (X none)) fun v =>
    Polynomial.C (X (some v)) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (some (a, v.2))) else 0)

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, colAddGen, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]`. Apply the tactic sequence `by_cases h2 : v.2 = j <;> by_cases h1 : v.1 = b <;>`. Apply the tactic sequence `simp [h1, h2, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, aeval_X] <;> ring`.
-/
theorem rowGenO_comp_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (l j : Fin n) :
    (rowGenO R a b).comp (colAddGen R (r := r) l j) =
      (Polynomial.mapAlgHom (colAddGen R (r := r) l j)).comp (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h2 : v.2 = j <;> by_cases h1 : v.1 = b <;>
    simp [h1, h2, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      aeval_X] <;> ring

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rename_X, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]`. Apply the tactic sequence `by_cases h1 : v.1 = b <;>`. Simplify using `[h1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]`.
-/
theorem rowGenO_comp_rename (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    (rowGenO R a b).comp (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      (Polynomial.mapAlgHom (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n)))).comp
        (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h1 : v.1 = b <;>
    simp [h1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]

/- English proof (translation)
Establish `hA` using `congrArg (fun φ => φ f) (rowGenO_comp_colAddGen R a b l j)`. Establish `hB` using `congrArg (fun φ => φ f) (rowGenO_comp_rename R (n := n) a b)`. Simplify using `only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom] at hA hB`. Rewrite `hA` using `[hf, hB]`. Establish `hk` using `congrArg (fun P => Polynomial.coeff P k) hA`.

Simplify using `only [Polynomial.coeff_map] at hk`. Unfold `rowDiv`. Conclude with `hk.symm`.
-/
theorem rowDiv_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : colAddGen R l j f = rename some f) :
    colAddGen R l j (rowDiv R a b k f) = rename some (rowDiv R a b k f) := by
  have hA := congrArg (fun φ => φ f) (rowGenO_comp_colAddGen R a b l j)
  have hB := congrArg (fun φ => φ f) (rowGenO_comp_rename R (n := n) a b)
  simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom] at hA hB
  rw [hf, hB] at hA
  have hk := congrArg (fun P => Polynomial.coeff P k) hA
  simp only [Polynomial.coeff_map] at hk
  unfold rowDiv
  exact hk.symm

/- English proof (translation)
Introduce `R _ r n ν a b k f hf`. Rewrite `hf`, the goal using `[rowdiv_mem_dualWeyl_iff]`. Conclude with `⟨rowDiv_homog R ν a b k f hf.1, fun l j hlj => rowDiv_colAddGen R a b k l j f (hf.2 l j hlj)⟩`.
-/
theorem dualWeylModuleRowDividedPowerStable : RowDivStable := by
  intro R _ r n ν a b k f hf
  rw [rowdiv_mem_dualWeyl_iff] at hf ⊢
  exact ⟨rowDiv_homog R ν a b k f hf.1, fun l j hlj => rowDiv_colAddGen R a b k l j f (hf.2 l j hlj)⟩

end Formalism.GradedWeylDivisibility
