import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def iotaC (R : Type) [CommRing R] (n k : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin (n + k)) R :=
  Matrix.reindexAlgEquiv R R finSumFinEquiv (Matrix.fromBlocks Y 0 0 1)

/- English proof (translation)
Rewrite using `[iotaC, iotaC, iotaC, ← map_mul, Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem iotaC_mul (R : Type) [CommRing R] (n k : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    iotaC R n k (A * B) = iotaC R n k A * iotaC R n k B := by
  rw [iotaC, iotaC, iotaC, ← map_mul, Matrix.fromBlocks_multiply]
  simp

/- English proof (translation)
Rewrite using `[iotaC, Matrix.fromBlocks_one, map_one]`.
-/
theorem iotaC_one (R : Type) [CommRing R] (n k : ℕ) : iotaC R n k 1 = 1 := by
  rw [iotaC, Matrix.fromBlocks_one, map_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>`. Apply the tactic sequence `simp [Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all`.
-/
theorem iotaC_map (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) R) : (iotaC R n k Y).map φ = iotaC S n k (Y.map φ) := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>`. Simplify using `[Matrix.one_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]`.
-/
theorem iotaC_conj (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    iotaC ℂ n k Y.conjTranspose = (iotaC ℂ n k Y).conjTranspose := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]

/- English proof (translation)
Rewrite using `[iotaC, Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`.
-/
theorem iotaC_det (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : (iotaC ℂ n k Y).det = Y.det := by
  rw [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

/- English proof (translation)
Establish `hi : ∀ i : Fin (n + 0), finSumFinEquiv.symm i = Sum.inl i` using `fun i => by`. Rewrite using `[Equiv.symm_apply_eq]`. Both sides reduce to the same expression. Use extensionality with `i j`. Simplify using `[iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hi]`.
-/
theorem iotaC_zero (R : Type) [CommRing R] (n : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    iotaC R n 0 Y = Y := by
  have hi : ∀ i : Fin (n + 0), finSumFinEquiv.symm i = Sum.inl i := fun i => by
    rw [Equiv.symm_apply_eq]; rfl
  ext i j
  simp [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hi]

open Formalism.REAL (fockF)

def fct {σ : Type} (m : σ →₀ ℕ) : ℂ := ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

/- English proof (translation)
Use `trans ∑ m ∈ p.support ∩ s, p.coeff m * star (q.coeff m) * fct m`. Unfold `fockF fct`. Use `symm`. Apply `Finset.sum_subset Finset.inter_subset_left` to reduce the goal to its premises. Introduce `m hm hms`.

Distinguish the cases in `hq : q.coeff m = 0`. Simplify using `[hq]`. Conclude with `absurd (Finset.mem_inter.mpr ⟨hm, hs m (MvPolynomial.mem_support_iff.mp hm) hq⟩) hms`. Apply `Finset.sum_subset Finset.inter_subset_right` to reduce the goal to its premises. Introduce `m hm hms`.

Distinguish the cases in `hp : p.coeff m = 0`. Simplify using `[hp]`. Conclude with `absurd (Finset.mem_inter.mpr ⟨MvPolynomial.mem_support_iff.mpr hp, hm⟩) hms`.
-/
theorem fockF_eq_sum {σ : Type} (p q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : ∀ m, p.coeff m ≠ 0 → q.coeff m ≠ 0 → m ∈ s) :
    fockF p q = ∑ m ∈ s, p.coeff m * star (q.coeff m) * fct m := by
  classical
  trans ∑ m ∈ p.support ∩ s, p.coeff m * star (q.coeff m) * fct m
  · unfold fockF fct
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro m hm hms
    by_cases hq : q.coeff m = 0
    · simp [hq]
    · exact absurd (Finset.mem_inter.mpr ⟨hm, hs m (MvPolynomial.mem_support_iff.mp hm) hq⟩) hms
  · apply Finset.sum_subset Finset.inter_subset_right
    intro m hm hms
    by_cases hp : p.coeff m = 0
    · simp [hp]
    · exact absurd (Finset.mem_inter.mpr ⟨MvPolynomial.mem_support_iff.mpr hp, hm⟩) hms

/- English proof (translation)
Establish `hs : ∀ r : MvPolynomial σ ℂ, r.support ⊆ p.support ∪ p'.support → fockF r q = ∑ m ∈ p.support ∪ p'.support, r.coeff m * star (q.coeff m) * fct m` using `fun r hr => fockF_eq_sum r q _ (fun m h1 _ => hr (MvPolynomial.mem_support_iff.mpr h1))`. Rewrite using `[hs (p + p') MvPolynomial.support_add, hs p Finset.subset_union_left, hs p' Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockF_add_left {σ : Type} (p p' q : MvPolynomial σ ℂ) :
    fockF (p + p') q = fockF p q + fockF p' q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ, r.support ⊆ p.support ∪ p'.support →
      fockF r q = ∑ m ∈ p.support ∪ p'.support, r.coeff m * star (q.coeff m) * fct m :=
    fun r hr => fockF_eq_sum r q _ (fun m h1 _ => hr (MvPolynomial.mem_support_iff.mpr h1))
  rw [hs (p + p') MvPolynomial.support_add, hs p Finset.subset_union_left,
    hs p' Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Rewrite using `[fockF_eq_sum (c • p) q p.support (fun m h _ => by`. Rewrite `h` using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Conclude with `MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)),`. Use `fockF_eq_sum p q p.support (fun m h _ => MvPolynomial.mem_support_iff.mpr h), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockF_smul_left {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF (c • p) q = c * fockF p q := by
  classical
  rw [fockF_eq_sum (c • p) q p.support (fun m h _ => by
        rw [MvPolynomial.coeff_smul, smul_eq_mul] at h
        exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)),
    fockF_eq_sum p q p.support (fun m h _ => MvPolynomial.mem_support_iff.mpr h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `[fockF]`.
-/
theorem fockF_zero_left {σ : Type} (q : MvPolynomial σ ℂ) : fockF 0 q = 0 := by
  simp [fockF]

/- English proof (translation)
Establish `hs : ∀ r : MvPolynomial σ ℂ, fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m` using `fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)`. Rewrite using `[hs, hs, hs, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add, star_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockF_add_right {σ : Type} (p q q' : MvPolynomial σ ℂ) :
    fockF p (q + q') = fockF p q + fockF p q' := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

/- English proof (translation)
Establish `hs : ∀ r : MvPolynomial σ ℂ, fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m` using `fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)`. Rewrite using `[hs, hs, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockF_smul_right {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF p (c • q) = star c * fockF p q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[fockF]`. Introduce `a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_left, ih]`.
-/
theorem fockF_sum_left {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, x i) q = ∑ i ∈ s, fockF (x i) q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_left, ih]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[fockF]`. Introduce `a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, ih]`.
-/
theorem fockF_sum_right {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    fockF p (∑ i ∈ s, x i) = ∑ i ∈ s, fockF p (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, ih]

/- English proof (translation)
Rewrite using `[fockF_sum_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[fockF_smul_left, fockF_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[fockF_smul_right]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockF_lc {σ ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, a i • x i) (∑ j ∈ s, a j • x j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (x i) (x j) := by
  rw [fockF_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fockF_smul_left, fockF_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fockF_smul_right]
  ring

/- English proof (translation)
Assume the negation of the conclusion as `hp`. Take `⟨m, hm⟩` from `Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hp)`. Establish `hre : (fockF p p).re = ∑ m ∈ p.support, Complex.normSq (p.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ)`. Unfold `fockF`. Rewrite using `[Complex.re_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `show (p.coeff m * (starRingEnd ℂ) (p.coeff m) * _).re = _`. Rewrite using `[Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]`. Establish `hpos : 0 < ∑ m ∈ p.support, Complex.normSq (p.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ)` using `Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)) (Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _))) ⟨m, hm⟩`. Rewrite `hpos` using `[← hre, h, Complex.zero_re]`.

Conclude with `lt_irrefl _ hpos`.
-/
private theorem eq_zero_of_fockF_self_eq_zero {σ : Type} (p : MvPolynomial σ ℂ) (h : fockF p p = 0) : p = 0 := by
  classical
  by_contra hp
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hp)
  have hre : (fockF p p).re =
      ∑ m ∈ p.support, Complex.normSq (p.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
    unfold fockF
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    show (p.coeff m * (starRingEnd ℂ) (p.coeff m) * _).re = _
    rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpos : 0 < ∑ m ∈ p.support, Complex.normSq (p.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) :=
    Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm))
      (Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _))) ⟨m, hm⟩
  rw [← hre, h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

/- English proof (translation)
Establish `hyy : fockF (∑ i ∈ s, a i • xf i) (∑ i ∈ s, a i • xf i) = 0`. Establish `he` using `fockF_lc s a xe`. Rewrite `he` using `[h0, fockF_zero_left]`. Rewrite using `[fockF_lc]`. Repeatedly rewrite using `[hK]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Use `_ = 0 := by rw [← he, mul_zero]`. Conclude with `eq_zero_of_fockF_self_eq_zero _ hyy`.
-/
theorem lc_zero_of_gram {σ τ ι : Type} (s : Finset ι) (a : ι → ℂ) (xe : ι → MvPolynomial σ ℂ)
    (xf : ι → MvPolynomial τ ℂ) (K : ℂ)
    (hK : ∀ i j, fockF (xf i) (xf j) = K * fockF (xe i) (xe j))
    (h0 : ∑ i ∈ s, a i • xe i = 0) : ∑ i ∈ s, a i • xf i = 0 := by
  have hyy : fockF (∑ i ∈ s, a i • xf i) (∑ i ∈ s, a i • xf i) = 0 := by
    have he := fockF_lc s a xe
    rw [h0, fockF_zero_left] at he
    rw [fockF_lc]
    simp_rw [hK]
    calc _ = K * ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (xe i) (xe j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [← he, mul_zero]
  exact eq_zero_of_fockF_self_eq_zero _ hyy

/- English proof (translation)
Rewrite using `[fockRowAdj r n M.conjTranspose p q, Matrix.conjTranspose_conjTranspose]`.
-/
theorem fockF_rowAct_right (r n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (p q : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF p (rowAct ℂ M q) = fockF (rowAct ℂ M.conjTranspose p) q := by
  rw [fockRowAdj r n M.conjTranspose p q, Matrix.conjTranspose_conjTranspose]

end PI.WGB
