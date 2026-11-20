import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Matrix Finset

open scoped ComplexOrder

noncomputable section

namespace Elem

variable {R : Type*} [CommRing R] {κ : Type*}

def subsetCols {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) : κ :=
  ((S.1.equivFinOfCardEq S.2).symm i : κ)

/- English proof (translation)
Introduce `i j h`. Conclude with `(S.1.equivFinOfCardEq S.2).symm.injective (Subtype.ext h)`.
-/
theorem subsetCols_injective {p : ℕ} (S : {s : Finset κ // s.card = p}) :
    Function.Injective (subsetCols S) := by
  intro i j h
  exact (S.1.equivFinOfCardEq S.2).symm.injective (Subtype.ext h)

/- English proof (translation)
The claim follows from `((S.1.equivFinOfCardEq S.2).symm i).2`.
-/
theorem subsetCols_mem {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) :
    subsetCols S i ∈ S.1 :=
  ((S.1.equivFinOfCardEq S.2).symm i).2

/- English proof (translation)
Assemble the required witnesses or components as `⟨S.1.equivFinOfCardEq S.2 ⟨k, hk⟩, by simp [subsetCols]⟩`.
-/
theorem exists_subsetCols_eq {p : ℕ} (S : {s : Finset κ // s.card = p}) {k : κ}
    (hk : k ∈ S.1) : ∃ i, subsetCols S i = k :=
  ⟨S.1.equivFinOfCardEq S.2 ⟨k, hk⟩, by simp [subsetCols]⟩

/- English proof (translation)
Simplify using `only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Simplify using `only [submatrix_apply, id, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mul_expand [Fintype κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ φ : Fin p → κ, (A.submatrix id φ).det * ∏ i, B (φ i) i := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Simplify using `only [Function.Injective, not_forall] at h`. Take `⟨i, j, hij, hne⟩` from `h`. Conclude with `det_zero_of_column_eq hne (fun k => by simp [hij])`.
-/
theorem det_submatrix_eq_zero_of_not_injective {p : ℕ} (A : Matrix (Fin p) κ R)
    (φ : Fin p → κ) (h : ¬ Function.Injective φ) : (A.submatrix id φ).det = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

/- English proof (translation)
Rewrite using `[det_mul_expand]`. Rewrite using `[← Finset.sum_filter_of_ne (p := Function.Injective) (fun φ _ h => by`. Assume the negation of the conclusion as `hφ`. Conclude with `h (by rw [det_submatrix_eq_zero_of_not_injective A φ hφ, zero_mul]))]`. Establish `hpairs : ∑ S : {s : Finset κ // s.card = p}, (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det = ∑ x : {s : Finset κ // s.card = p} × Equiv.Perm (Fin p), (A.submatrix id (subsetCols x.1 ∘ x.2)).det * ∏ i, B (subsetCols x.1 (x.2 i)) i`.

Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Rewrite using `[det_apply' (B.submatrix _ _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Establish `: A.submatrix id (subsetCols S ∘ π) = (A.submatrix id (subsetCols S)).submatrix id π` using `rfl`.

Rewrite using `[this, det_permute']`. Simplify using `only [submatrix_apply, id]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hpairs]`. Use `symm`.

Use `Finset.sum_bij (fun x _ => subsetCols x.1 ∘ x.2) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `(subsetCols_injective x.1).comp x.2.injective`. Introduce and unpack `⟨S, π⟩ _ ⟨T, π'⟩ _ hxy`.

Simplify using `only at hxy`. Establish `hST : S = T`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `k`. Prove the components needed by the constructor for the conclusion.

Introduce `hk`. Take `⟨i, rfl⟩` from `exists_subsetCols_eq S hk`. Use `congrFun hxy (π.symm i)` as an intermediate fact. Simplify using `only [Function.comp_apply, Equiv.apply_symm_apply] at this`. Rewrite using `[this]`.

Conclude with `subsetCols_mem T _`. Introduce `hk`. Take `⟨i, rfl⟩` from `exists_subsetCols_eq T hk`. Use `congrFun hxy (π'.symm i)` as an intermediate fact. Simplify using `only [Function.comp_apply, Equiv.apply_symm_apply] at this`.

Rewrite using `[← this]`. Conclude with `subsetCols_mem S _`. Substitute `hST` using the available equality. Establish `: π = π'`. Use extensionality with `i`.

Conclude with `congrArg Fin.val (subsetCols_injective S (congrFun hxy i))`. Rewrite using `[this]`. Introduce `φ hφ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ`. Set `S : {s : Finset κ // s.card = p}` to `⟨Finset.univ.image φ, by rw [Finset.card_image_of_injective _ hφ]; simp⟩`.

Set `g : Fin p → Fin p` to `fun i => S.1.equivFinOfCardEq S.2 ⟨φ i, Finset.mem_image_of_mem φ (Finset.mem_univ i)⟩`. Establish `hg : Function.Injective g`. Introduce `i j h`. Use `(S.1.equivFinOfCardEq S.2).injective h` as an intermediate fact. Conclude with `hφ (congrArg Subtype.val this)`.

Use `⟨(S, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[subsetCols, g, S]`. Introduce `x _`. Both sides reduce to the same expression.
-/
theorem cauchyBinet [Fintype κ] [DecidableEq κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det := by
  rw [det_mul_expand]
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun φ _ h => by
        by_contra hφ
        exact h (by rw [det_submatrix_eq_zero_of_not_injective A φ hφ, zero_mul]))]
  have hpairs : ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det =
      ∑ x : {s : Finset κ // s.card = p} × Equiv.Perm (Fin p),
        (A.submatrix id (subsetCols x.1 ∘ x.2)).det * ∏ i, B (subsetCols x.1 (x.2 i)) i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [det_apply' (B.submatrix _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have : A.submatrix id (subsetCols S ∘ π) =
        (A.submatrix id (subsetCols S)).submatrix id π := rfl
    rw [this, det_permute']
    simp only [submatrix_apply, id]
    ring
  rw [hpairs]
  symm
  refine Finset.sum_bij (fun x _ => subsetCols x.1 ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (subsetCols_injective x.1).comp x.2.injective
  · rintro ⟨S, π⟩ _ ⟨T, π'⟩ _ hxy
    simp only at hxy
    have hST : S = T := by
      apply Subtype.ext
      ext k
      constructor
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq S hk
        have := congrFun hxy (π.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [this]
        exact subsetCols_mem T _
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq T hk
        have := congrFun hxy (π'.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [← this]
        exact subsetCols_mem S _
    subst hST
    have : π = π' := by
      ext i
      exact congrArg Fin.val (subsetCols_injective S (congrFun hxy i))
    rw [this]
  · intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    let S : {s : Finset κ // s.card = p} :=
      ⟨Finset.univ.image φ, by rw [Finset.card_image_of_injective _ hφ]; simp⟩
    let g : Fin p → Fin p := fun i =>
      S.1.equivFinOfCardEq S.2 ⟨φ i, Finset.mem_image_of_mem φ (Finset.mem_univ i)⟩
    have hg : Function.Injective g := by
      intro i j h
      have := (S.1.equivFinOfCardEq S.2).injective h
      exact hφ (congrArg Subtype.val this)
    refine ⟨(S, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)),
      Finset.mem_univ _, ?_⟩
    funext i
    simp [subsetCols, g, S]
  · intro x _
    rfl

end Elem

open Elem in

/- English proof (translation)
Introduce `p q Z`. Use `set A := Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) Z with hAdef`. Establish `hA : 1 + Z * Z.conjTranspose = A * A.conjTranspose`. Rewrite using `[hAdef, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]`. Simplify using the standard rewrite rules.

Rewrite using `[hA, cauchyBinet, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Establish `hB : A.conjTranspose.submatrix (subsetCols S) id = (A.submatrix id (subsetCols S)).conjTranspose`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[hB, det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem PlueckerCauchyBinet.intersectionNumber_baseChange : PlueckerCauchyBinet.Statement := by
  intro p q Z
  set A := Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) Z with hAdef
  have hA : 1 + Z * Z.conjTranspose = A * A.conjTranspose := by
    rw [hAdef, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp
  rw [hA, cauchyBinet, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hB : A.conjTranspose.submatrix (subsetCols S) id =
      (A.submatrix id (subsetCols S)).conjTranspose := by
    ext i j; simp
  rw [hB, det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/- English proof (translation)
Introduce `p q Z hZ`. Use `set H := 1 + Z * Z.conjTranspose with hHdef`. Establish `hpsd : H.PosSemidef` using `Matrix.PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)`. Establish `hH : H.IsHermitian` using `hpsd.isHermitian`. Use `set ev := hH.eigenvalues`.

Establish `hev : ∀ i, 0 ≤ ev i` using `hpsd.eigenvalues_nonneg`. Establish `hdet : H.det = ((∏ i, ev i : ℝ) : ℂ)`. Rewrite using `[hH.det_eq_prod_eigenvalues]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `htrH : H.trace = ((p * (1 + q) : ℝ) : ℂ)`. Establish `hZZ : (Z * Z.conjTranspose).trace = ((p * q : ℕ) : ℂ)`. Simplify using `only [trace, Matrix.diag, mul_apply, conjTranspose_apply]`. Establish `: ∀ i j, Z i j * (starRingEnd ℂ) (Z i j) = 1`. Introduce `i j`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hZ i j]`. Simplify using the standard rewrite rules. Simplify using `[this]`. Rewrite using `[hHdef, trace_add, trace_one, hZZ]`. Use `push_cast`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ i, ev i = p * (1 + q)`. Establish `h1` using `hH.trace_eq_sum_eigenvalues`. Rewrite `h1` using `[htrH]`.

Establish `: ((∑ i, ev i : ℝ) : ℂ) = ((p * (1 + q) : ℝ) : ℂ)`. Rewrite using `[h1]`. Use `push_cast`. Both sides reduce to the same expression. Conclude with `this` after adjusting the coercions.

Rewrite using `[hdet, Complex.ofReal_re]`. Use `push_cast`. Break down `Nat.eq_zero_or_pos p with hp | hp` into its components or cases. Substitute `hp` using the available equality. Simplify using the standard rewrite rules.

Establish `hp' : (0 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hamgm` using `Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ : Fin p => 1 / (p : ℝ)) ev (fun i _ => by positivity) (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp) (fun i _ => hev i)`. Establish `hrhs : ∑ i, 1 / (p : ℝ) * ev i = 1 + q`. Rewrite using `[← Finset.mul_sum, hsum]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hamgm` using `[hrhs]`. Establish `hprod : ∏ i, ev i = (∏ i, ev i ^ (1 / (p : ℝ))) ^ p`. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (hev i), one_div_mul_cancel hp'.ne', Real.rpow_one]`.

Rewrite using `[hprod]`. Conclude with `pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hev i) _) hamgm p`.
-/
theorem PlueckerHadamard.intersectionNumber_baseChange : PlueckerHadamard.Statement := by
  intro p q Z hZ
  set H := 1 + Z * Z.conjTranspose with hHdef
  have hpsd : H.PosSemidef := Matrix.PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)
  have hH : H.IsHermitian := hpsd.isHermitian
  set ev := hH.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := hpsd.eigenvalues_nonneg
  have hdet : H.det = ((∏ i, ev i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]; push_cast; rfl
  have htrH : H.trace = ((p * (1 + q) : ℝ) : ℂ) := by
    have hZZ : (Z * Z.conjTranspose).trace = ((p * q : ℕ) : ℂ) := by
      simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
      have : ∀ i j, Z i j * (starRingEnd ℂ) (Z i j) = 1 := by
        intro i j
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hZ i j]
        simp
      simp [this]
    rw [hHdef, trace_add, trace_one, hZZ]
    push_cast
    simp
    ring
  have hsum : ∑ i, ev i = p * (1 + q) := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [htrH] at h1
    have : ((∑ i, ev i : ℝ) : ℂ) = ((p * (1 + q) : ℝ) : ℂ) := by
      rw [h1]; push_cast; rfl
    exact_mod_cast this
  rw [hdet, Complex.ofReal_re]
  push_cast
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hamgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (fun _ : Fin p => 1 / (p : ℝ)) ev (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => hev i)
    have hrhs : ∑ i, 1 / (p : ℝ) * ev i = 1 + q := by
      rw [← Finset.mul_sum, hsum]; field_simp
    rw [hrhs] at hamgm
    have hprod : ∏ i, ev i = (∏ i, ev i ^ (1 / (p : ℝ))) ^ p := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hev i), one_div_mul_cancel hp'.ne', Real.rpow_one]
    rw [hprod]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hev i) _) hamgm p

end

end RestTerms

end GroundTheory.Heights₂.Heights
