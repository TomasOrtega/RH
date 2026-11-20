import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.FormPerpVectorMemOfIntegral

open scoped BigOperators
open NumberField

namespace GlobalTheory.GridSize

open GlobalTheory.Harm GlobalTheory.MvPoly

section Minor

variable {T : Type*} {p q n : ℕ}

/- English proof (translation)
Rewrite using `[rowForm_apply]`. Use `(l1Norm_linearForm_le (fun k => (t, r, k)) v).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.card_fin]`. Conclude with `mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR, hv⟩) (Real.sqrt_nonneg _)`.
-/
theorem l1Norm_rowBlockLinearForm_le (t : T) (r : Fin p ⊕ Fin q) (v : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∑ k, ‖v k‖ ^ 2 ≤ R ^ 2) : l1Norm (rowForm t r v) ≤ √(n : ℝ) * R := by
  rw [rowForm_apply]
  refine (l1Norm_linearForm_le (fun k => (t, r, k)) v).trans ?_
  rw [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR, hv⟩) (Real.sqrt_nonneg _)

/- English proof (translation)
Use `(l1Norm_det_le_pow M h).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.card_fin]`. Establish `: (i : ℝ) ≤ N` using `by exact_mod_cast hi`. Use `gcongr`.
-/
theorem l1Norm_det_le_of_entry_bound {σ : Type*} {i N : ℕ} (hi : i ≤ N)
    (M : Matrix (Fin i) (Fin i) (MvPolynomial σ ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a b, l1Norm (M a b) ≤ B) : l1Norm M.det ≤ (N * B) ^ i := by
  refine (l1Norm_det_le_pow M h).trans ?_
  rw [Fintype.card_fin]
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  gcongr

/- English proof (translation)
Establish `hB : 0 ≤ √(n : ℝ) * R` using `by positivity`. Rewrite using `[minorProd, typeDegree, ← Finset.prod_pow_eq_pow_sum, mul_assoc]`. Use `(l1Norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => l1Norm_nonneg _) fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[pow_add]`. Use `(l1Norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (l1Norm_nonneg _) (by positivity))` and prove the remaining obligations.

Use `(l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1)) fun i _ => ?_).trans_eq ?_` and prove the remaining obligations. Conclude with `l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hε _ _)`. Simplify using `only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]`. Use `(l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1)) fun i _ => ?_).trans_eq ?_` and prove the remaining obligations. Conclude with `l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hφ _ _)`.

Simplify using `only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]`.
-/
theorem l1Norm_rowBlockLeadingMinorProduct_le [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → Fin n → ℂ) (φ : T → Fin q → Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ t a, ∑ k, ‖ε t a k‖ ^ 2 ≤ R ^ 2) (hφ : ∀ t b, ∑ k, ‖φ t b k‖ ^ 2 ≤ R ^ 2)
    {N : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    l1Norm (minorProd c c' ε φ) ≤ (N * √(n : ℝ) * R) ^ typeDegree c c' := by
  have hB : 0 ≤ √(n : ℝ) * R := by positivity
  rw [minorProd, typeDegree, ← Finset.prod_pow_eq_pow_sum, mul_assoc]
  refine (l1Norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => l1Norm_nonneg _) fun t _ => ?_)
  rw [pow_add]
  refine (l1Norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (l1Norm_nonneg _) (by positivity))
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hε _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hφ _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]

end Minor

section Length

variable {E : Type*} [CommRing E] {κ : Type*} [Fintype κ]

noncomputable def embSeminorm (τ : E →+* ℂ) : RingSeminorm E where
  toFun x := ‖τ x‖
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by simp
  mul_le' x y := by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem embSeminorm_apply (τ : E →+* ℂ) (x : E) : embSeminorm τ x = ‖τ x‖ := rfl

noncomputable def embVec (τ : E →+* ℂ) : (κ → E) →+ EuclideanSpace ℂ κ where
  toFun v := WithLp.toLp 2 fun k => τ (v k)
  map_zero' := by ext k; simp
  map_add' v w := by ext k; simp

omit [Fintype κ] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem embVec_apply (τ : E →+* ℂ) (v : κ → E) (k : κ) : embVec τ v k = τ (v k) := rfl

omit [Fintype κ] in

/- English proof (translation)
Use extensionality with `k`. Simplify using the standard rewrite rules.
-/
theorem embVec_smul (τ : E →+* ℂ) (x : E) (v : κ → E) : embVec τ (x • v) = τ x • embVec τ v := by
  ext k; simp

noncomputable def embLength (τ : E →+* ℂ) : AddGroupSeminorm (κ → E) where
  toFun v := ‖embVec τ v‖
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embLength_apply (τ : E →+* ℂ) (v : κ → E) : embLength τ v = ‖embVec τ v‖ := rfl

/- English proof (translation)
Rewrite using `[embLength_apply, EuclideanSpace.norm_sq_eq]`. Both sides reduce to the same expression.
-/
theorem embLength_sq (τ : E →+* ℂ) (v : κ → E) : embLength τ v ^ 2 = ∑ k, ‖τ (v k)‖ ^ 2 := by
  rw [embLength_apply, EuclideanSpace.norm_sq_eq]; rfl

/- English proof (translation)
Rewrite using `[embLength_apply, embVec_smul, norm_smul, embLength_apply]`.
-/
theorem embLength_smul (τ : E →+* ℂ) (x : E) (v : κ → E) :
    embLength τ (x • v) = ‖τ x‖ * embLength τ v := by
  rw [embLength_apply, embVec_smul, norm_smul, embLength_apply]

/- English proof (translation)
The claim follows from `(le_abs_self _).trans (sq_le_sq.mp (by rwa [embLength_sq]))`.
-/
theorem embLength_le_abs (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2) :
    embLength τ v ≤ |R| :=
  (le_abs_self _).trans (sq_le_sq.mp (by rwa [embLength_sq]))

/- English proof (translation)
Rewrite using `[← embLength_sq, ← sq_abs R]`. Conclude with `pow_le_pow_left₀ (apply_nonneg _ _) h 2`.
-/
theorem sum_sq_le_of_embLength_le (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : embLength τ v ≤ |R|) :
    ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2 := by
  rw [← embLength_sq, ← sq_abs R]
  exact pow_le_pow_left₀ (apply_nonneg _ _) h 2

/- English proof (translation)
Rewrite using `[map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Simplify using `only [map_mul, norm_mul, hs]`. Use `(le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))` and prove the remaining obligations. Rewrite using `[mul_pow, embLength_sq, embLength_sq]`.

Conclude with `Finset.sum_mul_sq_le_sq_mul_sq _ _ _`.
-/
theorem norm_emb_sum_mul_le (τ : E →+* ℂ) (s : E → E) (hs : ∀ x, ‖τ (s x)‖ = ‖τ x‖)
    (x y : κ → E) : ‖τ (∑ k, x k * s (y k))‖ ≤ embLength τ x * embLength τ y := by
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  simp only [map_mul, norm_mul, hs]
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  rw [mul_pow, embLength_sq, embLength_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/- English proof (translation)
Apply `sum_sq_le_of_embLength_le` to reduce the goal to its premises. Rewrite using `[embLength_apply, map_sum, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← embLength_apply, embLength_smul, map_natCast, Complex.norm_natCast]`. Conclude with `mul_le_mul (by exact_mod_cast hA i) (embLength_le_abs τ (hv i)) (apply_nonneg _ _) (Nat.cast_nonneg _)`.
-/
theorem sum_sq_combination_le (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (v : ι → κ → E) {ρ : ℝ}
    (hv : ∀ i, ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2) (A : ι → ℕ) {d : ℕ} (hA : ∀ i, A i ≤ d) :
    ∑ k, ‖τ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * d * ρ) ^ 2 := by
  apply sum_sq_le_of_embLength_le
  rw [embLength_apply, map_sum, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_assoc,
    ← nsmul_eq_mul, ← Finset.card_univ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_)
  rw [← embLength_apply, embLength_smul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul (by exact_mod_cast hA i) (embLength_le_abs τ (hv i)) (apply_nonneg _ _)
    (Nat.cast_nonneg _)

end Length

section Perp

open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem perpVec_eq_perpVector {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {p : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) :
    perpVec h e e' g = perpVector (fun a => (LinearMap.proj (e a)).comp h) e' g := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p n : ℕ}

/- English proof (translation)
Establish `hs : ∀ x, ‖τ (cc x)‖ = ‖τ x‖` using `fun x => by`. Rewrite using `[cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]`. Establish `key : ∀ u v, embLength τ u ≤ |R| → embLength τ v ≤ |R| → ‖τ (h u v)‖ ≤ |R| ^ 2` using `fun u v hu hv => by`. Rewrite using `[hh, sq]`. Conclude with `(norm_emb_sum_mul_le τ cc hs u v).trans (mul_le_mul hu hv (apply_nonneg _ _) (abs_nonneg _))`.

Apply `sum_sq_le_of_embLength_le` to reduce the goal to its premises. Rewrite using `[perpVec_eq_perpVector, abs_mul, Nat.abs_cast, abs_pow, pow_succ, pow_mul, ← mul_assoc]`. Conclude with `seminorm_perpVector_le (embSeminorm τ) (by simp) (embLength τ) (fun x v => (embLength_smul τ x v).le) _ e' g (fun a a' => key _ _ (embLength_le_abs τ (he' a')) (embLength_le_abs τ (he a))) (fun a => key _ _ (embLength_le_abs τ hg) (embLength_le_abs τ (he a))) (fun a => embLength_ …`.
-/
theorem sum_sq_perpVec_le (τ : E →+* ℂ) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (e e' : Fin p → Fin n → E) (g : Fin n → E) {R : ℝ}
    (he : ∀ a, ∑ k, ‖τ (e a k)‖ ^ 2 ≤ R ^ 2) (he' : ∀ a, ∑ k, ‖τ (e' a k)‖ ^ 2 ≤ R ^ 2)
    (hg : ∑ k, ‖τ (g k)‖ ^ 2 ≤ R ^ 2) :
    ∑ k, ‖τ (perpVec h e e' g k)‖ ^ 2 ≤ (((p + 1).factorial : ℝ) * R ^ (2 * p + 1)) ^ 2 := by
  have hs : ∀ x, ‖τ (cc x)‖ = ‖τ x‖ := fun x => by
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have key : ∀ u v, embLength τ u ≤ |R| → embLength τ v ≤ |R| → ‖τ (h u v)‖ ≤ |R| ^ 2 :=
    fun u v hu hv => by
      rw [hh, sq]
      exact (norm_emb_sum_mul_le τ cc hs u v).trans
        (mul_le_mul hu hv (apply_nonneg _ _) (abs_nonneg _))
  apply sum_sq_le_of_embLength_le
  rw [perpVec_eq_perpVector, abs_mul, Nat.abs_cast, abs_pow, pow_succ, pow_mul, ← mul_assoc]
  exact seminorm_perpVector_le (embSeminorm τ) (by simp) (embLength τ)
    (fun x v => (embLength_smul τ x v).le) _ e' g
    (fun a a' => key _ _ (embLength_le_abs τ (he' a')) (embLength_le_abs τ (he a)))
    (fun a => key _ _ (embLength_le_abs τ hg) (embLength_le_abs τ (he a)))
    (fun a => embLength_le_abs τ (he' a)) (embLength_le_abs τ hg)

end Perp

end GlobalTheory.GridSize
