import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinkowskiLinearForms

namespace GlobalTheory.HermClass

open MeasureTheory Module Submodule NumberField Matrix

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms`. Consider the case `exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms`. Consider the case `(apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms ..)`.
-/
theorem exists_int_vecMul_lt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) (h : |A.det| < t ^ Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ j, |∑ i, (z i : ℝ) * A i j| < t := by
  first
  | exact @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | (apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms ..)

/- English proof (translation)
Establish `hM' : (M : ℚ) ≠ 0` using `by exact_mod_cast hM`. Establish `h0 : T.det ≠ 0`. Introduce `hd`. Take `⟨x, hx0, hx⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hd`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hx0`.

Establish `hi' : x i ≠ 0` using `hi`. Take `⟨m, hm⟩` from `h ((2 * M * x i)⁻¹ • x) (fun j => ⟨0, by rw [Matrix.smul_vecMul, hx]; simp⟩) i`. Establish `h2 : (2 * m : ℚ) = 1`. Rewrite using `[← hm]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Establish `h3 : 2 * m = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Use `⟨h0, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit T.det` using `isUnit_iff_ne_zero.2 h0`.

Establish `hK : ∀ k i, ∃ m : ℤ, M * T⁻¹ k i = m` using `fun k => h (T⁻¹ k) fun j => by`. Establish `: (T⁻¹ k ᵥ* T) j = (T⁻¹ * T) k j` using `rfl`. Rewrite using `[this, Matrix.nonsing_inv_mul T hu, Matrix.one_apply]`. Use `split_ifs`. Conclude with `⟨1, by simp⟩`.

Conclude with `⟨0, by simp⟩`. Use `choose K hK using hK`. Establish `hKe : (Int.castRingHom ℚ).mapMatrix (Matrix.of K) = (M : ℚ) • T⁻¹`. Use extensionality with `k i`. Simplify using `[← hK]`.

Establish `hdet : (((Matrix.of K).det : ℤ) : ℚ) * T.det = (M : ℚ) ^ Fintype.card ι`. Use `(Int.castRingHom ℚ).map_det (Matrix.of K)` as an intermediate fact. Rewrite `this` using `[hKe, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Rewrite using `[← eq_intCast (Int.castRingHom ℚ), this]`. Clear the denominators using the available nonvanishing facts.

Establish `hK0 : (Matrix.of K).det ≠ 0`. Introduce `hz`. Rewrite `hdet` using `[hz]`. Conclude with `pow_ne_zero _ hM' (by simpa using hdet.symm)`. Establish `h1 : (1 : ℚ) ≤ |(((Matrix.of K).det : ℤ) : ℚ)|` using `by exact_mod_cast Int.one_le_abs hK0`.

Rewrite using `[← abs_pow, ← hdet, abs_mul]`. Conclude with `le_mul_of_one_le_left (abs_nonneg _) h1`.
-/
theorem det_ne_zero_and_abs_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℚ)
    {M : ℤ} (hM : M ≠ 0)
    (h : ∀ x : ι → ℚ, (∀ j, ∃ m : ℤ, (x ᵥ* T) j = m) → ∀ i, ∃ m : ℤ, M * x i = m) :
    T.det ≠ 0 ∧ |T.det| ≤ |(M : ℚ)| ^ Fintype.card ι := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have h0 : T.det ≠ 0 := by
    intro hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    have hi' : x i ≠ 0 := hi
    obtain ⟨m, hm⟩ := h ((2 * M * x i)⁻¹ • x) (fun j => ⟨0, by rw [Matrix.smul_vecMul, hx]; simp⟩) i
    have h2 : (2 * m : ℚ) = 1 := by
      rw [← hm]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
  refine ⟨h0, ?_⟩
  have hu : IsUnit T.det := isUnit_iff_ne_zero.2 h0
  have hK : ∀ k i, ∃ m : ℤ, M * T⁻¹ k i = m := fun k => h (T⁻¹ k) fun j => by
    have : (T⁻¹ k ᵥ* T) j = (T⁻¹ * T) k j := rfl
    rw [this, Matrix.nonsing_inv_mul T hu, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  choose K hK using hK
  have hKe : (Int.castRingHom ℚ).mapMatrix (Matrix.of K) = (M : ℚ) • T⁻¹ := by
    ext k i; simp [← hK]
  have hdet : (((Matrix.of K).det : ℤ) : ℚ) * T.det = (M : ℚ) ^ Fintype.card ι := by
    have := (Int.castRingHom ℚ).map_det (Matrix.of K)
    rw [hKe, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at this
    rw [← eq_intCast (Int.castRingHom ℚ), this]; field_simp
  have hK0 : (Matrix.of K).det ≠ 0 := by
    intro hz; rw [hz] at hdet
    exact pow_ne_zero _ hM' (by simpa using hdet.symm)
  have h1 : (1 : ℚ) ≤ |(((Matrix.of K).det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hK0
  rw [← abs_pow, ← hdet, abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

/- English proof (translation)
Use `haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero`. Take `⟨e, he⟩` from `LinearMap.BilinForm.exists_orthogonal_basis hq`. Use `set ρ : (F →+* ℂ) → (F →+* ℝ) := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding with hρ`. Establish `hρc : ∀ φ x, ((ρ φ x : ℝ) : ℂ) = φ x` using `fun φ x => by simp [hρ]`. Establish `hqe : ∀ x y, q x y = ∑ k, e.repr x k * e.repr y k * q (e k) (e k)`.

Introduce `x y`. Use `conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `l _ hl`. Establish `: q (e l) (e k) = 0` using `he hl`. Rewrite using `[this, mul_zero]`. Simplify using the standard rewrite rules.

Establish `htr : ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, ρ φ x`. Introduce `x`. Establish `h` using `trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)`. Rewrite `h` using `[← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x) _ (fun _ => rfl)]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Simplify using `only [Complex.ofReal_sum, hρc, ← h]`. Simplify using the standard rewrite rules. Set `ε : κ ≃ (F →+* ℂ) × Fin (finrank F V)` to `Fintype.equivOfCardEq (by`. Rewrite using `[hκ, Fintype.card_prod, Embeddings.card, Fintype.card_fin])`. Set `a : κ → ℝ` to `fun j => ρ (ε j).1 (q (e (ε j).2) (e (ε j).2))`.

Set `B : Matrix κ κ ℝ` to `Matrix.of fun i j => ρ (ε j).1 (e.repr (b i) (ε j).2)`. Use `set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT`. Establish `hTB : (Rat.castHom ℝ).mapMatrix T = B * Matrix.diagonal a * Bᵀ`. Use extensionality with `i i'`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply, eq_ratCast, htr, Matrix.transpose_apply, B, a]`. Rewrite using `[Fintype.sum_equiv ε _ (fun p => ρ p.1 (e.repr (b i) p.2) * ρ p.1 (q (e p.2) (e p.2)) * ρ p.1 (e.repr (b i') p.2)) (fun _ => rfl), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[hqe, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdT : ((T.det : ℚ) : ℝ) = B.det ^ 2 * ∏ j, a j`. Use `(Rat.castHom ℝ).map_det T` as an intermediate fact. Rewrite `this` using `[hTB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`.

Rewrite using `[← eq_ratCast (Rat.castHom ℝ), this]`. Expand and normalize the polynomial expressions, which then agree. Set `A : Matrix κ κ ℝ` to `B * Matrix.diagonal fun j => Real.sqrt |a j|`. Establish `hdA : A.det ^ 2 = |((T.det : ℚ) : ℝ)|`. Rewrite using `[hdT, Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← Finset.prod_pow, abs_mul, Finset.abs_prod, abs_of_nonneg (sq_nonneg B.det)]`.

Simplify using `only [Real.sq_sqrt (abs_nonneg _)]`. Establish `hA0 : A.det ≠ 0`. Introduce `hz`. Rewrite `hdA` using `[hz]`. Apply `h0` to reduce the goal to its premises.

Establish `: ((T.det : ℚ) : ℝ) = 0` using `by simpa using hdA.symm`. Conclude with `this` after adjusting the coercions. Establish `hA1 : |A.det| < t ^ Fintype.card κ`. Apply `abs_lt_of_sq_lt_sq _ (by positivity)` to reduce the goal to its premises. Rewrite using `[hdA]` and apply the resulting hypothesis.

Take `⟨z, hz0, hz⟩` from `exists_int_vecMul_lt A hA0 ht hA1`. Use `⟨z, hz0, fun φ => ?_⟩` and prove the remaining obligations. Use `set v := ∑ i, z i • b i with hv`. Rewrite using `[← hρc, Complex.norm_real, hqe, map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Establish `: ∀ k, ‖ρ φ (e.repr v k * e.repr v k * q (e k) (e k))‖ ≤ t ^ 2`. Introduce `k`. Establish `h2` using `hz (ε.symm (φ, k))`. Establish `h3 : ∑ i, (z i : ℝ) * A i (ε.symm (φ, k)) = ρ φ (e.repr v k) * Real.sqrt |ρ φ (q (e k) (e k))|`. Establish `hc : e.repr v k = ∑ i, (z i : F) * e.repr (b i) k`.

Rewrite using `[← e.coord_apply, hv, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_mul, e.coord_apply]`. Rewrite using `[hc, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [A, Matrix.mul_diagonal, B, a, Matrix.of_apply, Equiv.apply_symm_apply, mul_assoc, map_mul, map_intCast]`. Rewrite `h2` using `[h3]`. Establish `h4` using `(sq_lt_sq' (abs_lt.1 h2).1 (abs_lt.1 h2).2).le`. Rewrite `h4` using `[mul_pow, Real.sq_sqrt (abs_nonneg _)]`. Rewrite using `[map_mul, map_mul, Real.norm_eq_abs, abs_mul, abs_mul_self]`.

Rewrite `h4` using `[sq]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_short_of_trace_det {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : LinearMap.BilinForm F V) (hq : LinearMap.IsSymm q) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → V) (hκ : Fintype.card κ = finrank ℚ F * finrank F V) {t : ℝ} (ht : 0 < t)
    (h0 : (Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det ≠ 0)
    (h1 : |(((Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det : ℚ) : ℝ)| <
      (t ^ Fintype.card κ) ^ 2) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ ∀ φ : F →+* ℂ,
      ‖φ (q (∑ i, z i • b i) (∑ i, z i • b i))‖ ≤ finrank F V * t ^ 2 := by
  classical
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hq
  set ρ : (F →+* ℂ) → (F →+* ℝ) := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
    with hρ
  have hρc : ∀ φ x, ((ρ φ x : ℝ) : ℂ) = φ x := fun φ x => by simp [hρ]
  have hqe : ∀ x y, q x y = ∑ k, e.repr x k * e.repr y k * q (e k) (e k) := by
    intro x y
    conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hl
      have : q (e l) (e k) = 0 := he hl
      rw [this, mul_zero]
    · simp
  have htr : ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, ρ φ x := by
    intro x
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x) _ (fun _ => rfl)] at h
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, hρc, ← h]
    simp
  let ε : κ ≃ (F →+* ℂ) × Fin (finrank F V) := Fintype.equivOfCardEq (by
    rw [hκ, Fintype.card_prod, Embeddings.card, Fintype.card_fin])
  let a : κ → ℝ := fun j => ρ (ε j).1 (q (e (ε j).2) (e (ε j).2))
  let B : Matrix κ κ ℝ := Matrix.of fun i j => ρ (ε j).1 (e.repr (b i) (ε j).2)
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  have hTB : (Rat.castHom ℝ).mapMatrix T = B * Matrix.diagonal a * Bᵀ := by
    ext i i'
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply,
      eq_ratCast, htr, Matrix.transpose_apply, B, a]
    rw [Fintype.sum_equiv ε _ (fun p => ρ p.1 (e.repr (b i) p.2) * ρ p.1 (q (e p.2) (e p.2)) *
      ρ p.1 (e.repr (b i') p.2)) (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [hqe, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  have hdT : ((T.det : ℚ) : ℝ) = B.det ^ 2 * ∏ j, a j := by
    have := (Rat.castHom ℝ).map_det T
    rw [hTB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← eq_ratCast (Rat.castHom ℝ), this]; ring
  let A : Matrix κ κ ℝ := B * Matrix.diagonal fun j => Real.sqrt |a j|
  have hdA : A.det ^ 2 = |((T.det : ℚ) : ℝ)| := by
    rw [hdT, Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← Finset.prod_pow, abs_mul,
      Finset.abs_prod, abs_of_nonneg (sq_nonneg B.det)]
    simp only [Real.sq_sqrt (abs_nonneg _)]
  have hA0 : A.det ≠ 0 := by
    intro hz
    rw [hz] at hdA
    apply h0
    have : ((T.det : ℚ) : ℝ) = 0 := by simpa using hdA.symm
    exact_mod_cast this
  have hA1 : |A.det| < t ^ Fintype.card κ := by
    apply abs_lt_of_sq_lt_sq _ (by positivity)
    rwa [hdA]
  obtain ⟨z, hz0, hz⟩ := exists_int_vecMul_lt A hA0 ht hA1
  refine ⟨z, hz0, fun φ => ?_⟩
  set v := ∑ i, z i • b i with hv
  rw [← hρc, Complex.norm_real, hqe, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k, ‖ρ φ (e.repr v k * e.repr v k * q (e k) (e k))‖ ≤ t ^ 2 := by
    intro k
    have h2 := hz (ε.symm (φ, k))
    have h3 : ∑ i, (z i : ℝ) * A i (ε.symm (φ, k)) =
        ρ φ (e.repr v k) * Real.sqrt |ρ φ (q (e k) (e k))| := by
      have hc : e.repr v k = ∑ i, (z i : F) * e.repr (b i) k := by
        rw [← e.coord_apply, hv, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, zsmul_eq_mul, e.coord_apply]
      rw [hc, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [A, Matrix.mul_diagonal, B, a, Matrix.of_apply, Equiv.apply_symm_apply,
        mul_assoc, map_mul, map_intCast]
    rw [h3] at h2
    have h4 := (sq_lt_sq' (abs_lt.1 h2).1 (abs_lt.1 h2).2).le
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)] at h4
    rw [map_mul, map_mul, Real.norm_eq_abs, abs_mul, abs_mul_self]
    rwa [sq] at h4
  calc _ ≤ ∑ _k : Fin (finrank F V), t ^ 2 := Finset.sum_le_sum fun k _ => this k
    _ = _ := by simp

end GlobalTheory.HermClass
