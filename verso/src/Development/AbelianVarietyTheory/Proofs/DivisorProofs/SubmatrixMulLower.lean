import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.ChernCalc
open scoped Matrix ComplexOrder

namespace GlobalTheory.LeadingMinorPositivity

section Lin

variable {s : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `∑ l, T a l * M l b = ∑ l : {a : Fin s // (a : ℕ) < j}, T a l * M l b`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun l : Fin s => (l : ℕ) < j) (by simp) (fun l => T a l * M l b)]`. Use `(Finset.sum_filter_of_ne fun l _ hl => ?_).symm` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Use `hl ?_` and prove the remaining obligations. Rewrite using `[hT a l (by have := a.2; show (a.1 : ℕ) < l; omega), zero_mul]`.
-/
theorem submatrix_mul_lower {κ : Type} (T : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0)
    (M : Matrix (Fin s) κ ℂ) (j : ℕ) :
    (T * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id =
      T.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id := by
  ext a b
  change ∑ l, T a l * M l b = ∑ l : {a : Fin s // (a : ℕ) < j}, T a l * M l b
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin s => (l : ℕ) < j) (by simp)
    (fun l => T a l * M l b)]
  refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
  by_contra h
  refine hl ?_
  rw [hT a l (by have := a.2; show (a.1 : ℕ) < l; omega), zero_mul]

/- English proof (translation)
Set `v : {a : Fin s // (a : ℕ) < j} → Fin s` to `Subtype.val`. Establish `h1 : (G * Tᴴ).submatrix v v = G.submatrix v v * (T.submatrix v v)ᴴ`. Use `submatrix_mul_lower T hT (G.submatrix v id)ᴴ j` as an intermediate fact. Establish `h2` using `(congrArg Matrix.conjTranspose this).trans (Matrix.conjTranspose_mul _ _)`. Use `Eq.trans ?_ (h2.trans ?_)` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Both sides reduce to the same expression. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]`. Both sides reduce to the same expression. Establish `h3 : (T * G * Tᴴ).submatrix v v = T.submatrix v v * (G.submatrix v v * (T.submatrix v v)ᴴ)`.

Use `submatrix_mul_lower T hT ((G * Tᴴ).submatrix id v) j` as an intermediate fact. Rewrite using `[← h1, Matrix.mul_assoc]`. Conclude with `this`. Establish `h4 : (T.submatrix v v).det = ∏ a, T (v a) (v a)` using `Matrix.det_of_isLowerTriangular _ fun a b hab => hT _ _ hab`. Unfold `leadMinor`.

Express the relevant statement in the definitionally equal form `((T * G * Tᴴ).submatrix v v).det = _ * (G.submatrix v v).det`. Rewrite using `[h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h4, Finset.prod_subtype (p := fun l : Fin s => (l : ℕ) < j) _ (by simp), mul_left_comm, mul_comm]`. Use `congr 1`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]`.
-/
theorem leadMinor_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (j : ℕ) :
    leadMinor (T * G * Tᴴ) j =
      ((∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < j, ‖T a a‖ ^ 2 : ℝ) : ℂ) * leadMinor G j := by
  let v : {a : Fin s // (a : ℕ) < j} → Fin s := Subtype.val
  have h1 : (G * Tᴴ).submatrix v v = G.submatrix v v * (T.submatrix v v)ᴴ := by
    have := submatrix_mul_lower T hT (G.submatrix v id)ᴴ j
    have h2 := (congrArg Matrix.conjTranspose this).trans (Matrix.conjTranspose_mul _ _)
    refine Eq.trans ?_ (h2.trans ?_)
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rfl
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
      rfl
  have h3 : (T * G * Tᴴ).submatrix v v = T.submatrix v v * (G.submatrix v v * (T.submatrix v v)ᴴ) := by
    have := submatrix_mul_lower T hT ((G * Tᴴ).submatrix id v) j
    rw [← h1, Matrix.mul_assoc]
    exact this
  have h4 : (T.submatrix v v).det = ∏ a, T (v a) (v a) :=
    Matrix.det_of_isLowerTriangular _ fun a b hab => hT _ _ hab
  unfold leadMinor
  change ((T * G * Tᴴ).submatrix v v).det = _ * (G.submatrix v v).det
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h4,
    Finset.prod_subtype (p := fun l : Fin s => (l : ℕ) < j) _ (by simp), mul_left_comm, mul_comm]
  congr 1
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]

/- English proof (translation)
The claim follows from `(Complex.pos_iff.1 (hG.submatrix Subtype.val_injective).det_pos).1`.
-/
theorem leadMinor_re_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re :=
  (Complex.pos_iff.1 (hG.submatrix Subtype.val_injective).det_pos).1

/- English proof (translation)
The claim follows from `div_pos (leadMinor_re_pos hG _) (leadMinor_re_pos hG _)`.
-/
theorem grD_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (i : Fin s) : 0 < grD G i :=
  div_pos (leadMinor_re_pos hG _) (leadMinor_re_pos hG _)

/- English proof (translation)
Establish `e : (Finset.univ.filter fun l : Fin s => (l : ℕ) < i + 1) = insert i (Finset.univ.filter fun l : Fin s => (l : ℕ) < i)`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hp : (∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < i, ‖T a a‖ ^ 2 : ℝ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd a))`.

Rewrite using `[grD, grD, leadMinor_conj T G hT, leadMinor_conj T G hT, Complex.re_ofReal_mul, Complex.re_ofReal_mul, e, Finset.prod_insert (by simp), mul_comm (‖T i i‖ ^ 2), mul_assoc, mul_div_mul_left _ _ hp, mul_div_assoc]`.
-/
theorem grD_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (hd : ∀ a, T a a ≠ 0) (i : Fin s) :
    grD (T * G * Tᴴ) i = ‖T i i‖ ^ 2 * grD G i := by
  have e : (Finset.univ.filter fun l : Fin s => (l : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun l : Fin s => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hp : (∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < i, ‖T a a‖ ^ 2 : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd a))
  rw [grD, grD, leadMinor_conj T G hT, leadMinor_conj T G hT, Complex.re_ofReal_mul, Complex.re_ofReal_mul, e,
    Finset.prod_insert (by simp), mul_comm (‖T i i‖ ^ 2), mul_assoc, mul_div_mul_left _ _ hp, mul_div_assoc]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hl with h | h` into its components or cases. Rewrite using `[hT l i h, mul_zero]`. Rewrite using `[hS i l h, zero_mul]`.
-/
theorem diag_mul_lower {K : Type} [Field K] (S T : Matrix (Fin s) (Fin s) K) (hS : ∀ a b, a < b → S a b = 0)
    (hT : ∀ a b, a < b → T a b = 0) (i : Fin s) : (S * T) i i = S i i * T i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hT l i h, mul_zero]
  · rw [hS i l h, zero_mul]

end Lin

/- English proof (translation)
Take `⟨τ, i⟩` from `x`. Establish `hT` using `(Fr.mem_iff hA).1 hA'`. Establish `hS` using `(Fr.mem_iff (Fr.mem_genericPoint hA')).1 hB`. Take `⟨ψ, hψ⟩` from `exists_ratVal_hom y`. Establish `hV` using `hT.map_of (ratVal · y) ψ hψ τ`.

Establish `hlow : ∀ a b, a < b → (A' * A⁻¹).map (ratVal · y) τ a b = 0` using `fun a b h => hV.2.2.2 a b a.2 h`. Establish `hd : ∀ a, (A' * A⁻¹).map (ratVal · y) τ a a ≠ 0`. Establish `h` using `hV.2.1`. Rewrite `h` using `[Matrix.det_of_isLowerTriangular _ fun a b hab => hlow a b hab]`. Conclude with `fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)`.

Establish `e1 : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹)`. Rewrite using `[mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]`. Establish `e2 : (B * A⁻¹) τ i i / f = (B * A'⁻¹) τ i i / f * (A' * A⁻¹) τ i i`. Rewrite using `[e1, Pi.mul_apply (B * A'⁻¹), diag_mul_lower _ _ (fun a b h => (hS τ).2.2.2 a b a.2 h) (fun a b h => (hT τ).2.2.2 a b a.2 h), div_mul_eq_mul_div]`. Establish `hu0` using `ratVal_ne_zero hu`.

Establish `hur : RegAt (under y) ((B * A'⁻¹) τ i i / f)`. Assume the negation of the conclusion as `h`. Conclude with `hu0 (dif_neg h)`. Establish `ht : ratVal ((A' * A⁻¹) τ i i) y ≠ 0` using `hd i`. Establish `hg` using `(grD_pos (hH.posDef y A hA τ) i).ne'`.

Establish `e3 : grD (H A' y τ) i = ‖ratVal ((A' * A⁻¹) τ i i) y‖ ^ 2 * grD (H A y τ) i`. Rewrite using `[hH.trans y A hA A' hA' τ]`. Conclude with `grD_conj _ _ hlow hd i`. Establish `n1` using `pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)`. Establish `n2` using `pow_ne_zero 2 (norm_ne_zero_iff.2 ht)`.

Simplify using `only at n1 ⊢`. Rewrite using `[e2, e3, ratVal_mul hur (mem_O_ratOf.1 ((hT τ).1 i i)), norm_mul, mul_pow, Real.log_mul n1 n2, Real.log_mul n2 hg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem green_frame_indep (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H)
    (B : Mat m X.Fn) (hB : B ∈ E.S (genericPoint X.X)) (y : GlobalTheory.CxPts X.str σ)
    (A : Mat m X.Fn) (hA : A ∈ E.S (under y)) (A' : Mat m X.Fn) (hA' : A' ∈ E.S (under y))
    (x : Root m) (f : X.Fn) (hu : UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f)) :
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
      -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  obtain ⟨τ, i⟩ := x
  have hT := (Fr.mem_iff hA).1 hA'
  have hS := (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hB
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  have hV := hT.map_of (ratVal · y) ψ hψ τ
  have hlow : ∀ a b, a < b → (A' * A⁻¹).map (ratVal · y) τ a b = 0 := fun a b h => hV.2.2.2 a b a.2 h
  have hd : ∀ a, (A' * A⁻¹).map (ratVal · y) τ a a ≠ 0 := by
    have h := hV.2.1
    rw [Matrix.det_of_isLowerTriangular _ fun a b hab => hlow a b hab] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  have e1 : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
    rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
  have e2 : (B * A⁻¹) τ i i / f = (B * A'⁻¹) τ i i / f * (A' * A⁻¹) τ i i := by
    rw [e1, Pi.mul_apply (B * A'⁻¹), diag_mul_lower _ _ (fun a b h => (hS τ).2.2.2 a b a.2 h)
      (fun a b h => (hT τ).2.2.2 a b a.2 h), div_mul_eq_mul_div]
  have hu0 := ratVal_ne_zero hu
  have hur : RegAt (under y) ((B * A'⁻¹) τ i i / f) := by
    by_contra h
    exact hu0 (dif_neg h)
  have ht : ratVal ((A' * A⁻¹) τ i i) y ≠ 0 := hd i
  have hg := (grD_pos (hH.posDef y A hA τ) i).ne'
  have e3 : grD (H A' y τ) i = ‖ratVal ((A' * A⁻¹) τ i i) y‖ ^ 2 * grD (H A y τ) i := by
    rw [hH.trans y A hA A' hA' τ]
    exact grD_conj _ _ hlow hd i
  have n1 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)
  have n2 := pow_ne_zero 2 (norm_ne_zero_iff.2 ht)
  dsimp only at n1 ⊢
  rw [e2, e3, ratVal_mul hur (mem_O_ratOf.1 ((hT τ).1 i i)), norm_mul, mul_pow, Real.log_mul n1 n2,
    Real.log_mul n2 hg]
  ring

end GlobalTheory.LeadingMinorPositivity
