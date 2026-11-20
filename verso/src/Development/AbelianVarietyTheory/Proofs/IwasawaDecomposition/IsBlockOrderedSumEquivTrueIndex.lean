import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded

noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q m : ℕ}

abbrev Low (m : ℕ) : Type := {s : Fin m × Fin m // s.2 < s.1}

def uni (y : Low m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => if h : b < a then y ⟨(a, b), h⟩ else if a = b then 1 else 0

def dens (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : ℝ :=
  ∏ i : Fin m, ‖lminor ((uni y)ᴴ * A * uni y) i.castSucc‖ ^ (-2 : ℤ)

def IsBlockSL2Embedding (e : Fin r ≃ Fin p ⊕ Fin q) : Prop :=
  (∀ a, (e.symm (Sum.inl a) : ℕ) = q + a) ∧ ∀ a, (e.symm (Sum.inr a) : ℕ) = a

def toMat (v : Fin p × Fin q → ℂ) : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun a b => v (a, b)

def glue (e : Fin r ≃ Fin p ⊕ Fin q) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : Low r → ℂ :=
  fun s => fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) (e s.1.1) (e s.1.2)

def base (e : Fin r ≃ Fin p ⊕ Fin q) (y : Low r → ℂ) : Fin p × Fin q → ℂ := vecOf (moeb (reindex e e (uni y)) 0)

def shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  (fromBlocks 1 Z 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * A * fromBlocks 1 Z 0 1

def schur (H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₂₁

def sgnMat (r q : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨idx_symm_inl h, idx_symm_inr h⟩`.
-/
theorem isBlockOrderedSumEquiv_trueIndex {r j : ℕ} (h : j ≤ r) : IsBlockSL2Embedding (idx h) := ⟨idx_symm_inl h, idx_symm_inr h⟩

/- English proof (translation)
Simplify using `using Fintype.card_congr e`.
-/
theorem IsBlockSL2Embedding.card {e : Fin r ≃ Fin p ⊕ Fin q} (_ : IsBlockSL2Embedding e) : r = p + q := by
  simpa using Fintype.card_congr e

/- English proof (translation)
Assemble the required witnesses or components as `⟨((finCongr (add_comm p q)).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _), by constructor <;> intro a <;> simp [add_comm]⟩`.
-/
theorem exists_isBlockOrderedSumEquiv (p q : ℕ) : ∃ e : Fin (p + q) ≃ Fin p ⊕ Fin q, IsBlockSL2Embedding e :=
  ⟨((finCongr (add_comm p q)).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _), by
    constructor <;> intro a <;> simp [add_comm]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem toMat_vecOf (Z : Matrix (Fin p) (Fin q) ℂ) : toMat (vecOf Z) = Z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem vecOf_toMat (v : Fin p × Fin q → ℂ) : vecOf (toMat v) = v := rfl

/- English proof (translation)
Rewrite using `[det_of_lowerTriangular]`. Simplify using `[uni]`. Introduce `a b h`. Establish `h' : a < b` using `h`. Simplify using `[uni, not_lt_of_gt h', h'.ne]`.
-/
theorem det_uni (y : Low m → ℂ) : (uni y).det = 1 := by
  rw [det_of_lowerTriangular]
  · simp [uni]
  · intro a b h
    have h' : a < b := h
    simp [uni, not_lt_of_gt h', h'.ne]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[reindex_apply, submatrix_apply]`. Distinguish the cases in `hab : e.symm b < e.symm a`. Simplify using `only [uni, of_apply, dif_pos hab]`. Rewrite using `[h]`.

Simplify using `[uni]`. Simplify using `only [uni, of_apply, dif_neg hab, EmbeddingLike.apply_eq_iff_eq]`. Rewrite `hab` using `[Fin.lt_def]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab`. Establish `: ¬ b < a` using `by rw [Fin.lt_def]; omega`.

Simplify using `[this]`. Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish `: ¬ b < a` using `by rw [Fin.lt_def]; omega`.

Simplify using `[this]`.
-/
theorem uni_eq_of_entries {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (y : Low r → ℂ) (y1 : Low q → ℂ) (y2 : Low p → ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) (h : ∀ s : Low r, y s = fromBlocks (uni y2) Y 0 (uni y1) (e s.1.1) (e s.1.2)) :
    reindex e e (uni y) = fromBlocks (uni y2) Y 0 (uni y1) := by
  ext a b
  rw [reindex_apply, submatrix_apply]
  by_cases hab : e.symm b < e.symm a
  · simp only [uni, of_apply, dif_pos hab]
    rw [h]; simp [uni]
  · simp only [uni, of_apply, dif_neg hab, EmbeddingLike.apply_eq_iff_eq]
    rw [Fin.lt_def] at hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]
    · have := b.2; omega
    · simp
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]

/- English proof (translation)
The claim follows from `uni_eq_of_entries he _ _ _ _ fun _ => rfl`.
-/
theorem reindex_uni_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e (uni (glue e w)) = fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) :=
  uni_eq_of_entries he _ _ _ _ fun _ => rfl

/- English proof (translation)
Rewrite using `[base, reindex_uni_glue he, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, mul_nonsing_inv_cancel_right _ _ (by rw [det_uni]; exact isUnit_one), vecOf_toMat]`.
-/
theorem base_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : base e (glue e w) = w.1 := by
  rw [base, reindex_uni_glue he, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    mul_nonsing_inv_cancel_right _ _ (by rw [det_uni]; exact isUnit_one), vecOf_toMat]

/- English proof (translation)
Introduce `y`. Use `set M := reindex e e (uni y) with hM`. Set `y1 : Low q → ℂ` to `fun s => M (.inr s.1.1) (.inr s.1.2)`. Use `⟨(vecOf (M.toBlocks₁₂ * (uni y1)⁻¹), y1, fun s => M (.inl s.1.1) (.inl s.1.2)), funext fun s => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, b⟩, hab⟩` from `s`.

Take `⟨a, rfl⟩` from `e.symm.surjective a`. Take `⟨b, rfl⟩` from `e.symm.surjective b`. Establish `hy : y ⟨(e.symm a, e.symm b), hab⟩ = M a b`. Establish `hab' : e.symm b < e.symm a` using `hab`. Simplify using `only [hM, reindex_apply, submatrix_apply, uni, of_apply, dif_pos hab']`.

Rewrite using `[hy]`. Simplify using `only [glue, toMat_vecOf, Equiv.apply_symm_apply]`. Rewrite using `[nonsing_inv_mul_cancel_right _ _ (by rw [det_uni]; exact isUnit_one)]`. Use `replace hab : (e.symm b : ℕ) < e.symm a := hab`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab`.

Establish `: b < a` using `by rw [Fin.lt_def]; omega`. Simplify using `[uni, this]`. Both sides reduce to the same expression. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `: b < a` using `hab`. Simplify using `[uni, this, y1]`.
-/
theorem glue_surjective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Surjective (glue e) := by
  intro y
  set M := reindex e e (uni y) with hM
  let y1 : Low q → ℂ := fun s => M (.inr s.1.1) (.inr s.1.2)
  refine ⟨(vecOf (M.toBlocks₁₂ * (uni y1)⁻¹), y1, fun s => M (.inl s.1.1) (.inl s.1.2)), funext fun s => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := s
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨b, rfl⟩ := e.symm.surjective b
  have hy : y ⟨(e.symm a, e.symm b), hab⟩ = M a b := by
    have hab' : e.symm b < e.symm a := hab
    simp only [hM, reindex_apply, submatrix_apply, uni, of_apply, dif_pos hab']
  rw [hy]
  simp only [glue, toMat_vecOf, Equiv.apply_symm_apply]
  rw [nonsing_inv_mul_cancel_right _ _ (by rw [det_uni]; exact isUnit_one)]
  replace hab : (e.symm b : ℕ) < e.symm a := hab
  rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
  · have : b < a := by rw [Fin.lt_def]; omega
    simp [uni, this]
  · rfl
  · have := a.2; omega
  · have : b < a := hab
    simp [uni, this, y1]

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Simplify using `only [uni, of_apply]`. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem continuous_uni : Continuous (uni : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) := by
  refine continuous_matrix fun a b => ?_
  simp only [uni, of_apply]
  split_ifs <;> fun_prop

/- English proof (translation)
The claim follows from `continuous_matrix fun a b => continuous_apply (a, b)`.
-/
theorem continuous_toMat : Continuous (toMat : (Fin p × Fin q → ℂ) → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_matrix fun a b => continuous_apply (a, b)

/- English proof (translation)
Use `continuous_pi fun s => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.1` using `continuous_uni.comp (by fun_prop)`. Establish `h2 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.2` using `continuous_uni.comp (by fun_prop)`. Conclude with `(h2.matrix_fromBlocks ((continuous_toMat.comp continuous_fst).matrix_mul h1) continuous_const h1).matrix_elem _ _`.
-/
theorem continuous_glue (e : Fin r ≃ Fin p ⊕ Fin q) : Continuous (glue e) := by
  refine continuous_pi fun s => ?_
  have h1 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.1 :=
    continuous_uni.comp (by fun_prop)
  have h2 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.2 :=
    continuous_uni.comp (by fun_prop)
  exact (h2.matrix_fromBlocks ((continuous_toMat.comp continuous_fst).matrix_mul h1) continuous_const h1).matrix_elem _ _

/- English proof (translation)
Use `Finset.measurable_prod _ fun i _ => Measurable.pow_const (Continuous.measurable (Continuous.norm ?_)) _` and prove the remaining obligations. Conclude with `(((continuous_uni.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_uni).matrix_submatrix _ _).matrix_det`.
-/
theorem measurable_dens (A : Matrix (Fin m) (Fin m) ℂ) : Measurable (dens A) := by
  refine Finset.measurable_prod _ fun i _ => Measurable.pow_const (Continuous.measurable (Continuous.norm ?_)) _
  exact (((continuous_uni.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_uni).matrix_submatrix _ _).matrix_det

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => zpow_nonneg (norm_nonneg _) _`.
-/
theorem dens_nonneg (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : 0 ≤ dens A y :=
  Finset.prod_nonneg fun _ _ => zpow_nonneg (norm_nonneg _) _

/- English proof (translation)
Establish `h2 : Continuous fun x => (g x).toBlocks₂₂` using `continuous_matrix fun _ _ => hg.matrix_elem _ _`. Simplify using `only [moeb_zero, mul_apply, inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`. Conclude with `Finset.measurable_sum _ fun c _ => (hg.matrix_elem (.inl a) (.inr c)).measurable.mul (h2.matrix_det.measurable.inv.mul (h2.matrix_adjugate.matrix_elem _ _).measurable)`.
-/
theorem measurable_moeb_zero {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {g : α → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : Continuous g) (a : Fin p) (b : Fin q) :
    Measurable fun x => moeb (g x) 0 a b := by
  have h2 : Continuous fun x => (g x).toBlocks₂₂ := continuous_matrix fun _ _ => hg.matrix_elem _ _
  simp only [moeb_zero, mul_apply, inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun c _ => (hg.matrix_elem (.inl a) (.inr c)).measurable.mul
    (h2.matrix_det.measurable.inv.mul (h2.matrix_adjugate.matrix_elem _ _).measurable)

/- English proof (translation)
The claim follows from `measurable_pi_lambda _ fun s => measurable_moeb_zero (continuous_uni.matrix_submatrix _ _) s.1 s.2`.
-/
theorem measurable_base (e : Fin r ≃ Fin p ⊕ Fin q) : Measurable (base e) :=
  measurable_pi_lambda _ fun s => measurable_moeb_zero (continuous_uni.matrix_submatrix _ _) s.1 s.2

/- English proof (translation)
Simplify using `[shear, det_conjTranspose, det_fromBlocks_zero₂₁]`.
-/
theorem det_shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).det = A.det := by
  simp [shear, det_conjTranspose, det_fromBlocks_zero₂₁]

/- English proof (translation)
The claim follows from `hA.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by simp [det_fromBlocks_zero₂₁])))`.
-/
theorem posDef_shear {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).PosDef :=
  hA.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2
    (by simp [det_fromBlocks_zero₂₁])))

/- English proof (translation)
Use `letI := invertibleOfIsUnitDet _ h`. Use `conv_lhs => rw [← fromBlocks_toBlocks H, det_fromBlocks₂₂]`. Rewrite using `[schur, invOf_eq_nonsing_inv]`.
-/
theorem det_eq_mul_schur {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUnit H.toBlocks₂₂.det) :
    H.det = H.toBlocks₂₂.det * (schur H).det := by
  letI := invertibleOfIsUnitDet _ h
  conv_lhs => rw [← fromBlocks_toBlocks H, det_fromBlocks₂₂]
  rw [schur, invOf_eq_nonsing_inv]

/- English proof (translation)
Establish `h1 : H.toBlocks₁₁.PosDef` using `h.submatrix Sum.inl_injective`. Establish `h2 : H.toBlocks₂₂.PosDef` using `h.submatrix Sum.inr_injective`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Use `letI := invertibleOfIsUnitDet _ h2.det_pos.ne'.isUnit`. Establish `e : H.toBlocks₂₁ = H.toBlocks₁₂ᴴ`.

Use extensionality with `a b`. Conclude with `(h.1.apply _ _).symm`. Establish `h3` using `h.posSemidef`. Rewrite `h3` using `[← fromBlocks_toBlocks H, e, PosDef.fromBlocks₂₂ _ _ h2, ← e]`. Use `h3.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 ?_)` and prove the remaining obligations.

Establish `h4` using `h.det_pos.ne'`. Rewrite `h4` using `[det_eq_mul_schur h2.det_pos.ne'.isUnit]`. Conclude with `(right_ne_zero_of_mul h4).isUnit`.
-/
theorem posDef_blocks {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : H.PosDef) :
    H.toBlocks₁₁.PosDef ∧ H.toBlocks₂₂.PosDef ∧ (schur H).PosDef := by
  have h1 : H.toBlocks₁₁.PosDef := h.submatrix Sum.inl_injective
  have h2 : H.toBlocks₂₂.PosDef := h.submatrix Sum.inr_injective
  refine ⟨h1, h2, ?_⟩
  letI := invertibleOfIsUnitDet _ h2.det_pos.ne'.isUnit
  have e : H.toBlocks₂₁ = H.toBlocks₁₂ᴴ := by
    ext a b
    exact (h.1.apply _ _).symm
  have h3 := h.posSemidef
  rw [← fromBlocks_toBlocks H, e, PosDef.fromBlocks₂₂ _ _ h2, ← e] at h3
  refine h3.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 ?_)
  have h4 := h.det_pos.ne'
  rw [det_eq_mul_schur h2.det_pos.ne'.isUnit] at h4
  exact (right_ne_zero_of_mul h4).isUnit

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type}
  (ι : Tau → X.Ψ)

def coords (z : V (nd X)) : Tau → Low r → ℂ := fun t s => z (Fintype.equivFin (Ent X) ⟨ι t, s⟩)

def proj (z : V (nd X)) : Tau × Fin j × Fin (r - j) → ℂ := flat (domPt X hj ι (cpt X (x0F X) z))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_nmat (z : V (nd X)) (t : Tau) : mat (nmat X z) (ι t) = uni (coords X ι z t) := rfl

/- English proof (translation)
The claim follows from `measurable_pi_lambda _ fun s => measurable_moeb_zero ((continuous_const.matrix_mul (KU.cont_mat X (ι s.1))).matrix_submatrix _ _) s.2.1 s.2.2`.
-/
theorem measurable_domPt : Measurable fun x : Frame X.Ψ r => flat (domPt X hj ι x) :=
  measurable_pi_lambda _ fun s => measurable_moeb_zero
    ((continuous_const.matrix_mul (KU.cont_mat X (ι s.1))).matrix_submatrix _ _) s.2.1 s.2.2

/- English proof (translation)
The claim follows from `(measurable_domPt X hj ι).comp (KU.cont_cpt X _).measurable`.
-/
theorem measurable_proj : Measurable (proj X hj ι) := (measurable_domPt X hj ι).comp (KU.cont_cpt X _).measurable

/- English proof (translation)
Establish `e : frameCo X hj (cpt X (x0F X) z) (ι t) = reindex (idx hj) (idx hj) (uni (coords X ι z t))`. Rewrite using `[frameCo, ← mat_nmat]`. Use `congr 1`. Conclude with `nonsing_inv_mul_cancel_left _ _ (det_x0F X (ι t)).isUnit`. Simplify using `only [proj, flat, domPt, base, vecOf, e]`.
-/
theorem proj_eq (z : V (nd X)) (t : Tau) (s : Fin j × Fin (r - j)) :
    proj X hj ι z (t, s) = base (idx hj) (coords X ι z t) s := by
  have e : frameCo X hj (cpt X (x0F X) z) (ι t) = reindex (idx hj) (idx hj) (uni (coords X ι z t)) := by
    rw [frameCo, ← mat_nmat]
    congr 1
    exact nonsing_inv_mul_cancel_left _ _ (det_x0F X (ι t)).isUnit
  simp only [proj, flat, domPt, base, vecOf, e]

/- English proof (translation)
Establish `h0` using `congrArg transpose (isOrth_x0F X (ι t))`. Rewrite `h0` using `[gram_eq_mul, diagonal_transpose]`. Establish `h1` using `gram_eq_mul (ι t).1 X.Gm (mat (cpt X (x0F X) z) (ι t))`. Establish `e : mat (cpt X (x0F X) z) (ι t) = mat (x0F X) (ι t) * uni (coords X ι z t)` using `rfl`. Rewrite using `[sgnMat, ← h0, dmin, lminor, ← det_transpose, transpose_submatrix, h1, e, lminor]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem dmin_cpt (z : V (nd X)) (t : Tau) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X (x0F X) z) (ι t) i =
      lminor ((uni (coords X ι z t))ᴴ * sgnMat r X.p0 * uni (coords X ι z t)) i := by
  have h0 := congrArg transpose (isOrth_x0F X (ι t))
  rw [gram_eq_mul, diagonal_transpose] at h0
  have h1 := gram_eq_mul (ι t).1 X.Gm (mat (cpt X (x0F X) z) (ι t))
  have e : mat (cpt X (x0F X) z) (ι t) = mat (x0F X) (ι t) * uni (coords X ι z t) := rfl
  rw [sgnMat, ← h0, dmin, lminor, ← det_transpose, transpose_submatrix, h1, e, lminor]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end Data

end GlobalTheory.FlagFibre
