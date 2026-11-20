import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnitaryInvMeasure

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Torus (X : Data E r) : Type := X.Ψ → Fin r → Circle

instance (X : Data E r) : CommGroup (Torus X) := inferInstanceAs (CommGroup (X.Ψ → Fin r → Circle))
instance (X : Data E r) : TopologicalSpace (Torus X) :=
  inferInstanceAs (TopologicalSpace (X.Ψ → Fin r → Circle))
instance (X : Data E r) : IsTopologicalGroup (Torus X) :=
  inferInstanceAs (IsTopologicalGroup (X.Ψ → Fin r → Circle))
instance (X : Data E r) : CompactSpace (Torus X) :=
  inferInstanceAs (CompactSpace (X.Ψ → Fin r → Circle))
instance (X : Data E r) : T2Space (Torus X) := inferInstanceAs (T2Space (X.Ψ → Fin r → Circle))
instance (X : Data E r) : MeasurableSpace (Torus X) := borel _
instance (X : Data E r) : BorelSpace (Torus X) := ⟨rfl⟩

def haarT (X : Data E r) : Measure (Torus X) := Measure.haarMeasure ⊤

instance (X : Data E r) : (haarT X).IsMulLeftInvariant := by unfold haarT; infer_instance

instance (X : Data E r) : IsProbabilityMeasure (haarT X) :=
  ⟨by have := Measure.haarMeasure_self (G := Torus X) (K₀ := ⊤); simpa [haarT] using this⟩

def diagF (X : Data E r) (t : Torus X) : Frame X.Ψ r :=
  fun τ => Matrix.diagonal fun a => ((t τ a : Circle) : ℂ)

variable (X : Data E r)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Use `⟨?_, fun c hc => ?_⟩` and prove the remaining obligations. Simplify using `[_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_eq, Circle.norm_coe]`. Simplify using `[_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ (Ne.symm hc)]`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.diagF_unit (t : _root_.GlobalTheory.UnitaryInvMeasure.Torus X) (τ : X.Ψ)
    (a : Fin r) :
    ‖_root_.GlobalTheory.UnitaryInvMeasure.diagF X t τ a a‖ = 1 ∧
      ∀ c, c ≠ a → _root_.GlobalTheory.UnitaryInvMeasure.diagF X t τ a c = 0 := by
  refine ⟨?_, fun c hc => ?_⟩
  · simp [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_eq, Circle.norm_coe]
  · simp [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ (Ne.symm hc)]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Bor`. Introduce `τ`. Use `⟨?_, fun a c h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Matrix.diagonal fun a => ((t τ a : Circle) : ℂ)).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => Circle.coe_ne_zero _`. Simplify using `[_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ h.ne']`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.diagF_mem (t : _root_.GlobalTheory.UnitaryInvMeasure.Torus X) :
    _root_.GlobalTheory.UnitaryInvMeasure.diagF X t ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · change (Matrix.diagonal fun a => ((t τ a : Circle) : ℂ)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => Circle.coe_ne_zero _
  · simp [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ h.ne']

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_` and prove the remaining obligations. Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Simplify using `only [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_eq]`. Conclude with `continuous_subtype_val.comp ((continuous_apply a).comp (continuous_apply τ))`.

Simplify using `only [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ h]`. Conclude with `continuous_const`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.continuous_diagF : Continuous (_root_.GlobalTheory.UnitaryInvMeasure.diagF X) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  by_cases h : a = c
  · subst h
    simp only [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_eq]
    exact continuous_subtype_val.comp ((continuous_apply a).comp (continuous_apply τ))
  · simp only [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ h]
    exact continuous_const

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat`. Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Conclude with `Continuous.matrix_mul ((continuous_apply τ).comp continuous_fst) ((continuous_apply τ).comp continuous_snd)`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.continuous_rmul :
    Continuous fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 p.2 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  exact Continuous.matrix_mul
    ((continuous_apply τ).comp continuous_fst) ((continuous_apply τ).comp continuous_snd)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat`. Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_assoc (n τ) (Matrix.of (x τ)) (Matrix.of (b τ))).symm`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ)
    (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.lmulC n (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (X.lmulC n x) b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  funext τ
  exact (Matrix.mul_assoc (n τ) (Matrix.of (x τ)) (Matrix.of (b τ))).symm

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.gram`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply]`. Establish `key : ∀ c, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC n x) τ) c = (n τ).mulVec (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) c)`. Introduce `c`.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.col`. Use extensionality with `k`. Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.mat, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Both sides reduce to the same expression. Rewrite using `[key, key, hn τ]`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC n x) τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram
  ext a b
  simp only [Matrix.of_apply]
  have key : ∀ c, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC n x) τ) c = (n τ).mulVec (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) c) := by
    intro c
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.col
    ext k
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rfl
  rw [key, key, hn τ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at *`. Introduce `τ`. Rewrite using `[_root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC X hn]`. Conclude with `hx τ`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.orth_lmulC {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (X.lmulC n x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at *
  intro τ
  rw [_root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC X hn]
  exact hx τ

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF`. Use `infer_instance`.
-/
private theorem sFinite_muF (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : SFinite (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF; infer_instance

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
The claim follows from `continuous_apply τ`.
-/
private theorem continuous_frame_mat (τ : X.Ψ) : Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ :=
  continuous_apply τ

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor`. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq]`. Establish `h` using `continuous_frame_mat X τ`. Use `Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)` and prove the remaining obligations. Conclude with `(h.matrix_transpose.matrix_mul continuous_const).matrix_mul (h.matrix_map continuous_star)`.
-/
private theorem continuous_dmin_torus_haar_measure (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq]
  have h := continuous_frame_mat X τ
  refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
  exact (h.matrix_transpose.matrix_mul continuous_const).matrix_mul
    (h.matrix_map continuous_star)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG`. Simplify using `only [Set.setOf_forall, Set.setOf_and]`. Use `isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations. Conclude with `isOpen_ne_fun (continuous_frame_mat X τ).matrix_det continuous_const`. Conclude with `isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin_torus_haar_measure X τ i)))`.
-/
private theorem isOpen_X_dom : IsOpen X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (continuous_frame_mat X τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin_torus_haar_measure X τ i)))

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_` and prove the remaining obligations. Establish `: ∀ z, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z τ a c = ∑ k, x0 τ a k * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.nM X z τ k c`. Introduce `z`. Establish `h` using `congrFun (congrFun (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mat_cpt X x0 z τ) a) c`. Conclude with `h`.

Repeatedly rewrite using `[this]`. Use `continuous_finset_sum _ fun k _ => continuous_const.mul ?_` and prove the remaining obligations. Conclude with `(_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.cd_nM X τ k c).continuous`.
-/
private theorem continuous_cpt_torus_haar_measure (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : Continuous (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  have : ∀ z, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z τ a c = ∑ k, x0 τ a k * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.nM X z τ k c := by
    intro z
    have h := congrFun (congrFun (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mat_cpt X x0 z τ) a) c
    exact h
  simp_rw [this]
  refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
  exact (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.cd_nM X τ k c).continuous

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Establish `h` using `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF X b`. Use function extensionality and compare the values at `τ`. Establish `h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF X) τ = 1`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _root_.ReciprocityTheory.ChartRestriction.G.FD.mat`. Both sides reduce to the same expression.

Use `show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF X) τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ = b τ`. Rewrite using `[h1, Matrix.one_mul]`. Both sides reduce to the same expression.
-/
private theorem oneF_rmul (b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF X) b = b := by
  have h := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF X b
  funext τ
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF X) τ = 1 := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    rfl
  show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF X) τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ = b τ
  rw [h1, Matrix.one_mul]
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Use `⟨fun τ a => ⟨b τ a a, mem_sphere_zero_iff_norm.mpr (hb τ a).1⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ a c`. Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Simplify using `[_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_eq]`.

Simplify using `[_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ h, (hb τ a).2 c (Ne.symm h)]`.
-/
private theorem exists_diagF_eq_of_unit_diagonal (b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hb : ∀ τ a, ‖b τ a a‖ = 1 ∧ ∀ c, c ≠ a → b τ a c = 0) :
    ∃ t : _root_.GlobalTheory.UnitaryInvMeasure.Torus X, _root_.GlobalTheory.UnitaryInvMeasure.diagF X t = b := by
  refine ⟨fun τ a => ⟨b τ a a, mem_sphere_zero_iff_norm.mpr (hb τ a).1⟩, ?_⟩
  funext τ a c
  by_cases h : a = c
  · subst h
    simp [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_eq]
  · simp [_root_.GlobalTheory.UnitaryInvMeasure.diagF, Matrix.diagonal_apply_ne _ h, (hb τ a).2 c (Ne.symm h)]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Both sides reduce to the same expression.
-/
private theorem rmul_diagF_diagF (s t : _root_.GlobalTheory.UnitaryInvMeasure.Torus X) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.GlobalTheory.UnitaryInvMeasure.diagF X s) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t) =
      _root_.GlobalTheory.UnitaryInvMeasure.diagF X (s * t) := by
  funext τ
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Repeatedly rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X, rmul_diagF_diagF]`. Conclude with `lintegral_mul_left_eq_self (fun t => f (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t))) s`.
-/
private theorem lintegral_haarT_rmul_diagF_translate (f : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ≥0∞) (y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (s : _root_.GlobalTheory.UnitaryInvMeasure.Torus X) :
    ∫⁻ t, f (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (_root_.GlobalTheory.UnitaryInvMeasure.diagF X s)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t))
      ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X =
    ∫⁻ t, f (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t)) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X := by
  simp_rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X, rmul_diagF_diagF]
  exact lintegral_mul_left_eq_self
    (fun t => f (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t))) s

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mat_lmulC (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC n x) τ = n τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG`. Simplify using `only [Set.mem_setOf_eq]`. Establish `hp : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.lmulC n x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i`. Introduce `τ i`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin`.

Rewrite using `[_root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC X hn]`. Simplify using `only [hp, mat_lmulC, Matrix.det_mul, mul_ne_zero_iff, hdet, ne_eq, not_false_eq_true, true_and]`.
-/
private theorem lmulC_mem_dom_iff_of_unitary {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n)
    (hdet : ∀ τ, (n τ).det ≠ 0) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.lmulC n x ∈ X.dom ↔ x ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  simp only [Set.mem_setOf_eq]
  have hp : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.lmulC n x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
    intro τ i
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
    rw [_root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC X hn]
  simp only [hp, mat_lmulC, Matrix.det_mul, mul_ne_zero_iff, hdet, ne_eq, not_false_eq_true, true_and]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC _root_.ReciprocityTheory.ChartRestriction.G.FD.mat`. Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_assoc (n τ) (m τ) (Matrix.of (x τ))).symm`.
-/
private theorem lmulC_lmulC (n m : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.lmulC n (X.lmulC m x) = X.lmulC (fun τ => n τ * m τ) x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  funext τ
  exact (Matrix.mul_assoc (n τ) (m τ) (Matrix.of (x τ))).symm

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `h1` using `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mat_cpt X (X.lmulC n x0) z τ`. Establish `h2` using `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mat_cpt X x0 z τ`. Express the relevant statement in the definitionally equal form `_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (X.lmulC n x0) z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC n (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) τ`. Rewrite using `[h1, mat_lmulC, mat_lmulC, h2, Matrix.mul_assoc]`.
-/
private theorem cpt_lmulC_eq_lmulC_cpt (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) z :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (X.lmulC n x0) z = X.lmulC n (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) := by
  funext τ
  have h1 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mat_cpt X (X.lmulC n x0) z τ
  have h2 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mat_cpt X x0 z τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (X.lmulC n x0) z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC n (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) τ
  rw [h1, mat_lmulC, mat_lmulC, h2, Matrix.mul_assoc]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Establish `hp : ∀ x τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.lmulC n x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i`. Introduce `x τ i`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin`. Rewrite using `[_root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC X hn]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF`.

Simplify using `only [cpt_lmulC_eq_lmulC_cpt, lmulC_mem_dom_iff_of_unitary X hn hdet, hp]`.
-/
private theorem muF_lmulC_eq_of_unitary {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n)
    (hdet : ∀ τ, (n τ).det ≠ 0) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X (X.lmulC n x0) = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 := by
  have hp : ∀ x τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.lmulC n x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
    intro x τ i
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
    rw [_root_.GlobalTheory.UnitaryInvMeasure.gram_lmulC X hn]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
  simp only [cpt_lmulC_eq_lmulC_cpt, lmulC_mem_dom_iff_of_unitary X hn hdet, hp]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
/- English proof (translation)
Introduce `hInv hβ hCrit hFin hH r X H hHiff _ _ x0 hx0`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.MeasInvStatement at hInv`. Take `⟨β, hβc, hβm⟩` from `hβ r X`. Take `⟨_, _, hHx⟩` from `hH r X H hHiff`. Take `⟨horb, ι, hιc, hιx, hιg⟩` from `hHx x0 hx0`.

Use `haveI : SecondCountableTopology (_root_.GlobalTheory.UnitaryInvMeasure.Torus X) := inferInstanceAs (SecondCountableTopology (X.Ψ → Fin r → Circle))`. Use `haveI := sFinite_muF X x0`. Establish `hu : ∀ g : H, X.IsUnitaryC fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)` using `fun g => (hHiff g).1 g.2`. Establish `hdet : ∀ (g : H) τ, (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)).det ≠ 0` using `fun g τ => ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero`. Establish `hOrthN : ∀ x ∈ X.dom, ∀ t, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t))` using `fun x hx t => (hCrit r X _ _ (hβm x hx).2 (_root_.GlobalTheory.UnitaryInvMeasure.diagF_mem X t)).2 (fun τ a => _root_.GlobalTheory.UnitaryInvMeasure.diagF_unit X t τ a)`.

Set `S : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X)` to `X.dom ×ˢ Set.univ`. Set `P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X → H` to `S.piecewise (fun p => ι (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X p.2))) (fun _ => 1)`. Establish `hPm : Measurable P`. Use `ContinuousOn.measurable_piecewise ?_ continuousOn_const ((isOpen_X_dom X).measurableSet.prod MeasurableSet.univ)` and prove the remaining obligations. Establish `h3 : ContinuousOn (fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1)) S` using `(_root_.GlobalTheory.UnitaryInvMeasure.continuous_rmul X).comp_continuousOn (f := fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X => (p.1, β p.1)) (continuousOn_fst.prodMk (hβc.comp continuousOn_fst fun p hp => hp …`.

Establish `h2 : ContinuousOn (fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1)) (_root_.GlobalTheory.Unit …` using `(_root_.GlobalTheory.UnitaryInvMeasure.continuous_rmul X).comp_continuousOn (f := fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X => (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1), _root_.GlobalT …`. Conclude with `hιc.comp h2 fun p hp => hOrthN p.1 hp.1 p.2`. Establish `hPeq : ∀ x ∈ X.dom, ∀ t, P (x, t) = ι (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t))` using `fun x hx t => Set.piecewise_eq_of_mem _ _ _ (Set.mk_mem_prod hx (Set.mem_univ t))`. Set `F : (H → ℝ≥0∞) → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ≥0∞` to `fun f x => ∫⁻ t, f (P (x, t)) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X`. Establish `hFm : ∀ f : H → ℝ≥0∞, Measurable f → Measurable (F f)` using `fun f hf => (hf.comp hPm).lintegral_prod_right'`.

Establish `hQm : Measurable fun p : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) × _root_.GlobalTheory.UnitaryInvMeasure.Torus X => P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 p.1, p.2)` using `hPm.comp (((continuous_cpt_torus_haar_measure X x0).measurable.comp measurable_fst).prodMk measurable_snd)`. Set `ν : Measure H` to `((_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0).prod (_root_.GlobalTheory.UnitaryInvMeasure.haarT X)).map fun p => P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 p.1, p.2)`. Establish `hK : ∀ f : H → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂ν = ∫⁻ z, F f (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0`. Introduce `f hf`. Rewrite using `[lintegral_map hf hQm]`.

Conclude with `lintegral_prod (fun p => f (P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 p.1, p.2))) (hf.comp hQm).aemeasurable`. Establish `hOm : MeasurableSet (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)` using `((isOpen_X_dom X).preimage (continuous_cpt_torus_haar_measure X x0)).measurableSet`. Establish `hae : ∀ᵐ z ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom`. Establish `h1 : ∀ᵐ z ∂(volume.restrict (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)), z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0` using `ae_restrict_mem hOm`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF`.

Conclude with `(withDensity_absolutelyContinuous _ _).ae_le h1`. Establish `hI : ∀ f : H → ℝ≥0∞, ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) → ∫⁻ t, f (ι (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul …`. Introduce `f x hx b hb hxb`. Establish `hy` using `(hβm x hx).2`. Establish `hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (β x)) b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r` using `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X (hβm x hx).1) hb`.

Establish `heq : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (β x)) b) = _root_.ReciprocityTheory.Chart …`. Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X, ← _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X (β x), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_invF X (hβm x hx).1, oneF_rmul]`. Take `⟨s, hs⟩` from `exists_diagF_eq_of_unit_diagonal X _ ((hCrit r X _ _ hy hc).1 (heq ▸ hxb))`. Rewrite using `[← heq, ← hs, lintegral_haarT_rmul_diagF_translate X (fun w => f (ι w))]`. Conclude with `lintegral_congr fun t => by rw [hPeq x hx t]`.

Establish `hE : ∀ f : H → ℝ≥0∞, ∀ g : H, ∀ x ∈ X.dom, F (fun h => f (g * h)) x = F f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x)`. Introduce `f g x hx`. Establish `hgx` using `(lmulC_mem_dom_iff_of_unitary X (hu g) (hdet g) x).2 hx`. Establish `hw : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) (β x))`. Rewrite using `[← _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul]`.

Conclude with `_root_.GlobalTheory.UnitaryInvMeasure.orth_lmulC X (hu g) (hβm x hx).2`. Rewrite using `[← hI f _ hgx _ (hβm x hx).1 hw]`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Use `show f (g * P (x, t)) = _`. Rewrite using `[hPeq x hx t]`.

Use `congr 1`. Establish `hwo` using `hOrthN x hx t`. Rewrite using `[← _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul, ← _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul]`. Use `conv_rhs => rw [← hιx _ hwo]`. Rewrite using `[lmulC_lmulC]`.

Conclude with `(hιg (g * ι _)).symm`. Establish `hFinv : ∀ f : H → ℝ≥0∞, Measurable f → ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, F f (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = F f x`. Introduce `f hf x hx b hb`. Establish `hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ X.dom` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb`. Establish `hb' : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul b (β (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r` using `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X hb (hβm _ hx').1`.

Establish `ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul b (β (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b))))`. Rewrite using `[← _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X]`. Conclude with `(hβm _ hx').2`. Rewrite using `[← hI f x hx _ hb' ho]`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations.

Use `show f (P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b, t)) = _`. Rewrite using `[hPeq _ hx' t, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X x b]`. Establish `hactc : Continuous fun g : H => X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC`. Use `continuous_pi fun τ => ?_` and prove the remaining obligations.

Conclude with `(Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul continuous_const`. Establish `hinvF : ∀ f : H → ℝ≥0∞, Measurable f → ∀ g : H, ∫⁻ h, f (g * h) ∂ν = ∫⁻ h, f h ∂ν`. Introduce `f hf g`. Rewrite using `[hK (fun h => f (g * h)) (hf.comp (measurable_const_mul g)), hK f hf]`. Establish `hx0'` using `horb g`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[muF_lmulC_eq_of_unitary X (hu g) (hdet g)]`. Use `_ = ∫⁻ z, F f (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 := hInv r X _ x0 hx0' hx0 (F f) (hFm f hf) (hFinv f hf)`. Use `⟨ν, ⟨fun g => ?_⟩, ⟨fun K hKc => ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `A hA`.

Rewrite using `[Measure.map_apply (measurable_const_mul g) hA, ← lintegral_indicator_one hA, ← lintegral_indicator_one (measurable_const_mul g hA), ← hinvF (A.indicator 1) (measurable_one.indicator hA) g]`. Both sides reduce to the same expression. Establish `hKm : MeasurableSet K` using `hKc.measurableSet`. Establish `hC : IsCompact ((fun g : H => X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) '' K)` using `hKc.image hactc`. Establish `hCd : (fun g : H => X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) '' K ⊆ X.dom`.

Introduce and unpack `_ ⟨g, -, rfl⟩`. Conclude with `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IC.orth_mem_dom X (horb g)`. Establish `hfin` using `hFin r X x0 hx0 _ hC hCd`. Rewrite using `[← lintegral_indicator_one hKm, hK (K.indicator 1) (measurable_one.indicator hKm)]`. Use `lt_of_le_of_lt ?_ hfin` and prove the remaining obligations.

Use `le_trans (lintegral_mono_ae (hae.mono fun z hz => ?_)) (lintegral_indicator_one_le _)` and prove the remaining obligations. Distinguish the cases in `hs : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.sat X x0 ((fun g : H => X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) '' K)`. Rewrite using `[Set.indicator_of_mem hs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.indicator_of_notMem hs]`.

Establish `h0 : ∀ t, K.indicator 1 (P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t)) = (0 : ℝ≥0∞)`. Introduce `t`. Use `Set.indicator_of_notMem (fun hPK => hs ?_) _` and prove the remaining obligations. Rewrite `hPK` using `[hPeq _ hz t]`. Establish `hwo` using `hOrthN _ hz t`.

Establish `hbt` using `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X (hβm _ hz).1 (_root_.GlobalTheory.UnitaryInvMeasure.diagF_mem X t)`. Use `⟨hz, _, ⟨_, hPK, hιx _ hwo⟩, _, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hbt, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z), _root_. …`. Use `show ∫⁻ t, K.indicator 1 (P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t)) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X ≤ 0`. Simplify using `only [h0, lintegral_zero, le_refl]`.

Introduce `φ hφ hφinv`. Rewrite using `[hK (fun g : H => φ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) (hφ.comp hactc.measurable)]`. Use `lintegral_congr_ae (hae.mono fun z hz => ?_)` and prove the remaining obligations. Establish `h1 : ∀ t, φ (X.lmulC (fun τ => ((P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = φ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)` using `fun t => by`. Rewrite using `[hPeq _ hz t, hιx _ (hOrthN _ hz t), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X, hφinv _ hz _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X (hβm _ hz).1 (_root_.GlobalTheory.UnitaryInvMeasure.diagF_mem X t))]`.

Use `show ∫⁻ t, φ (X.lmulC (fun τ => ((P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X = _`. Simplify using `only [h1, lintegral_const, measure_univ, mul_one]`.
-/
theorem _root_.GlobalTheory.UnitaryInvMeasure.invMeas :
    (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.MeasInvStatement (E := E)) →
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ β : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      ContinuousOn β X.dom ∧ ∀ x ∈ X.dom, β x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x))) →
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r →
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ↔ ∀ τ a, ‖b τ a a‖ = 1 ∧ ∀ c, c ≠ a → b τ a c = 0)) →
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 →
      ∀ C : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), IsCompact C → C ⊆ X.dom → _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.sat X x0 C) < ⊤) →
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 →
        (∀ g : H, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X
          (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧
        ∃ ι : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → H, ContinuousOn ι {x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x} ∧
          (∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
            X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧
          ∀ g : H, ι (X.lmulC
            (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g) →
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      ∀ [MeasurableSpace H] [BorelSpace H] (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 →
        ∃ ν : Measure H, ν.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts ν ∧
          ∀ φ : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ≥0∞, Measurable φ →
            (∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, φ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = φ x) →
            ∫⁻ g, φ (X.lmulC
              (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) ∂ν =
            ∫⁻ z, φ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) := by
  classical
  intro hInv hβ hCrit hFin hH r X H hHiff _ _ x0 hx0
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.MeasInvStatement at hInv
  obtain ⟨β, hβc, hβm⟩ := hβ r X
  obtain ⟨_, _, hHx⟩ := hH r X H hHiff
  obtain ⟨horb, ι, hιc, hιx, hιg⟩ := hHx x0 hx0
  haveI : SecondCountableTopology (_root_.GlobalTheory.UnitaryInvMeasure.Torus X) :=
    inferInstanceAs (SecondCountableTopology (X.Ψ → Fin r → Circle))
  haveI := sFinite_muF X x0
  have hu : ∀ g : H, X.IsUnitaryC fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) :=
    fun g => (hHiff g).1 g.2
  have hdet : ∀ (g : H) τ, (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)).det ≠ 0 :=
    fun g τ => ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  have hOrthN : ∀ x ∈ X.dom, ∀ t, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t)) := fun x hx t =>
    (hCrit r X _ _ (hβm x hx).2 (_root_.GlobalTheory.UnitaryInvMeasure.diagF_mem X t)).2
      (fun τ a => _root_.GlobalTheory.UnitaryInvMeasure.diagF_unit X t τ a)
  let S : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X) := X.dom ×ˢ Set.univ
  let P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X → H := S.piecewise
    (fun p => ι (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X p.2))) (fun _ => 1)
  have hPm : Measurable P := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
      ((isOpen_X_dom X).measurableSet.prod MeasurableSet.univ)
    have h3 : ContinuousOn (fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X =>
        _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1)) S :=
      (_root_.GlobalTheory.UnitaryInvMeasure.continuous_rmul X).comp_continuousOn
        (f := fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X => (p.1, β p.1))
        (continuousOn_fst.prodMk (hβc.comp continuousOn_fst fun p hp => hp.1))
    have h2 : ContinuousOn (fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X =>
        _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X p.2)) S :=
      (_root_.GlobalTheory.UnitaryInvMeasure.continuous_rmul X).comp_continuousOn
        (f := fun p : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.GlobalTheory.UnitaryInvMeasure.Torus X =>
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul p.1 (β p.1), _root_.GlobalTheory.UnitaryInvMeasure.diagF X p.2))
        (h3.prodMk ((_root_.GlobalTheory.UnitaryInvMeasure.continuous_diagF X).comp continuous_snd).continuousOn)
    exact hιc.comp h2 fun p hp => hOrthN p.1 hp.1 p.2
  have hPeq : ∀ x ∈ X.dom, ∀ t, P (x, t) =
      ι (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t)) := fun x hx t =>
    Set.piecewise_eq_of_mem _ _ _ (Set.mk_mem_prod hx (Set.mem_univ t))
  let F : (H → ℝ≥0∞) → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ≥0∞ := fun f x =>
    ∫⁻ t, f (P (x, t)) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X
  have hFm : ∀ f : H → ℝ≥0∞, Measurable f → Measurable (F f) := fun f hf =>
    (hf.comp hPm).lintegral_prod_right'
  have hQm : Measurable fun p : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) × _root_.GlobalTheory.UnitaryInvMeasure.Torus X =>
      P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 p.1, p.2) :=
    hPm.comp (((continuous_cpt_torus_haar_measure X x0).measurable.comp measurable_fst).prodMk measurable_snd)
  let ν : Measure H := ((_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0).prod (_root_.GlobalTheory.UnitaryInvMeasure.haarT X)).map
    fun p => P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 p.1, p.2)
  have hK : ∀ f : H → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂ν = ∫⁻ z, F f (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 := by
    intro f hf
    rw [lintegral_map hf hQm]
    exact lintegral_prod (fun p => f (P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 p.1, p.2))) (hf.comp hQm).aemeasurable
  have hOm : MeasurableSet (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0) := ((isOpen_X_dom X).preimage (continuous_cpt_torus_haar_measure X x0)).measurableSet
  have hae : ∀ᵐ z ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := by
    have h1 : ∀ᵐ z ∂(volume.restrict (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)), z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 := ae_restrict_mem hOm
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF
    exact (withDensity_absolutelyContinuous _ _).ae_le h1

  have hI : ∀ f : H → ℝ≥0∞, ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) →
      ∫⁻ t, f (ι (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (_root_.GlobalTheory.UnitaryInvMeasure.diagF X t)))
        ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X = F f x := by
    intro f x hx b hb hxb
    have hy := (hβm x hx).2
    have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (β x)) b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r :=
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X (hβm x hx).1) hb
    have heq : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (β x)) b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X, ← _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X (β x), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_invF X (hβm x hx).1, oneF_rmul]
    obtain ⟨s, hs⟩ := exists_diagF_eq_of_unit_diagonal X _ ((hCrit r X _ _ hy hc).1 (heq ▸ hxb))
    rw [← heq, ← hs, lintegral_haarT_rmul_diagF_translate X (fun w => f (ι w))]
    exact lintegral_congr fun t => by rw [hPeq x hx t]
  have hE : ∀ f : H → ℝ≥0∞, ∀ g : H, ∀ x ∈ X.dom,
      F (fun h => f (g * h)) x = F f (X.lmulC
        (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) := by
    intro f g x hx
    have hgx := (lmulC_mem_dom_iff_of_unitary X (hu g) (hdet g) x).2 hx
    have hw : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (X.lmulC
        (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) (β x)) := by
      rw [← _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul]
      exact _root_.GlobalTheory.UnitaryInvMeasure.orth_lmulC X (hu g) (hβm x hx).2
    rw [← hI f _ hgx _ (hβm x hx).1 hw]
    refine lintegral_congr fun t => ?_
    show f (g * P (x, t)) = _
    rw [hPeq x hx t]
    congr 1
    have hwo := hOrthN x hx t
    rw [← _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul, ← _root_.GlobalTheory.UnitaryInvMeasure.lmulC_rmul]
    conv_rhs => rw [← hιx _ hwo]
    rw [lmulC_lmulC]
    exact (hιg (g * ι _)).symm
  have hFinv : ∀ f : H → ℝ≥0∞, Measurable f → ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r,
      F f (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = F f x := by
    intro f hf x hx b hb
    have hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ X.dom := _root_.ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
    have hb' : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul b (β (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X hb (hβm _ hx').1
    have ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul b (β (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)))) := by
      rw [← _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X]; exact (hβm _ hx').2
    rw [← hI f x hx _ hb' ho]
    refine lintegral_congr fun t => ?_
    show f (P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b, t)) = _
    rw [hPeq _ hx' t, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X x b]
  have hactc : Continuous fun g : H => X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC
    refine continuous_pi fun τ => ?_
    exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
      continuous_const
  have hinvF : ∀ f : H → ℝ≥0∞, Measurable f → ∀ g : H,
      ∫⁻ h, f (g * h) ∂ν = ∫⁻ h, f h ∂ν := by
    intro f hf g
    rw [hK (fun h => f (g * h)) (hf.comp (measurable_const_mul g)), hK f hf]
    have hx0' := horb g
    calc ∫⁻ z, F (fun h => f (g * h)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0
        = ∫⁻ z, F f (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (X.lmulC
            (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) z)
            ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 :=
          lintegral_congr_ae (hae.mono fun z hz => by beta_reduce; rw [hE f g _ hz, cpt_lmulC_eq_lmulC_cpt])
      _ = ∫⁻ z, F f (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (X.lmulC
            (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) z)
            ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X (X.lmulC
            (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
          rw [muF_lmulC_eq_of_unitary X (hu g) (hdet g)]
      _ = ∫⁻ z, F f (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 :=
          hInv r X _ x0 hx0' hx0 (F f) (hFm f hf) (hFinv f hf)
  refine ⟨ν, ⟨fun g => ?_⟩, ⟨fun K hKc => ?_⟩, ?_⟩
  · ext A hA
    rw [Measure.map_apply (measurable_const_mul g) hA, ← lintegral_indicator_one hA,
      ← lintegral_indicator_one (measurable_const_mul g hA),
      ← hinvF (A.indicator 1) (measurable_one.indicator hA) g]
    rfl
  · have hKm : MeasurableSet K := hKc.measurableSet
    have hC : IsCompact ((fun g : H => X.lmulC
        (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) '' K) :=
      hKc.image hactc
    have hCd : (fun g : H => X.lmulC
        (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) '' K ⊆ X.dom := by
      rintro _ ⟨g, -, rfl⟩
      exact _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IC.orth_mem_dom X (horb g)
    have hfin := hFin r X x0 hx0 _ hC hCd
    rw [← lintegral_indicator_one hKm, hK (K.indicator 1) (measurable_one.indicator hKm)]
    refine lt_of_le_of_lt ?_ hfin
    refine le_trans (lintegral_mono_ae (hae.mono fun z hz => ?_)) (lintegral_indicator_one_le _)
    by_cases hs : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.sat X x0 ((fun g : H => X.lmulC
        (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) '' K)
    · rw [Set.indicator_of_mem hs]
      calc F (K.indicator 1) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ≤ ∫⁻ _t, 1 ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X :=
            lintegral_mono fun t => by unfold Set.indicator; split_ifs <;> simp
        _ = 1 := by simp
    · rw [Set.indicator_of_notMem hs]
      have h0 : ∀ t, K.indicator 1 (P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t)) = (0 : ℝ≥0∞) := by
        intro t
        refine Set.indicator_of_notMem (fun hPK => hs ?_) _
        rw [hPeq _ hz t] at hPK
        have hwo := hOrthN _ hz t
        have hbt := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X (hβm _ hz).1 (_root_.GlobalTheory.UnitaryInvMeasure.diagF_mem X t)
        refine ⟨hz, _, ⟨_, hPK, hιx _ hwo⟩, _, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hbt, ?_⟩
        rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_invF X hbt, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF]
      show ∫⁻ t, K.indicator 1 (P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t)) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X ≤ 0
      simp only [h0, lintegral_zero, le_refl]
  · intro φ hφ hφinv
    rw [hK (fun g : H => φ (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) (hφ.comp hactc.measurable)]
    refine lintegral_congr_ae (hae.mono fun z hz => ?_)
    have h1 : ∀ t, φ (X.lmulC (fun τ => ((P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t) : X.Ψ → GL (Fin r) ℂ) τ :
        Matrix (Fin r) (Fin r) ℂ)) x0) = φ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) := fun t => by
      rw [hPeq _ hz t, hιx _ (hOrthN _ hz t), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc X,
        hφinv _ hz _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem X (hβm _ hz).1 (_root_.GlobalTheory.UnitaryInvMeasure.diagF_mem X t))]
    show ∫⁻ t, φ (X.lmulC (fun τ => ((P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z, t) : X.Ψ → GL (Fin r) ℂ) τ :
        Matrix (Fin r) (Fin r) ℂ)) x0) ∂_root_.GlobalTheory.UnitaryInvMeasure.haarT X = _
    simp only [h1, lintegral_const, measure_univ, mul_one]

end

end GlobalTheory.UnitaryInvMeasure
