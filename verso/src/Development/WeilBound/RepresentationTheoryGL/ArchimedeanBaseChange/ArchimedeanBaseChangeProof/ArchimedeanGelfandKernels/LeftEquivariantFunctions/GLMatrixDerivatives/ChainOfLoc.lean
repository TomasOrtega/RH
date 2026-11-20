import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfEq

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Loc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
The claim follows from `isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const`.
-/
theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

/- English proof (translation)
Introduce `x hx`. Simplify using `only [Rd]`. Rewrite using `[Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]`.
-/
theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (X : Mat n) :
    Set.EqOn (Rd X f) (Rd X f') U := by
  intro x hx
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

/- English proof (translation)
Introduce `x hx`. Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply]`. Rewrite using `[rd_congr hU h _ hx, rd_congr hU h _ hx]`.
-/
theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b f) (Eu s a b f') U := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h _ hx, rd_congr hU h _ hx]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b f f' h x hx`. Simplify using `only [Epow]`. Use `split_ifs`.

Conclude with `h hx`. Both sides reduce to the same expression. Consider the case `succ m ih`. Introduce `a b f f' h x hx`. Simplify using `only [Epow, Finset.sum_apply]`.

Conclude with `Finset.sum_congr rfl fun c _ => eu_congr hU (ih c b h) s a c hx`.
-/
theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (Epow s m a b f) (Epow s m a b f') U := by
  induction m with
  | zero =>
    intro a b f f' h x hx
    simp only [Epow]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro a b f f' h x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (ih c b h) s a c hx

/- English proof (translation)
Introduce `x hx`. Simplify using `only [gel, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => epow_congr hU s m a a h hx`.
-/
theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m f) (gel s m f') U := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU s m a a h hx

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => intro f f' h`. Conclude with `h`. Consider the case `cons p w ih => intro f f' h`.

Conclude with `gel_congr hU (ih h) p.1 p.2`.
-/
theorem zop_congr {U : Set (Mat n)} (hU : IsOpen U) : ∀ (w : List (Bool × ℕ)) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (zOp w f) (zOp w f') U := by
  intro w
  induction w with
  | nil => intro f f' h; exact h
  | cons p w ih => intro f f' h; exact gel_congr hU (ih h) p.1 p.2

/- English proof (translation)
Take `⟨R, hR⟩` from `hc`. Establish `hcont : Continuous fun y : G n => F y.val`. Use `hF.comp_continuous (Units.continuous_val) fun y => ?_` and prove the remaining obligations. Use `show (y.val).det ≠ 0`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero`.

Establish `hlg : ContinuousOn (lg (n` using `n)) (GLs n) := (hL n).2.2.2.1.continuousOn`. Establish `hK : IsCompact {y : G n | lg y.val ≤ R}` using `(hL n).2.2.2.2.1 R`. Establish `hclosed : IsClosed {y : G n | lg y.val ≤ R}`. Establish `: Continuous fun y : G n => lg y.val` using `hlg.comp_continuous Units.continuous_val fun y => (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero`. Conclude with `isClosed_le this continuous_const`.

Use `hcont.integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Use `HasCompactSupport.intro hK ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Set.mem_setOf_eq, not_le] at hy`. Conclude with `hR _ ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero) hy`.
-/
theorem integrable_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (hF : ContinuousOn F (GLs n))
    (hc : Cpt F) : Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val := by
    refine hF.comp_continuous (Units.continuous_val) fun y => ?_
    show (y.val).det ≠ 0
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
  have hlg : ContinuousOn (lg (n := n)) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hclosed : IsClosed {y : G n | lg y.val ≤ R} := by
    have : Continuous fun y : G n => lg y.val :=
      hlg.comp_continuous Units.continuous_val fun y => (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
    exact isClosed_le this continuous_const
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hK ?_
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  exact hR _ ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero) hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Loc
