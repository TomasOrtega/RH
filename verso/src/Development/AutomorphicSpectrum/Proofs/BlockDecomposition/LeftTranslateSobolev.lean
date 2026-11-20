import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTranslateSobolev

variable {n : ℕ}

/- English proof (translation)
Establish `hc : Continuous (fun g : Mat n => g.det)` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne.preimage hc`.
-/
theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

/- English proof (translation)
Simplify using `only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *`. Conclude with `mul_ne_zero hx hy`.
-/
theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

/- English proof (translation)
Establish `h` using `(Matrix.isUnit_iff_isUnit_det _).1 x.isUnit`. Conclude with `h.ne_zero`.
-/
theorem val_mem (x : G n) : x.val ∈ GLs n := by
  have h := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact h.ne_zero

def mulL (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := fun y z => Matrix.mul_add a y z
      map_smul' := fun c y => Matrix.mul_smul a c y }

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mulL_apply (a y : Mat n) : mulL a y = a * y := rfl

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
The claim follows from `hf.comp (mulL x.val).contDiff.contDiffOn (fun _ hy => mul_mem (val_mem x) hy)`.
-/
theorem contDiffOn_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (lTr x f) (GLs n) :=
  hf.comp (mulL x.val).contDiff.contDiffOn (fun _ hy => mul_mem (val_mem x) hy)

/- English proof (translation)
Establish `hxg : x.val * g ∈ GLs n` using `mul_mem (val_mem x) hg`. Establish `hd : DifferentiableAt ℝ f (mulL x.val g)` using `(hf.contDiffAt ((isOpen_GLs n).mem_nhds hxg)).differentiableAt (by simp)`. Establish `hc : fderiv ℝ (f ∘ mulL x.val) g = (fderiv ℝ f (mulL x.val g)).comp (mulL x.val)` using `(hd.hasFDerivAt.comp g (mulL x.val).hasFDerivAt).fderiv`. Use `show fderiv ℝ (f ∘ mulL x.val) g (g * X) = fderiv ℝ f (x.val * g) (x.val * g * X)`. Rewrite using `[hc]`.

Simplify using `[Matrix.mul_assoc]`.
-/
theorem Rd_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n)
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (lTr x f) g = Rd X f (x.val * g) := by
  have hxg : x.val * g ∈ GLs n := mul_mem (val_mem x) hg
  have hd : DifferentiableAt ℝ f (mulL x.val g) :=
    (hf.contDiffAt ((isOpen_GLs n).mem_nhds hxg)).differentiableAt (by simp)
  have hc : fderiv ℝ (f ∘ mulL x.val) g = (fderiv ℝ f (mulL x.val g)).comp (mulL x.val) :=
    (hd.hasFDerivAt.comp g (mulL x.val).hasFDerivAt).fderiv
  show fderiv ℝ (f ∘ mulL x.val) g (g * X) = fderiv ℝ f (x.val * g) (x.val * g * X)
  rw [hc]
  simp [Matrix.mul_assoc]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons p w ih => exact ((hR n).1 V (Rw w f) ih).1 (bs p)`.
-/
theorem contDiffOn_Rw (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hR n).1 V (Rw w f) ih).1 (bs p)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro g _`. Both sides reduce to the same expression. Consider the case `cons p w ih`. Introduce `g hg`.

Establish `he : Rw w (lTr x f) =ᶠ[𝓝 g] lTr x (Rw w f)` using `Filter.eventuallyEq_of_mem ((isOpen_GLs n).mem_nhds hg) (fun y hy => ih y hy)`. Use `show Rd (bs p) (Rw w (lTr x f)) g = Rd (bs p) (Rw w f) (x.val * g)`. Rewrite using `[← Rd_lTr x (contDiffOn_Rw hR hf w) (bs p) hg]`. Use `show fderiv ℝ (Rw w (lTr x f)) g (g * bs p) = fderiv ℝ (lTr x (Rw w f)) g (g * bs p)`. Rewrite using `[he.fderiv_eq]`.
-/
theorem Rw_lTr (hR : RCalc) (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ∀ g ∈ GLs n, Rw w (lTr x f) g = Rw w f (x.val * g) := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have he : Rw w (lTr x f) =ᶠ[𝓝 g] lTr x (Rw w f) :=
      Filter.eventuallyEq_of_mem ((isOpen_GLs n).mem_nhds hg) (fun y hy => ih y hy)
    show Rd (bs p) (Rw w (lTr x f)) g = Rd (bs p) (Rw w f) (x.val * g)
    rw [← Rd_lTr x (contDiffOn_Rw hR hf w) (bs p) hg]
    show fderiv ℝ (Rw w (lTr x f)) g (g * bs p) = fderiv ℝ (lTr x (Rw w f)) g (g * bs p)
    rw [he.fderiv_eq]

end LeftTranslateSobolev

open LeftTranslateSobolev in

/- English proof (translation)
Introduce `n _ _ μ _ V _ _ _ _ hR x f hf`. Use `⟨⟨contDiffOn_lTr x hf.1, fun w => ?_⟩, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h` using `(hf.2 w).comp_measurePreserving (measurePreserving_mul_left μ x)`. Establish `he : (fun y : G n => Rw w (lTr x f) y.val) = (fun y : G n => Rw w f y.val) ∘ (fun y => x * y)`. Use function extensionality and compare the values at `fun y => Rw_lTr hR x hf.1 w y.val (val_mem y)`.

Rewrite using `[he]`. Conclude with `h`. Establish `ht : ∀ s, gel s 2 (lTr x f) g = gel s 2 f (x.val * g)` using `fun s => (((hR n).1 V f hf.1).2.2.2 s 2 x.val (val_mem x) g hg).1`. Simplify using `only [Om, Pi.smul_apply, Pi.add_apply, ht]`.
-/
theorem ltSob : LtSob := by
  intro n _ _ μ _ V _ _ _ _ hR x f hf
  refine ⟨⟨contDiffOn_lTr x hf.1, fun w => ?_⟩, fun g hg => ?_⟩
  · have h := (hf.2 w).comp_measurePreserving (measurePreserving_mul_left μ x)
    have he : (fun y : G n => Rw w (lTr x f) y.val) = (fun y : G n => Rw w f y.val) ∘ (fun y => x * y) :=
      funext fun y => Rw_lTr hR x hf.1 w y.val (val_mem y)
    rw [he]
    exact h
  · have ht : ∀ s, gel s 2 (lTr x f) g = gel s 2 f (x.val * g) := fun s =>
      (((hR n).1 V f hf.1).2.2.2 s 2 x.val (val_mem x) g hg).1
    simp only [Om, Pi.smul_apply, Pi.add_apply, ht]

end GlobalTheory.CompanionTheory.KerFc
