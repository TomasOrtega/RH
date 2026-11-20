import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Eq

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `show fderiv ℝ (fun x => A (f x)) g (g * X) = A (fderiv ℝ f g (g * X))`. Distinguish the cases in `hf : DifferentiableAt ℝ f g`. Establish `h : HasFDerivAt (fun x => A (f x)) ((A.restrictScalars ℝ : V →L[ℝ] V).comp (fderiv ℝ f g)) g` using `(A.restrictScalars ℝ : V →L[ℝ] V).hasFDerivAt.comp g hf.hasFDerivAt`. Rewrite using `[h.fderiv]`.

Both sides reduce to the same expression. Establish `hn : ¬ DifferentiableAt ℝ (fun x => A (f x)) g`. Introduce `h`. Apply `hf` to reduce the goal to its premises. Establish `h2 : DifferentiableAt ℝ (fun x => A.symm (A (f x))) g` using `(A.symm.restrictScalars ℝ : V →L[ℝ] V).differentiableAt.comp g h`.

Simplify using `using h2`. Rewrite using `[fderiv_zero_of_not_differentiableAt hn, fderiv_zero_of_not_differentiableAt hf]`. Simplify using the standard rewrite rules.
-/
theorem rd_equiv (A : V ≃L[ℂ] V) (X : Mat n) (f : Mat n → V) : Rd X (fun x => A (f x)) = fun x => A (Rd X f x) := by
  funext g
  show fderiv ℝ (fun x => A (f x)) g (g * X) = A (fderiv ℝ f g (g * X))
  by_cases hf : DifferentiableAt ℝ f g
  · have h : HasFDerivAt (fun x => A (f x)) ((A.restrictScalars ℝ : V →L[ℝ] V).comp (fderiv ℝ f g)) g :=
      (A.restrictScalars ℝ : V →L[ℝ] V).hasFDerivAt.comp g hf.hasFDerivAt
    rw [h.fderiv]
    rfl
  · have hn : ¬ DifferentiableAt ℝ (fun x => A (f x)) g := by
      intro h
      apply hf
      have h2 : DifferentiableAt ℝ (fun x => A.symm (A (f x))) g :=
        (A.symm.restrictScalars ℝ : V →L[ℝ] V).differentiableAt.comp g h
      simpa using h2
    rw [fderiv_zero_of_not_differentiableAt hn, fderiv_zero_of_not_differentiableAt hf]
    simp

/- English proof (translation)
Unfold `Eu`. Rewrite using `[rd_equiv, rd_equiv]`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases hs : s = true <;> simp [hs, map_add, map_smul]`.
-/
theorem eu_equiv (A : V ≃L[ℂ] V) (s : Bool) (a b : Fin n) (f : Mat n → V) :
    Eu s a b (fun x => A (f x)) = fun x => A (Eu s a b f x) := by
  unfold Eu
  rw [rd_equiv, rd_equiv]
  funext x
  by_cases hs : s = true <;> simp [hs, map_add, map_smul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b f`. Rewrite using `[Epow.eq_1]`. Use function extensionality and compare the values at `x`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `succ m ih`. Introduce `a b f`. Rewrite using `[Epow.eq_2]`. Simplify using `only [ih, eu_equiv]`.

Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply, map_sum]`.
-/
theorem epow_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) (f : Mat n → V),
    Epow s m a b (fun x => A (f x)) = fun x => A (Epow s m a b f x) := by
  induction m with
  | zero =>
    intro a b f
    rw [Epow.eq_1]
    funext x
    split_ifs <;> simp
  | succ m ih =>
    intro a b f
    rw [Epow.eq_2]
    simp only [ih, eu_equiv]
    funext x
    simp [Finset.sum_apply, map_sum]

/- English proof (translation)
Unfold `gel`. Simplify using `only [epow_equiv]`. Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply, map_sum]`.
-/
theorem gel_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) (f : Mat n → V) :
    gel s m (fun x => A (f x)) = fun x => A (gel s m f x) := by
  unfold gel
  simp only [epow_equiv]
  funext x
  simp [Finset.sum_apply, map_sum]

/- English proof (translation)
Unfold `Om`. Rewrite using `[gel_equiv, gel_equiv]`. Use function extensionality and compare the values at `x`. Simplify using `[map_add, map_nsmul]`.
-/
theorem om_equiv (A : V ≃L[ℂ] V) (f : Mat n → V) : Om (fun x => A (f x)) = fun x => A (Om f x) := by
  unfold Om
  rw [gel_equiv, gel_equiv]
  funext x
  simp [map_add, map_nsmul]

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `f`. Simplify using `[zOp.eq_1]`.

Consider the case `cons p w ih`. Introduce `f`. Rewrite using `[zOp.eq_2]`. Simplify using `only [ih, gel_equiv]`.
-/
theorem zop_equiv (A : V ≃L[ℂ] V) : ∀ (w : List (Bool × ℕ)) (f : Mat n → V),
    zOp w (fun x => A (f x)) = fun x => A (zOp w f x) := by
  intro w
  induction w with
  | nil =>
    intro f
    simp [zOp.eq_1]
  | cons p w ih =>
    intro f
    rw [zOp.eq_2]
    simp only [ih, gel_equiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Eq
