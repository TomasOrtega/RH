import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

open MeasureTheory in
open scoped ContDiff BoundedContinuousFunction Topology in
/- English proof (translation)
Assemble the required witnesses or components as `⟨EuclideanSpace.single j 1, fun _ _ _ => rfl⟩`.
-/
private lemma exists_dir_dw_cons_eq_fderiv {d : ℕ} (j : Fin d) :
    ∃ e : _root_.ZetaZeros.D.EllReg.E d, ∀ (w : List (Fin d)) (f : _root_.ZetaZeros.D.EllReg.E d → ℂ) (x : _root_.ZetaZeros.D.EllReg.E d),
      _root_.ZetaZeros.D.EllReg.dw (j :: w) f x = fderiv ℝ (_root_.ZetaZeros.D.EllReg.dw w f) x e :=
  ⟨EuclideanSpace.single j 1, fun _ _ _ => rfl⟩

open MeasureTheory in
open scoped ContDiff BoundedContinuousFunction Topology in

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hu`. Consider the case `cons j w ih`. Take `⟨e, he⟩` from `exists_dir_dw_cons_eq_fderiv j`. Establish `h : _root_.ZetaZeros.D.EllReg.dw (j :: w) u = fun x => fderiv ℝ (_root_.ZetaZeros.D.EllReg.dw w u) x e` using `funext (he w u)`.

Rewrite using `[h]`. Conclude with `(ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const`.
-/
theorem _root_.GlobalTheory.HCA.contDiffOn_dw_of_isOpen {d : ℕ} {U : Set (_root_.ZetaZeros.D.EllReg.E d)} (hU : IsOpen U) (w : List (Fin d))
    (u : _root_.ZetaZeros.D.EllReg.E d → ℂ) (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (_root_.ZetaZeros.D.EllReg.dw w u) U := by
  induction w with
  | nil => exact hu
  | cons j w ih =>
    obtain ⟨e, he⟩ := exists_dir_dw_cons_eq_fderiv j
    have h : _root_.ZetaZeros.D.EllReg.dw (j :: w) u = fun x => fderiv ℝ (_root_.ZetaZeros.D.EllReg.dw w u) x e := funext (he w u)
    rw [h]
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

open MeasureTheory in
open scoped ContDiff BoundedContinuousFunction Topology in

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h`. Consider the case `cons j w ih`. Take `⟨e, he⟩` from `exists_dir_dw_cons_eq_fderiv j`. Introduce `x hx`.

Rewrite using `[he, he, (ih.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq]`.
-/
theorem _root_.GlobalTheory.HCA.eqOn_dw_of_isOpen {d : ℕ} {U : Set (_root_.ZetaZeros.D.EllReg.E d)} (hU : IsOpen U) (w : List (Fin d))
    (u v : _root_.ZetaZeros.D.EllReg.E d → ℂ) (h : Set.EqOn u v U) : Set.EqOn (_root_.ZetaZeros.D.EllReg.dw w u) (_root_.ZetaZeros.D.EllReg.dw w v) U := by
  induction w with
  | nil => exact h
  | cons j w ih =>
    obtain ⟨e, he⟩ := exists_dir_dw_cons_eq_fderiv j
    intro x hx
    rw [he, he, (ih.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons j w ih`. Introduce `x hx`.

Establish `hn` using `hU.mem_nhds hx`. Establish `he : dw w (s • u + t • v) =ᶠ[nhds x] s • dw w u + t • dw w v` using `ih.eventuallyEq_of_mem hn`. Establish `hdu : DifferentiableAt ℝ (dw w u) x` using `((contDiffOn_dw_of_isOpen hU w u hu).contDiffAt hn).differentiableAt (by simp)`. Establish `hdv : DifferentiableAt ℝ (dw w v) x` using `((contDiffOn_dw_of_isOpen hU w v hv).contDiffAt hn).differentiableAt (by simp)`. Establish `hd : HasFDerivAt (s • dw w u + t • dw w v) (s • fderiv ℝ (dw w u) x + t • fderiv ℝ (dw w v) x) x` using `(hdu.hasFDerivAt.const_smul s).add (hdv.hasFDerivAt.const_smul t)`.

Use `show fderiv ℝ (dw w (s • u + t • v)) x (ev j) = s • fderiv ℝ (dw w u) x (ev j) + t • fderiv ℝ (dw w v) x (ev j)`. Rewrite using `[he.fderiv_eq, hd.fderiv]`. Both sides reduce to the same expression.
-/
theorem eqOn_dw_lincomb_of_isOpen {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d))
    (u v : E d → ℂ) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (s t : ℂ) :
    Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U := by
  induction w with
  | nil => intro x _; rfl
  | cons j w ih =>
    intro x hx
    have hn := hU.mem_nhds hx
    have he : dw w (s • u + t • v) =ᶠ[nhds x] s • dw w u + t • dw w v := ih.eventuallyEq_of_mem hn
    have hdu : DifferentiableAt ℝ (dw w u) x :=
      ((contDiffOn_dw_of_isOpen hU w u hu).contDiffAt hn).differentiableAt (by simp)
    have hdv : DifferentiableAt ℝ (dw w v) x :=
      ((contDiffOn_dw_of_isOpen hU w v hv).contDiffAt hn).differentiableAt (by simp)
    have hd : HasFDerivAt (s • dw w u + t • dw w v)
        (s • fderiv ℝ (dw w u) x + t • fderiv ℝ (dw w v) x) x :=
      (hdu.hasFDerivAt.const_smul s).add (hdv.hasFDerivAt.const_smul t)
    show fderiv ℝ (dw w (s • u + t • v)) x (ev j)
      = s • fderiv ℝ (dw w u) x (ev j) + t • fderiv ℝ (dw w v) x (ev j)
    rw [he.fderiv_eq, hd.fderiv]
    rfl

/- English proof (translation)
Introduce `_ _ hU w` and use `⟨contDiffOn_dw_of_isOpen hU w, eqOn_dw_of_isOpen hU w, eqOn_dw_lincomb_of_isOpen hU w⟩`.
-/
theorem dw_smooth_local_linear : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)),
    (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧
    (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧
    (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ,
      Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) :=
  fun _ _ hU w => ⟨contDiffOn_dw_of_isOpen hU w, eqOn_dw_of_isOpen hU w,
    eqOn_dw_lincomb_of_isOpen hU w⟩

end GlobalTheory.HCA
