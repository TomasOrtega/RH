import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffA

noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace STD

variable {n : ℕ}

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) U` using `hf.fderiv_of_isOpen hU (by simp)`. Conclude with `(h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))`.
-/
theorem contDiffOn_dc {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (a : Fin n × Fin n) : ContDiffOn ℝ ∞ (dc a f) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))

/- English proof (translation)
The claim follows from `| [] => hf | a :: l => contDiffOn_dc hU (contDiffOn_dList hU hf l) a`.
-/
theorem contDiffOn_dList {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ l : List (Fin n × Fin n), ContDiffOn ℝ ∞ (dList l f) U
  | [] => hf
  | a :: l => contDiffOn_dc hU (contDiffOn_dList hU hf l) a

structure IsT (U : Set (Vr n)) (φ : Vr n → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  cpt : HasCompactSupport φ
  sub : tsupport φ ⊆ U

/- English proof (translation)
Introduce `x hx`. Assume the negation of the conclusion as `h`. Apply `hx` to reduce the goal to its premises. Establish `: fderiv ℝ f x = 0`. Assume the negation of the conclusion as `h'`.

Conclude with `h (support_fderiv_subset (𝕜 := ℝ) h')`. Simplify using `[dc, this]`.
-/
theorem support_dc_subset (f : Vr n → ℂ) (a : Fin n × Fin n) : support (dc a f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  have : fderiv ℝ f x = 0 := by
    by_contra h'
    exact h (support_fderiv_subset (𝕜 := ℝ) h')
  simp [dc, this]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)`. Conclude with `h.cpt.mono' (support_dc_subset φ a)`. Conclude with `(closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub`.
-/
theorem isT_dc {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) (a : Fin n × Fin n) : IsT U (dc a φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)
  · exact h.cpt.mono' (support_dc_subset φ a)
  · exact (closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub

/- English proof (translation)
The claim follows from `| [] => h | a :: l => isT_dc (isT_dList h l) a`.
-/
theorem isT_dList {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) : ∀ l : List (Fin n × Fin n), IsT U (dList l φ)
  | [] => h
  | a :: l => isT_dc (isT_dList h l) a

/- English proof (translation)
The claim follows from `| [] => le_rfl | a :: l => (closure_minimal ((support_dc_subset _ a).trans (tsupport_dList_subset φ l)) (isClosed_tsupport φ))`.
-/
theorem tsupport_dList_subset (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  | [] => le_rfl
  | a :: l => (closure_minimal ((support_dc_subset _ a).trans (tsupport_dList_subset φ l))
      (isClosed_tsupport φ))

/- English proof (translation)
Establish `hc' : Continuous (fun x => h x * φ x)` using `(hh.mul hφ.continuousOn).continuous_of_tsupport_subset hU ((tsupport_mul_subset_right).trans hs)`. Conclude with `hc'.integrable_of_hasCompactSupport hc.mul_left`.
-/
theorem integrable_mul_of_contOn {U : Set (Vr n)} (hU : IsOpen U) {h φ : Vr n → ℂ} (hh : ContinuousOn h U)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => h x * φ x) := by
  have hc' : Continuous (fun x => h x * φ x) :=
    (hh.mul hφ.continuousOn).continuous_of_tsupport_subset hU ((tsupport_mul_subset_right).trans hs)
  exact hc'.integrable_of_hasCompactSupport hc.mul_left

/- English proof (translation)
Establish `hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x` using `fun x hx => (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)`. Establish `hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x` using `fun x _ => (hφ.smooth.differentiable (by simp)) x`. Establish `hFc : ContinuousOn (fun x => fderiv ℝ F x) U` using `hF.continuousOn_fderiv_of_isOpen hU (by simp)`. Establish `hφc : Continuous (fun x => fderiv ℝ φ x)` using `hφ.smooth.continuous_fderiv (by simp)`. Establish `hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x)` using `fun v => integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub`.

Establish `hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v)` using `fun v => integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const) (hφ.cpt.fderiv_apply ℝ v) ((closure_minimal (fun x hx => support_fderiv_subset ℝ (fun h0 => (Function.mem_support.mp hx) (by simp [h0]))) (isClosed_tsupport φ)).trans hφ.sub)`. Establish `key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x` using `fun v => integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v) (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd`. Establish `e1 : ∫ x, F x * dc a φ x = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2)`. Rewrite using `[← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [dc]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∫ x, dc a F x * φ x = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x`. Rewrite using `[← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [dc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, key, key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ibp_dc {U : Set (Vr n)} (hU : IsOpen U) {F φ : Vr n → ℂ} (hF : ContDiffOn ℝ ∞ F U)
    (hφ : IsT U φ) (a : Fin n × Fin n) :
    ∫ x, F x * dc a φ x = - ∫ x, dc a F x * φ x := by
  have hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x := fun x hx =>
    (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)
  have hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x := fun x _ =>
    (hφ.smooth.differentiable (by simp)) x
  have hFc : ContinuousOn (fun x => fderiv ℝ F x) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hφc : Continuous (fun x => fderiv ℝ φ x) := hφ.smooth.continuous_fderiv (by simp)
  have hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x) := fun v =>
    integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub
  have hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v) := fun v =>
    integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const)
      (hφ.cpt.fderiv_apply ℝ v)
      ((closure_minimal (fun x hx => support_fderiv_subset ℝ
        (fun h0 => (Function.mem_support.mp hx) (by simp [h0])))
        (isClosed_tsupport φ)).trans hφ.sub)
  have key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v)
      (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd
  have e1 : ∫ x, F x * dc a φ x
      = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2) := by
    rw [← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  have e2 : ∫ x, dc a F x * φ x
      = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x := by
    rw [← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  rw [e1, e2, key, key]
  ring

/- English proof (translation)
Introduce `l`. Use `match l with`. Consider the case `[] => intro F φ _ _`. Simplify using `[dList]`. Consider the case `a :: l`.

Introduce `F φ hF hφ`. Establish `happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f)`. Introduce `l m f`. Proceed by induction on `l with`. Consider the case `nil => simp [dList]`.

Consider the case `cons b l ih => simp [dList, ih]`. Establish `h1` using `ibp_dc hU hF (isT_dList hφ l) a`. Establish `h2` using `ibp_dList hU l (contDiffOn_dc hU hF a) hφ`. Rewrite using `[dList, h1, h2, List.reverse_cons, happ]`. Simplify using `only [dList, List.length_cons, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ibp_dList {U : Set (Vr n)} (hU : IsOpen U) :
    ∀ (l : List (Fin n × Fin n)) {F φ : Vr n → ℂ}, ContDiffOn ℝ ∞ F U → IsT U φ →
      ∫ x, F x * dList l φ x = (-1) ^ l.length * ∫ x, dList l.reverse F x * φ x := by
  intro l
  match l with
  | [] => intro F φ _ _; simp [dList]
  | a :: l =>
    intro F φ hF hφ
    have happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f) := by
      intro l m f
      induction l with
      | nil => simp [dList]
      | cons b l ih => simp [dList, ih]
    have h1 := ibp_dc hU hF (isT_dList hφ l) a
    have h2 := ibp_dList hU l (contDiffOn_dc hU hF a) hφ
    rw [dList, h1, h2, List.reverse_cons, happ]
    simp only [dList, List.length_cons, pow_succ]
    ring

end STD

end PositivityTheory.Rg.Sw.LVs
