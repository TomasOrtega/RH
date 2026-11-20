import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open GlobalTheory.TorsionForm

namespace GlobalTheory.TorsionGerm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  {τ τ' : E → Matrix (Fin g) (Fin g) ℂ}

section Deriv

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [SMul ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [SMul ℂ W]

/- English proof (translation)
Unfold `d10`. Rewrite using `[hf.fderiv_eq]`.
-/
theorem d10_congr {f f' : V → W} {P : V} (hf : f =ᶠ[𝓝 P] f') (v : V) :
    d10 f P v = d10 f' P v := by
  unfold d10; rw [hf.fderiv_eq]

/- English proof (translation)
Unfold `d01`. Rewrite using `[hf.fderiv_eq]`.
-/
theorem d01_congr {f f' : V → W} {P : V} (hf : f =ᶠ[𝓝 P] f') (v : V) :
    d01 f P v = d01 f' P v := by
  unfold d01; rw [hf.fderiv_eq]

end Deriv

/- English proof (translation)
Establish `e : flat τ P = flat τ' P`. Unfold `flat`. Rewrite using `[hτ.eq_of_nhds]`. Establish `e2 : (fun b => per (τ b) (flat τ P)) =ᶠ[𝓝 P.1] fun b => per (τ' b) (flat τ' P)` using `by filter_upwards [hτ] with b hb`. Rewrite using `[hb, e]`.

Unfold `hor`. Rewrite using `[e2.fderiv_eq]`.
-/
theorem hor_congr {P : Pt E g} (hτ : τ =ᶠ[𝓝 P.1] τ') (v : E) : hor τ P v = hor τ' P v := by
  have e : flat τ P = flat τ' P := by
    unfold flat; rw [hτ.eq_of_nhds]
  have e2 : (fun b => per (τ b) (flat τ P)) =ᶠ[𝓝 P.1] fun b => per (τ' b) (flat τ' P) := by
    filter_upwards [hτ] with b hb
    rw [hb, e]
  unfold hor; rw [e2.fderiv_eq]

/- English proof (translation)
Unfold `imPart`. Rewrite using `[hτ]`.
-/
theorem imPart_congr {b : E} (hτ : τ b = τ' b) : imPart τ b = imPart τ' b := by
  unfold imPart; rw [hτ]

/- English proof (translation)
Establish `e : ∀ a c, d01 (fun b' => imPart τ b' a c) b v = d01 (fun b' => imPart τ' b' a c) b v`. Introduce `a c`. Use `d01_congr ?_ v` and prove the remaining obligations. Use `filter_upwards [hτ] with x hx`. Rewrite using `[imPart_congr hx]`.

Unfold `connForm`. Simplify using `only [e, imPart_congr hτ.eq_of_nhds]`.
-/
theorem connForm_congr {b : E} (hτ : τ =ᶠ[𝓝 b] τ') (v : E) (w : Ext (n + n + g)) :
    connForm τ b v w = connForm τ' b v w := by
  have e : ∀ a c, d01 (fun b' => imPart τ b' a c) b v = d01 (fun b' => imPart τ' b' a c) b v := by
    intro a c
    refine d01_congr ?_ v
    filter_upwards [hτ] with x hx
    rw [imPart_congr hx]
  unfold connForm
  simp only [e, imPart_congr hτ.eq_of_nhds]

/- English proof (translation)
Unfold `pointDifference`. Rewrite using `[d10_congr hs, hs.eq_of_nhds]`.
-/
theorem nab10_congr (h : Pt E g → ℝ) {s s' : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hs : s =ᶠ[𝓝 P] s') (v : Pt E g) : pointDifference h s P v = pointDifference h s' P v := by
  unfold pointDifference; rw [d10_congr hs, hs.eq_of_nhds]

/- English proof (translation)
Unfold `superconn nablaE dbarV dbarAdj`. Simplify using `only [hor_congr hτ, connForm_congr hτ, nab10_congr h hs, d01_congr hs, hs.eq_of_nhds, imPart_congr hτ.eq_of_nhds]`.
-/
theorem superconn_congr (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    {s s' : Pt E g → Ext (n + n + g)} {P : Pt E g} (hτ : τ =ᶠ[𝓝 P.1] τ') (hs : s =ᶠ[𝓝 P] s') :
    superconn τ h β u s P = superconn τ' h β u s' P := by
  unfold superconn nablaE dbarV dbarAdj
  simp only [hor_congr hτ, connForm_congr hτ, nab10_congr h hs, d01_congr hs, hs.eq_of_nhds,
    imPart_congr hτ.eq_of_nhds]

/- English proof (translation)
Use function extensionality and compare the values at `f z`. Unfold `curv`. Use `superconn_congr h β u hτ ?_` and prove the remaining obligations. Establish `h1 : ∀ᶠ P : Pt E g in 𝓝 (b, z), τ =ᶠ[𝓝 P.1] τ'` using `(continuous_fst.tendsto ((b, z) : Pt E g)).eventually hτ.eventuallyEq_nhds`. Use `filter_upwards [h1] with P hP`.

Conclude with `superconn_congr h β u hP EventuallyEq.rfl`.
-/
theorem curv_congr (h : Pt E g → ℝ) (β : Fin n → E) {b : E} (hτ : τ =ᶠ[𝓝 b] τ') (u : ℝ) :
    curv τ h β b u = curv τ' h β b u := by
  funext f z
  unfold curv
  refine superconn_congr h β u hτ ?_
  have h1 : ∀ᶠ P : Pt E g in 𝓝 (b, z), τ =ᶠ[𝓝 P.1] τ' :=
    (continuous_fst.tendsto ((b, z) : Pt E g)).eventually hτ.eventuallyEq_nhds
  filter_upwards [h1] with P hP
  exact superconn_congr h β u hP EventuallyEq.rfl

/- English proof (translation)
Establish `e0 : τ b = τ' b` using `hτ.eq_of_nhds`. Establish `e1` using `curv_congr h β hτ`. Unfold `IsTorsionForm IsHeatTrace IsHeatKernel IsSec at H ⊢`. Simplify using `only [e0, e1] at H`. Conclude with `H`.
-/
theorem isTorsionForm_congr (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ)
    (τ τ' : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (T : Ext (n + n)) (hτ : τ =ᶠ[𝓝 b] τ')
    (H : IsTorsionForm τ M j h β b T) : IsTorsionForm τ' M j h β b T := by
  have e0 : τ b = τ' b := hτ.eq_of_nhds
  have e1 := curv_congr h β hτ
  unfold IsTorsionForm IsHeatTrace IsHeatKernel IsSec at H ⊢
  simp only [e0, e1] at H
  exact H

end GlobalTheory.TorsionGerm
