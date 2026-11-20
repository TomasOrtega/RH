import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ Θ d A hd hG F hF hFA`. Establish `hO : IsOpen (∅ : Set (B.Mat k r))` using `isOpen_empty`. Establish `hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r` using `fun g hg => Or.inr hg`. Establish `hΦck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word F)`. Introduce `T hT`.

Rewrite using `[← Dw_wR]`. Apply `CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) T.word_lie x (by simpa [wL] using hx))` to reduce the goal to its premises. Simplify using `using hF`. Establish `hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum` using `rfl`. Use `⟨?_, fun m => ?_⟩` and prove the remaining obligations.

Rewrite using `[hop] clear hop`. Proceed by induction on `Θ with`. Consider the case `nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))`. Consider the case `cons T Θ ih`. Establish `h1 : B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F))` using `Pr.ck hO hcov ⟨(hG T (by simp)).1, hΦck T (by simp), fun g _ hg => by simp at hg⟩`.

Establish `h2` using `ih (fun S hS => hG S (by simp [hS])) (fun S hS => hΦck S (by simp [hS]))`. Simplify using `using CkOn_add h1 h2`. Rewrite using `[hop]`. Use `InCC_opsum Θ (fun T => ap T.coef (B.Rw T.word F)) ?_` and prove the remaining obligations. Introduce `T hT`.

Take `⟨hc1, -, hcb⟩` from `hG T hT`. Take `⟨C, hC⟩` from `hcb m`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : B.InCC (A - d + d) m (B.Rw T.word F) := by`. Rewrite using `[sub_add_cancel]`. Conclude with `InCC_Rw T.word_lie (hFA _)`.

Conclude with `⟨_, prodBound hO hcov (sCkOn_mono le_top hc1) (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hc (fun g _ hg => by simp at hg)⟩`.
-/
theorem class_lower_decay_holds : JDCCLower := by
  intro k r Wp Wq _ _ _ _ _ _ Θ d A hd hG F hF hFA
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hΦck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word F) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) T.word_lie x (by simpa [wL] using hx))
    simpa using hF
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  refine ⟨?_, fun m => ?_⟩
  · rw [hop]
    clear hop
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) :=
        Pr.ck hO hcov ⟨(hG T (by simp)).1, hΦck T (by simp), fun g _ hg => by simp at hg⟩
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hΦck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · rw [hop]
    refine InCC_opsum Θ (fun T => ap T.coef (B.Rw T.word F)) ?_
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ : B.InCC (A - d + d) m (B.Rw T.word F) := by
      rw [sub_add_cancel]; exact InCC_Rw T.word_lie (hFA _)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hc (fun g _ hg => by simp at hg)⟩

end

end Formalism.FourierDecayAlt.P.CutMP
