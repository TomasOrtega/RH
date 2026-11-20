import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernFormsFrameIndependentClosed.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.chernForms_frame_independent_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  first | exact @GlobalTheory.ChernFrame.chern_frame_closed | exact GlobalTheory.ChernFrame.chern_frame_closed | (intros; apply GlobalTheory.ChernFrame.chern_frame_closed <;> assumption)
