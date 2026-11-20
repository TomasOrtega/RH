import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Introduce `g hg hgO`. Unfold `B.opApply`. Apply `List.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`. Take `⟨T, hT, rfl⟩` from `List.mem_map.1 hx`.

Rewrite using `[Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO T.word_lie hz g hg hgO, map_zero]`.
-/
theorem rdsp_opApply_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ F g = 0 := by
  intro g hg hgO
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO T.word_lie hz g hg hgO, map_zero]

/- English proof (translation)
Introduce `g hg hgO`. Simplify using `only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]`. Rewrite using `[hz g hg hgO, map_zero]`.
-/
theorem rdsp_adjFn_vanish (T : B.DTerm k r Wp Wq) {O : Set (B.Mat k r)}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → ap T.coefAdj F g = 0 := by
  intro g hg hgO
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
  rw [hz g hg hgO, map_zero]

/- English proof (translation)
Introduce `X hX`. Conclude with `T.word_lie X (List.mem_reverse.mp hX)`.
-/
theorem rdsp_lie_rev (T : B.DTerm k r Wp Wq) : ∀ X ∈ T.word.reverse, inLie k r X := by
  intro X hX
  exact T.word_lie X (List.mem_reverse.mp hX)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdsp_opAdj_eq (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.opAdj Θ F = fun g => (Θ.map fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g).sum := rfl

/- English proof (translation)
Introduce `g hg hgO`. Rewrite using `[rdsp_opAdj_eq]`. Apply `List.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`. Take `⟨T, hT, rfl⟩` from `List.mem_map.1 hx`.

Rewrite using `[Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO (rdsp_lie_rev T) (rdsp_adjFn_vanish T hz) g hg hgO, smul_zero]`.
-/
theorem rdsp_opAdj_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ F g = 0 := by
  intro g hg hgO
  rw [rdsp_opAdj_eq]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO (rdsp_lie_rev T) (rdsp_adjFn_vanish T hz) g hg hgO, smul_zero]

/- English proof (translation)
Establish `hO : IsOpen (∅ : Set (B.Mat k r))` using `isOpen_empty`. Establish `hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r` using `fun g hg => Or.inr hg`. Establish `hz0 : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) → F g = 0` using `fun g _ hg => by simp at hg`. Establish `hapck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coefAdj F)` using `fun T hT => Pr.ck hO hcov ⟨(hG T hT).2.1, hF, hz0⟩`. Establish `hRck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word.reverse (ap T.coefAdj F))`.

Introduce `T hT`. Rewrite using `[← Dw_wR]`. Apply `CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) (rdsp_lie_rev T) x (by simpa [wL] using hx))` to reduce the goal to its premises. Simplify using `using hapck T hT`. Establish `hapcc : ∀ T ∈ Θ, ∀ m : ℕ, B.InCC A m (ap T.coefAdj F)`.

Introduce `T hT m`. Take `⟨hc1, hc2, hcb⟩` from `hG T hT`. Take `⟨C, hC⟩` from `hcb m`. Take `⟨c, hc⟩` from `hFA m`. Conclude with `⟨_, prodBound hO hcov (sCkOn_mono le_top hc2) (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).2) hc hz0⟩`.

Rewrite using `[rdsp_opAdj_eq]`. Use `⟨?_, fun m => ?_⟩` and prove the remaining obligations. Use `clear hapcc`. Proceed by induction on `Θ with`. Consider the case `nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))`.

Consider the case `cons T Θ ih`. Establish `h1 : B.CkOn ⊤ (B.GV k r) (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g)` using `CkOn_smul _ (hRck T (by simp))`. Establish `h2` using `ih (fun S hS => hG S (by simp [hS])) (fun S hS => hapck S (by simp [hS])) (fun S hS => hRck S (by simp [hS]))`. Simplify using `using CkOn_add h1 h2`. Use `InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) ?_` and prove the remaining obligations.

Introduce `T hT`. Take `⟨c, hc⟩ : B.InCC A m (B.Rw T.word.reverse (ap T.coefAdj F))` from `InCC_Rw (rdsp_lie_rev T) (hapcc T hT _)`. Conclude with `⟨_, CCle_smul _ hc⟩`.
-/
theorem rdsp_opAdj_cc (Θ : B.DiffOp k r Wp Wq) (d : ℝ) (hG : CutMP.GlobCoef Θ d) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV k r) F) (A : ℝ) (hFA : ∀ m : ℕ, B.InCC (A + d) m F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧ ∀ m : ℕ, B.InCC A m (B.opAdj Θ F) := by
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hz0 : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) → F g = 0 := fun g _ hg => by simp at hg
  have hapck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coefAdj F) := fun T hT =>
    Pr.ck hO hcov ⟨(hG T hT).2.1, hF, hz0⟩
  have hRck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word.reverse (ap T.coefAdj F)) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) (rdsp_lie_rev T) x (by simpa [wL] using hx))
    simpa using hapck T hT
  have hapcc : ∀ T ∈ Θ, ∀ m : ℕ, B.InCC A m (ap T.coefAdj F) := by
    intro T hT m
    obtain ⟨hc1, hc2, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ := hFA m
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc2)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).2) hc hz0⟩
  rw [rdsp_opAdj_eq]
  refine ⟨?_, fun m => ?_⟩
  · clear hapcc
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) :=
        CkOn_smul _ (hRck T (by simp))
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hapck S (by simp [hS]))
        (fun S hS => hRck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · refine InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) ?_
    intro T hT
    obtain ⟨c, hc⟩ : B.InCC A m (B.Rw T.word.reverse (ap T.coefAdj F)) :=
      InCC_Rw (rdsp_lie_rev T) (hapcc T hT _)
    exact ⟨_, CCle_smul _ hc⟩

end

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ hC`. Take `⟨hS, hGl, -⟩` from `CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ`. Establish `hG : CutMP.GlobCoef Θ (κ : ℝ)` using `hGl κ le_rfl`. Establish `hκ : (0 : ℝ) ≤ κ` using `Nat.cast_nonneg κ`. Use `⟨hS _, hC, fun ε _ => ⟨κ, hκ, fun T hT => ?_⟩, fun F hF => ?_⟩` and prove the remaining obligations.

Take `⟨-, -, hb⟩` from `hG T hT`. Take `⟨Cb, hCb⟩` from `hb (B.opOrder Θ + 5)`. Conclude with `⟨Cb, fun u v hu hv hl g hg _ => hCb u v hu hv hl g hg⟩`. Take `⟨ε, hε, hFck, hFcc, hFs⟩` from `hF`. Establish `hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε}` using `isOpen_lt (Gf_cont _ _) continuous_const`.

Establish `hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0`. Introduce `g hg hgO`. Assume the negation of the conclusion as `hne`. Use `hFs g hg hne` as an intermediate fact. Conclude with `absurd hgO (not_lt.2 this)`.

Use `⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1`. Introduce `A' m'`. Establish `h` using `(CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'`. Rewrite `h` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.

Introduce `g hg hne`. Assume the negation of the conclusion as `hlt`. Conclude with `hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))`. Conclude with `(rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1`. Introduce `A' m'`.

Conclude with `(rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'`. Introduce `g hg hne`. Assume the negation of the conclusion as `hlt`. Conclude with `hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))`.
-/
theorem spectral_polynomial_property : RDSPolyProp := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ hC
  obtain ⟨hS, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  refine ⟨hS _, hC, fun ε _ => ⟨κ, hκ, fun T hT => ?_⟩, fun F hF => ?_⟩
  · obtain ⟨-, -, hb⟩ := hG T hT
    obtain ⟨Cb, hCb⟩ := hb (B.opOrder Θ + 5)
    exact ⟨Cb, fun u v hu hv hl g hg _ => hCb u v hu hv hl g hg⟩
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    have := hFs g hg hne
    exact absurd hgO (not_lt.2 this)
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
