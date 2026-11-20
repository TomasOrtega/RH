import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF`. Take `⟨-, hGl, -⟩` from `CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ`. Establish `hG : CutMP.GlobCoef Θ (κ : ℝ)` using `hGl κ le_rfl`. Establish `hκ : (0 : ℝ) ≤ κ` using `Nat.cast_nonneg κ`. Take `⟨ε, hε, hFck, hFcc, hFs⟩` from `hF`.

Establish `hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε}` using `isOpen_lt (Gf_cont _ _) continuous_const`. Establish `hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0`. Introduce `g hg hgO`. Assume the negation of the conclusion as `hne`. Conclude with `absurd hgO (not_lt.2 (hFs g hg hne))`.

Use `⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1`. Introduce `A' m'`. Establish `h` using `(CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'`. Rewrite `h` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.

Introduce `g hg hne`. Assume the negation of the conclusion as `hlt`. Conclude with `hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))`. Conclude with `(rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1`. Introduce `A' m'`.

Conclude with `(rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'`. Introduce `g hg hne`. Assume the negation of the conclusion as `hlt`. Conclude with `hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))`.
-/
theorem spectral_nice_polynomial : RDSNicePoly := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF
  obtain ⟨-, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd hgO (not_lt.2 (hFs g hg hne))
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

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D _ _ Θ hΘ hC` and use `opProp1_of_poly spectral_nice_polynomial D hΘ hC`.
-/
theorem rDSPolyProp_of_nice : RDSPolyProp := fun k r Wp Wq _ _ _ _ _ _ D _ _ Θ hΘ hC =>
  opProp1_of_poly spectral_nice_polynomial D hΘ hC

end Formalism.FourierDecayAlt.P.CutSE
