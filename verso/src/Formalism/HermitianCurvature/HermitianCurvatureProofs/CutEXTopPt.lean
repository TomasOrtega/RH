import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FnValLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutEXTop

/- English proof (translation)
Substitute `hr'` using the available equality. Take `⟨-, hxG, hxP⟩` from `hx`. Establish `himg` using `Formalism.FourierDecayAlt.P.level_group_image k i 0`. Establish `hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩` using `hxG`. Rewrite `hxG'` using `[himg]`.

Take `⟨g, hgU, hgx⟩` from `hxG'`. Use `⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩` and prove the remaining obligations. Rewrite using `[← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]`. Conclude with `hxP`.
-/
theorem domR_pt (k i r' : ℕ) (hr' : r' = 0) (zs zs' : Fin (2 * r' + k + 1) → ℂ) (x : (Fin (i + r') → ℂ) × Q.Mx k (i + r'))
    (hx : x ∈ Q.DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs')) :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = ιLev k i r' g := by
  subst hr'
  obtain ⟨-, hxG, hxP⟩ := hx
  have himg := Formalism.FourierDecayAlt.P.level_group_image k i 0
  have hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩ := hxG
  rw [himg] at hxG'
  obtain ⟨g, hgU, hgx⟩ := hxG'
  refine ⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩
  rw [← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]
  exact hxP

/- English proof (translation)
Substitute `hn` using the available equality. Substitute `hz` using the available equality. Substitute `hz'` using the available equality. Take `⟨g, h1, h2, h3⟩` from `domR_pt k i r' hr' zs zs' x hx`. Conclude with `⟨g, h1, h2, h3⟩`.
-/
theorem domR_pt_cast (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0) {z z' : Fin (2 * n + k + 1) → ℂ}
    {zs zs' : Fin (2 * r' + k + 1) → ℂ} (hz : D.castV hn (liftVec k i r' zs) = z)
    (hz' : D.castV hn (liftVec k i r' zs') = z') (x : (Fin n → ℂ) × Q.Mx k n) (hx : x ∈ Q.DomR k n z z') :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = D.castM hn (ιLev k i r' g) := by
  subst hn
  subst hz
  subst hz'
  obtain ⟨g, h1, h2, h3⟩ := domR_pt k i r' hr' zs zs' x hx
  exact ⟨g, h1, h2, h3⟩

/- English proof (translation)
Substitute `hρ` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨h, fun a => a.elim0⟩`. Introduce `h`.

Conclude with `h.1`.
-/
theorem gv_iff_glev (k ρ : ℕ) (hρ : ρ = 0) (γ : B.Mat k ρ) : γ ∈ B.GV k ρ ↔ γ ∈ Q.Glev k ρ (Fin.last ρ) := by
  subst hρ
  constructor
  · intro h
    exact ⟨h, fun a => a.elim0⟩
  · intro h
    exact h.1

end Formalism.FourierDecayAlt.P.CutEXTop

open Formalism.FourierDecayAlt.P.CutEXTop in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p`. Use `⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩` and prove the remaining obligations. Conclude with `domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx`.
-/
theorem Formalism.FourierDecayAlt.P.top_point_existence : Formalism.FourierDecayAlt.P.CutEX.TopPt := by
  intro Wp Wq _ _ _ _ _ _ P p
  refine ⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩
  exact domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx
