import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.PullBdd

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hx`.
-/
theorem castFrame_mem_GG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E}
    {p0 : ℕ} {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hb`.
-/
theorem castFrame_mem_Bor {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) : castFrame h b ∈ Bor Ψ' r := by
  subst h; exact hb

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem bchar_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) (b : Frame Ψ r) :
    bchar la (castFrame h b) = bchar (castWt h la) b := by
  subst h; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem castFrame_rmul {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFrame h (rmul x b) = rmul (castFrame h x) (castFrame h b) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem castFrame_lact {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (β : GL (Fin r) E) (x : Frame Ψ r) :
    castFrame h (lact β x) = lact β (castFrame h x) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ`. Rewrite using `[Matrix.mul_assoc]`.
-/
theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (β : GL (Fin r) E) (x b : Frame Ψ r) :
    lact β (rmul x b) = rmul (lact β x) b := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = ((↑(β * γ) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)`. Rewrite using `[Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (β γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact β (lact γ x) = lact (β * γ) x := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
      Matrix (Fin r) (Fin r) ℂ) =
    ((↑(β * γ) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

/- English proof (translation)
Establish `e1 : mat (lact β x) τ = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ` using `rfl`. Establish `e2 : gram τ.1 G (mat (lact β x) τ) = gram τ.1 G (mat x τ)`. Use extensionality with `a b`. Simplify using `only [gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hβ]`. Unfold `dmin`.

Rewrite using `[e2]`.
-/
theorem dmin_lact {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {β : GL (Fin r) E}
    (hβ : ∀ u v, herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm G u v) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (lact β x) τ i = dmin G x τ i := by
  have e1 : mat (lact β x) τ = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have e2 : gram τ.1 G (mat (lact β x) τ) = gram τ.1 G (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hβ]
  unfold dmin
  rw [e2]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem nfac_cast {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E)
    (la : Wt Ψ' r) (x : Frame Ψ r) :
    (∏ τ : Ψ', ∏ i : Fin r, ‖dmin G (castFrame h x) τ i.succ / dmin G (castFrame h x) τ i.castSucc‖ ^
      (-(la τ i : ℝ) / 2)) =
    ∏ τ : Ψ, ∏ i : Fin r, ‖dmin G x τ i.succ / dmin G x τ i.castSucc‖ ^
      (-(castWt h la τ i : ℝ) / 2) := by
  subst h; rfl

/- English proof (translation)
Take `⟨⟨hQd, hQB, hQΓ⟩, C, hC⟩` from `hQ`. Establish `hmaps : ∀ x ∈ X.dom, lact β (castFrame hΨ x) ∈ Y.dom`. Introduce `x hx`. Establish `h1` using `castFrame_mem_GG hΨ hx`. Rewrite `h1` using `[hG, hp]`.

Conclude with `GlobalTheory.FrameFibre.lact_mem_GG hβ h1`. Use `⟨⟨?_, ?_, ?_⟩, C, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hd : Differentiable ℂ (fun x : Frame X.Ψ r => lact β (castFrame hΨ x))`. Rewrite using `[differentiable_pi]`. Introduce `τ`.

Rewrite using `[differentiable_pi]`. Introduce `a`. Rewrite using `[differentiable_pi]`. Introduce `b`. Simplify using `only [lact, castFrame, mat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]`.

Use `fun_prop`. Conclude with `hQd.comp hd.differentiableOn hmaps`. Introduce `x hx b hb`. Simplify using `only`. Rewrite using `[castFrame_rmul, lact_rmul, hQB _ (hmaps x hx) _ (castFrame_mem_Bor hΨ hb), bchar_castFrame]`.

Introduce `γ hγ x hx`. Simplify using `only`. Rewrite using `[hχX γ hγ, one_mul, castFrame_lact, lact_lact, show β * γ = (β * γ * β⁻¹) * β by group, ← lact_lact, hQΓ _ (hΓ γ hγ) _ (hmaps x hx), hχY _ (hΓ γ hγ), one_mul]`. Use `le_trans (le_of_eq ?_) (hC _ (hmaps x hx))` and prove the remaining obligations. Unfold `Data.pnorm`.

Use `congr 1`. Simplify using `only [dmin_lact hβ]`. Rewrite using `[← hG]`. Conclude with `(nfac_cast hΨ X.Gm la x).symm`.
-/
theorem isBddSec_transport (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hG : X.Gm = Y.Gm) (hp : X.p0 = Y.p0)
    (β : GL (Fin r) E)
    (hβ : ∀ u v, herm Y.Gm ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm Y.Gm u v)
    (hΓ : ∀ γ ∈ X.Γ, β * γ * β⁻¹ ∈ Y.Γ) (la : Wt Y.Ψ r)
    (hχX : ∀ γ ∈ X.Γ, X.χ (castWt hΨ la) γ = 1) (hχY : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (Q : Frame Y.Ψ r → ℂ) (hQ : Y.IsBddSec la Q) :
    X.IsBddSec (castWt hΨ la) (fun x => Q (lact β (castFrame hΨ x))) := by
  obtain ⟨⟨hQd, hQB, hQΓ⟩, C, hC⟩ := hQ
  have hmaps : ∀ x ∈ X.dom, lact β (castFrame hΨ x) ∈ Y.dom := by
    intro x hx
    have h1 := castFrame_mem_GG hΨ hx
    rw [hG, hp] at h1
    exact GlobalTheory.FrameFibre.lact_mem_GG hβ h1
  refine ⟨⟨?_, ?_, ?_⟩, C, fun x hx => ?_⟩
  · have hd : Differentiable ℂ (fun x : Frame X.Ψ r => lact β (castFrame hΨ x)) := by
      rw [differentiable_pi]; intro τ; rw [differentiable_pi]; intro a; rw [differentiable_pi]; intro b
      simp only [lact, castFrame, mat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
      fun_prop
    exact hQd.comp hd.differentiableOn hmaps
  · intro x hx b hb
    simp only
    rw [castFrame_rmul, lact_rmul, hQB _ (hmaps x hx) _ (castFrame_mem_Bor hΨ hb), bchar_castFrame]
  · intro γ hγ x hx
    simp only
    rw [hχX γ hγ, one_mul, castFrame_lact, lact_lact,
      show β * γ = (β * γ * β⁻¹) * β by group, ← lact_lact, hQΓ _ (hΓ γ hγ) _ (hmaps x hx),
      hχY _ (hΓ γ hγ), one_mul]
  · refine le_trans (le_of_eq ?_) (hC _ (hmaps x hx))
    unfold Data.pnorm
    congr 1
    simp only [dmin_lact hβ]
    rw [← hG]
    exact (nfac_cast hΨ X.Gm la x).symm

end

/- English proof (translation)
Introduce `E _ _ _ r U C _ _ M la F hF h c`. Establish `hY` using `(hF (h • c)).1`. Conclude with `isBddSec_transport (M.comp c).toData (M.comp (h • c)).toData ((M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm) (by rw [M.comp_Gm, M.comp_Gm]) (by rw [M.comp_basePoint, M.comp_basePoint]) (M.tr h c) (by rw [M.comp_Gm]; exact M.tr_herm h c) (fun γ hγ => (M.tr_conj h c γ).1 hγ) (castWt ( …`.
-/
theorem pull_isBddSec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type)
    [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ),
    F ∈ M.SS la → ∀ (h : U) (c : C),
      (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  intro E _ _ _ r U C _ _ M la F hF h c
  have hY := (hF (h • c)).1
  exact isBddSec_transport (M.comp c).toData (M.comp (h • c)).toData
    ((M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm) (by rw [M.comp_Gm, M.comp_Gm])
    (by rw [M.comp_basePoint, M.comp_basePoint]) (M.tr h c) (by rw [M.comp_Gm]; exact M.tr_herm h c)
    (fun γ hγ => (M.tr_conj h c γ).1 hγ) (castWt (M.comp_Ψ (h • c)) la)
    (fun γ hγ => M.χ_one c _ γ hγ) (fun γ hγ => M.χ_one (h • c) _ γ hγ) _ hY

end GlobalTheory.PullBdd
