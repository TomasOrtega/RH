import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `E _ _ k ρ hρ J c g`. Substitute `hρ` using the available equality. Simplify using `[Q.resG, Q.wCell]`.
-/
theorem residue_top_exceptional : ResTop := by
  intro E _ _ k ρ hρ J c g
  subst hρ
  simp [Q.resG, Q.wCell]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k ρ z z' π π' Ψ Ψ' h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Distinguish the cases in `hx : ((c, g) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'`. Conclude with `h _ hx`.

Rewrite using `[Ψ.2.1 (c, g) hx, Ψ'.2.1 (c, g) hx]`.
-/
theorem radial_extension_holds : RadExt := by
  intro Wp Wq _ _ _ _ k ρ z z' π π' Ψ Ψ' h
  apply Subtype.ext
  funext c g
  by_cases hx : ((c, g) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
  · exact h _ hx
  · rw [Ψ.2.1 (c, g) hx, Ψ'.2.1 (c, g) hx]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k ρ z z' π π' f hloc hequiv`. Establish `hUW : ∀ {w : Fin (2 * ρ + k + 1) → ℂ} {h : Mx k ρ}, h ∈ UWset k ρ w → h ∈ Glev k ρ (Fin.last ρ)` using `fun hh => ⟨hh.1, fun a _ => hh.2.1 a⟩`. Use `⟨⟨fun c g => if (c, g) ∈ DomR k ρ z z' then f g else 0, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = 0`. Conclude with `if_neg hx`.

Introduce `x₀ hx₀`. Take `⟨hΩ, hG, hpos⟩` from `hx₀`. Take `⟨U, F, hU, hgU, hF, hFe⟩` from `hloc x₀.2 hG hpos`. Use `⟨OmX ρ ×ˢ (U ∩ {g | 0 < GGl k ρ z z' g}), fun x => F x.2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX ρ).prod (hU.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k ρ z z')))`.

Conclude with `⟨hΩ, hgU, hpos⟩`. Conclude with `hF.comp contDiff_snd.contDiffOn (fun x hx => hx.2.1)`. Introduce `x hx hxG`. Establish `hxD : (x.1, x.2) ∈ DomR k ρ z z'` using `⟨hx.1, hxG, hx.2.2⟩`. Use `show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = F x.2`.

Rewrite using `[if_pos hxD]`. Conclude with `hFe x.2 hx.2.1 hxG`. Introduce `x hx h hh h' hh'`. Take `⟨hΩ, hG, hpos⟩` from `hx`. Establish `hD : (x.1, h * x.2 * h') ∈ DomR k ρ z z'` using `⟨hΩ, Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (hUW hh) hG) (hUW hh'), by rw [Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh hh']; exact hpos⟩`.

Establish `hD0 : (x.1, x.2) ∈ DomR k ρ z z'` using `⟨hΩ, hG, hpos⟩`. Use `show (if (x.1, h * x.2 * h') ∈ DomR k ρ z z' then f (h * x.2 * h') else 0) = π h ∘SL (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) ∘SL π' h'`. Rewrite using `[if_pos hD, if_pos hD0]`. Conclude with `hequiv x.2 hG hpos h hh h' hh'`. Introduce `x hx show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = f x.2`.

Conclude with `if_pos hx`.
-/
theorem radial_of_function_holds : RadOfFun := by
  classical
  intro Wp Wq _ _ _ _ k ρ z z' π π' f hloc hequiv
  have hUW : ∀ {w : Fin (2 * ρ + k + 1) → ℂ} {h : Mx k ρ}, h ∈ UWset k ρ w → h ∈ Glev k ρ (Fin.last ρ) :=
    fun hh => ⟨hh.1, fun a _ => hh.2.1 a⟩
  refine ⟨⟨fun c g => if (c, g) ∈ DomR k ρ z z' then f g else 0, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = 0
    exact if_neg hx
  · intro x₀ hx₀
    obtain ⟨hΩ, hG, hpos⟩ := hx₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hloc x₀.2 hG hpos
    refine ⟨OmX ρ ×ˢ (U ∩ {g | 0 < GGl k ρ z z' g}), fun x => F x.2, ?_, ?_, ?_, ?_⟩
    · exact (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX ρ).prod
        (hU.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k ρ z z')))
    · exact ⟨hΩ, hgU, hpos⟩
    · exact hF.comp contDiff_snd.contDiffOn (fun x hx => hx.2.1)
    · intro x hx hxG
      have hxD : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hx.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = F x.2
      rw [if_pos hxD]
      exact hFe x.2 hx.2.1 hxG
  · intro x hx h hh h' hh'
    obtain ⟨hΩ, hG, hpos⟩ := hx
    have hD : (x.1, h * x.2 * h') ∈ DomR k ρ z z' :=
      ⟨hΩ, Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (hUW hh) hG) (hUW hh'),
        by rw [Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh hh']; exact hpos⟩
    have hD0 : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hΩ, hG, hpos⟩
    show (if (x.1, h * x.2 * h') ∈ DomR k ρ z z' then f (h * x.2 * h') else 0) =
      π h ∘SL (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) ∘SL π' h'
    rw [if_pos hD, if_pos hD0]
    exact hequiv x.2 hG hpos h hh h' hh'
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = f x.2
    exact if_pos hx

/- English proof (translation)
Introduce `r h hh v`. Unfold `PBQ.zxH`. Rewrite using `[Matrix.det_reindex_self, Matrix.det_mul]`. Conclude with `mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (fun a => Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt))`.
-/
theorem determinant_vanishing_holds : ZxDet := by
  intro r h hh v
  unfold PBQ.zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero
    (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (fun a => Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt))

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `CutEX.residue_top_exceptional`.
-/
theorem residue_top_exceptional_level : CutEX.ResTop := CutEX.residue_top_exceptional
/- English proof (translation)
The claim follows from `CutEX.radial_extension_holds`.
-/
theorem radial_extension_exceptional : CutEX.RadExt := CutEX.radial_extension_holds
/- English proof (translation)
The claim follows from `CutEX.radial_of_function_holds`.
-/
theorem radial_of_function_exceptional : CutEX.RadOfFun := CutEX.radial_of_function_holds
/- English proof (translation)
The claim follows from `CutEX.determinant_vanishing_holds`.
-/
theorem determinant_exceptional_holds : CutEX.ZxDet := CutEX.determinant_vanishing_holds

end Formalism.FourierDecayAlt.P
