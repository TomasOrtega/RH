import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Introduce `D V A Λ h`. Take `⟨hlat, hdual⟩` from `h`. Establish `hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v))` using `fun v => A.fr_unit _`. Use `⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v) P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹ unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v) spec := ?_ Λ := Λ Λ_fg := hlat.fg Λ_span := hlat.span_eq_top Λ_dual := ?_ }, rfl, fun τ => ?_⟩` and prove the remaining obligations. Introduce `v set τ := (Formalism.L2.Host.tauPl D).symm v`.

Establish `hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ`. Rewrite using `[A.fr_gram τ]`. Both sides reduce to the same expression. Establish `hd : IsUnit (A.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (hf v)`. Establish `hdH : IsUnit ((A.fr τ)ᴴ).det`.

Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `hd.star`. Rewrite using `[hg, Matrix.conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Formalism.REAL.Jm (A.ε τ) := by`. Rewrite using `[Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]`. Introduce `x`. Rewrite using `[hdual x]`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations.

Unfold `Formalism.UG.hform`. Simplify using `only [RingHom.mem_range, starRingEnd_apply]`. Simplify using the standard rewrite rules.
-/
theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hlat.span_eq_top
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
