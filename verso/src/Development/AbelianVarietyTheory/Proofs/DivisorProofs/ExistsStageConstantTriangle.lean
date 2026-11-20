import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingFactorStageStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

/- English proof (translation)
Take `⟨F₁, h₁⟩` from `h₁`. Take `⟨F₂, h₂⟩` from `h₂`. Take `⟨F₃, h₃⟩` from `h₃`. Use `⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C₁, x₁, k₁⟩` from `h₁ ε CF (le_trans (le_max_left _ _) hCF)`.

Take `⟨C₂, x₂, k₂⟩` from `h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)`. Take `⟨C₃, x₃, k₃⟩` from `h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)`. Use `⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩` and prove the remaining obligations. Conclude with `k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G`. Conclude with `k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G`.

Conclude with `k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G`.
-/
theorem gBig_of₃ {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

/- English proof (translation)
Introduce `hP hK hM`. Use `gBig_of₃ (GlobalTheory.T.weil_top_grid_stage_exists hP) (GlobalTheory.T.exists_factor_of_stage_triangle hP hK hM) (GlobalTheory.T.exists_nonvanishing_factor_stage hP hK hM) ?_` and prove the remaining obligations. Introduce `D T Lc sc G μ₀ C x b hex hfac hcmp W S hstd hN ρ i j`. Take `⟨X, hT, hX⟩` from `hex W i j`. Take `⟨lam, hl⟩` from `hfac W S hstd hN i j (pp D j) (qq D j) _ _ _ X hX`.

Take `⟨κ, hκ, hc⟩` from `hcmp W S hstd hN ρ i j X lam hT hX hl`. Use `haveI : Nonempty T := ⟨μ₀⟩`. Conclude with `⟨_, _, _, X, lam, κ, hX, hl.isConst, hκ, hc⟩`.
-/
theorem top_stage : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m), ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c κ : T → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (pp D j) (qq D j) X ∧ X.IsConst W.ψ W.θ c ∧
      (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * c t := by
  intro hP hK hM
  refine gBig_of₃ (GlobalTheory.T.weil_top_grid_stage_exists hP) (GlobalTheory.T.exists_factor_of_stage_triangle hP hK hM) (GlobalTheory.T.exists_nonvanishing_factor_stage hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hex hfac hcmp W S hstd hN ρ i j
  obtain ⟨X, hT, hX⟩ := hex W i j
  obtain ⟨lam, hl⟩ := hfac W S hstd hN i j (pp D j) (qq D j) _ _ _ X hX
  obtain ⟨κ, hκ, hc⟩ := hcmp W S hstd hN ρ i j X lam hT hX hl
  haveI : Nonempty T := ⟨μ₀⟩
  exact ⟨_, _, _, X, lam, κ, hX, hl.isConst, hκ, hc⟩

end GlobalTheory.SqTower

end
