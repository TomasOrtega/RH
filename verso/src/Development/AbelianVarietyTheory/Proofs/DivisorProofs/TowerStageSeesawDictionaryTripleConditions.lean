import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumRiggedFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleSecondFiniteDatumIsFiniteRigging
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGridsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr

/- English proof (translation)
Take `⟨CF1, h1⟩` from `hP`. Take `⟨CF2, h2⟩` from `hQ`. Use `⟨max CF1 CF2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C1, x1, g1⟩` from `h1 ε CF (le_of_max_le_left hCF)`. Take `⟨C2, x2, g2⟩` from `h2 ε CF (le_of_max_le_right hCF)`.

Conclude with `⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G) (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩`.
-/
theorem gBig_two {P Q S : GP} (hP : GBig P) (hQ : GBig Q)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      P G μ₀ C x b → Q G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _
    (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G)
    (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩

/- English proof (translation)
Use `gBig_two GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_` and prove the remaining obligations. Introduce `D T Lc sc G μ₀ C x b hinf hram W i j p q A A' WW X hX`. Take `⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩` from `hX`. Take `⟨a, b, hab⟩` from `hinf W i j`. Establish `hsz` using `stage_sizes i j hp hq hrA hrA'`.

Establish `hrk : WW.rank = A.rank + A'.rank` using `hXi.rank.symm`. Establish `e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ` using `cart_frSgn_true_rigFr X.rA hXi.rigA`. Establish `e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ` using `cart_frSgn_false_rigFr X.rA' hXi.rigA'`. Establish `e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ` using `cart_rigFr X.rW hXi.rigW`. Use `⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, fun t => ⟨?_, fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩, GlobalTheory.T.seesawTriple_firstFiniteDatum_riggedFrames X _ _ _ _ _ _ _ _ e1 e2 hXi t, GlobalTheory.T.seesawTriple_secondFiniteDatum_isFinite_rigging X _ …` and prove the remaining obligations.

Use `{ hecA := (hXi.weil' t).hecS hecB := (hXi.weil t).hecS resA := (hXi.weil' t).resS resB := (hXi.weil t).resS rank := hrk even := by rw [hrk]; exact hsz.1 sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩ gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩ r …` and prove the remaining obligations. Establish `h1` using `(hab t τ).2.2`. Establish `h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ)`. Conclude with `(hrk ▸ hsz.2.2.2)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `P g h`. Establish `f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ` using `funext e1`. Establish `f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s` using `funext e2`. Establish `f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B` using `funext (onb_rigFr X.rA hXi.rigA)`. Establish `f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B` using `funext (onb_rigFr X.rW hXi.rigW)`.

Unfold `GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker`. Rewrite using `[f1, f2, f3, f4]`. Introduce `P g h`. Establish `f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s` using `funext e1'`. Establish `f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s` using `funext e2`.

Establish `f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B` using `funext (onb_rigFr X.rA' hXi.rigA')`. Establish `f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B` using `funext (onb_rigFr X.rW hXi.rigW)`. Unfold `GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'`. Rewrite using `[f1, f2, f3, f4]`. Both sides reduce to the same expression.
-/
theorem dictionary_at_stage : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
      GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
        HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_two GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_
  intro D T Lc sc G μ₀ C x b hinf hram W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hsz := stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  have e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ := cart_frSgn_true_rigFr X.rA hXi.rigA
  have e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ := cart_frSgn_false_rigFr X.rA' hXi.rigA'
  have e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ := cart_rigFr X.rW hXi.rigW
  refine ⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, fun t => ⟨?_,
    fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    GlobalTheory.T.seesawTriple_firstFiniteDatum_riggedFrames X _ _ _ _ _ _ _ _ e1 e2 hXi t, GlobalTheory.T.seesawTriple_secondFiniteDatum_isFinite_rigging X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩
  · refine
      { hecA := (hXi.weil' t).hecS
        hecB := (hXi.weil t).hecS
        resA := (hXi.weil' t).resS
        resB := (hXi.weil t).resS
        rank := hrk
        even := by rw [hrk]; exact hsz.1
        sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩
        ram := hram W i j p q A A' WW X ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ t }
    have h1 := (hab t τ).2.2
    have h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast (hrk ▸ hsz.2.2.2)
    linarith
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ := funext e1
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B := funext (onb_rigFr X.rA hXi.rigA)
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [f1, f2, f3, f4]
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s := funext e1'
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B := funext (onb_rigFr X.rA' hXi.rigA')
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [f1, f2, f3, f4]
    rfl

end GlobalTheory.StageDict

end
