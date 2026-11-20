import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGridsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨CF1, h1⟩` from `hP`. Take `⟨CF2, h2⟩` from `hQ`. Use `⟨max CF1 CF2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C1, x1, g1⟩` from `h1 ε CF (le_of_max_le_left hCF)`. Take `⟨C2, x2, g2⟩` from `h2 ε CF (le_of_max_le_right hCF)`.

Conclude with `⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G) (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩`.
-/
private theorem gBig_both {P Q S : GP} (hP : GBig P) (hQ : GBig Q)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ
    (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G)
    (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩

/- English proof (translation)
Establish `hv` using `hX.isVac`. Establish `hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t)`. Establish `h` using `(hX.weil t).hecT`. Rewrite using `[← inv_div]`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `continuous_inv.comp h.1`. Use `show ((β t / α t) _)⁻¹ = 1`. Rewrite using `[h.2 x, inv_one]`. Establish `hI : X.ideal S t ≠ ⊥`. Unfold `Tri.ideal`.

Rewrite using `[← Ideal.zero_eq_bot]`. Use `Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot]`. Conclude with `w.ne_bot`. Take `⟨f₁, h1, h1t⟩` from `GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac hX.rigA hX.rigW hν (hX.idem t) hI hv`.

Establish `heq : X.f t = f₁`. Take `⟨⟨Tm, hT⟩, hall⟩` from `hX.fst t`. Rewrite using `[hall Tm hT, h1.2 Tm hT]`. Establish `hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t)` using `heq ▸ h1t`. Use `⟨hft, fun τ => ?_⟩` and prove the remaining obligations.

Establish `ho` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)`. Establish `hF` using `GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq (hX.fst t) hv.2.theta hft (hv.2.fock τ)`. Rewrite using `[hA τ, hW τ]`. Conclude with `hF`.
-/
private theorem fst_fin {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW) (hA : ∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ)
    (hW : ∀ τ, FW.cart τ = X.rW.s τ) (hX : X.Is ψ θ α β νH S) (t : T) : GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hA τ, hW τ]
  exact hF

/- English proof (translation)
Establish `ho` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)`. Establish `hth : IsThetaFunO ψ A' WW (X.f' t)` using `GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta`. Use `⟨hth, fun τ => ?_⟩` and prove the remaining obligations. Establish `hF` using `GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)`. Rewrite using `[hA' τ, hW τ]`.

Conclude with `hF`.
-/
private theorem snd_fin {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (hA' : ∀ τ, (GlobalTheory.SquareComm.frSgn false FA').cart τ = X.rA'.s τ)
    (hW : ∀ τ, FW.cart τ = X.rW.s τ) (hI : X.Is ψ θ α β νH S) (t : T) : GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t) := by
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [hA' τ, hW τ]
  exact hF

open GlobalTheory.StageDict in
/- English proof (translation)
Use `gBig_both GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_` and prove the remaining obligations. Introduce `D T Lc sc G μ₀ C x b _ hinf hram W i j p q A A' WW X hX`. Take `⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩` from `hX`. Take `⟨a, b, hab⟩` from `hinf W i j`. Establish `hsz` using `stage_sizes i j hp hq hrA hrA'`.

Establish `hrk : WW.rank = A.rank + A'.rank` using `hXi.rank.symm`. Establish `e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ` using `cart_frSgn_true_rigFr X.rA hXi.rigA`. Establish `e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ` using `cart_frSgn_false_rigFr X.rA' hXi.rigA'`. Establish `e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ` using `cart_rigFr X.rW hXi.rigW`. Use `⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, hnA, hnA', hnW, fun t => ⟨?_, fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩, fst_fin X _ _ _ _ _ _ _ _ e1 e2 hXi t, snd_fin X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩` and prove the remaining obligations.

Use `{ hecA := (hXi.weil' t).hecS hecB := (hXi.weil t).hecS resA := (hXi.weil' t).resS resB := (hXi.weil t).resS rank := hrk even := by rw [hrk]; exact hsz.1 sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩ gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩ r …` and prove the remaining obligations. Establish `h1` using `(hab t τ).2.2`. Establish `h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ)`. Conclude with `(hrk ▸ hsz.2.2.2)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `P g h`. Establish `f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ` using `funext e1`. Establish `f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s` using `funext e2`. Establish `f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B` using `funext (onb_rigFr X.rA hXi.rigA)`. Establish `f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B` using `funext (onb_rigFr X.rW hXi.rigW)`.

Unfold `GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker`. Rewrite using `[f1, f2, f3, f4]`. Introduce `P g h`. Establish `f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s` using `funext e1'`. Establish `f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s` using `funext e2`.

Establish `f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B` using `funext (onb_rigFr X.rA' hXi.rigA')`. Establish `f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B` using `funext (onb_rigFr X.rW hXi.rigW)`. Unfold `GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'`. Rewrite using `[f1, f2, f3, f4]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.T.towerStage_seesawDictionary_framesSignatures : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
  GlobalTheory.SqTower.IsStageC W i j p q X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) (A.rank - p) p) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) (A'.rank - q) q) ∧
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) (WW.rank - (p + q)) (p + q)) ∧
    ∀ t : T, GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_both GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_
  intro D T Lc sc G μ₀ C x b _ hinf hram W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hsz := stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  have e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ := cart_frSgn_true_rigFr X.rA hXi.rigA
  have e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ := cart_frSgn_false_rigFr X.rA' hXi.rigA'
  have e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ := cart_rigFr X.rW hXi.rigW
  refine ⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, hnA, hnA', hnW, fun t => ⟨?_,
    fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    fst_fin X _ _ _ _ _ _ _ _ e1 e2 hXi t, snd_fin X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩
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
