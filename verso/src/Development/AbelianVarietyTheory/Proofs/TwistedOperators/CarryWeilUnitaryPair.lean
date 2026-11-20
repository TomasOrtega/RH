import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOverOfClauses
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanInvolutionEqOfCommute
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx.CarryWeil

open GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Break down `Y with ⟨_ | i, j⟩ | i | j` into its components or cases. Take `⟨-, rfl⟩` from `hY`. Establish `e : G.V (.grid 0 D.R.m) = D.sp.X'` using `congrArg LSp.sp (colY_m L)`. Rewrite using `[e]`. Conclude with `GlobalTheory.Hk3.StepX.gram_posDef_X τ`.

Take `⟨hi, rfl⟩` from `hY`. Establish `hV` using `G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)`. Use `hV.sigOK (tauE D τ)` as an intermediate fact. Rewrite `this` using `[hV.sig]`. Simplify using `only [Node.neg, Nat.sub_self, Nat.zero_div] at this`.

Conclude with `GlobalTheory.DefiniteQuotient.posDef_of_signature this`. Conclude with `hY.elim`. Establish `hV` using `G.isV (X := .top j) hY (fun j h => by cases h)`. Use `hV.sigOK (tauE D τ)` as an intermediate fact. Rewrite `this` using `[hV.sig]`.

Simplify using `only [Node.neg] at this`. Conclude with `GlobalTheory.DefiniteQuotient.posDef_of_signature this`.
-/
theorem gram_posDef_def (G : GridData L sc) {Y : Node} (hY : DefNode D.R.m Y) (τ : D.what₂.Tau) :
    (gramAt D (G.V Y) τ).PosDef := by
  rcases Y with ⟨_ | i, j⟩ | i | j
  · obtain ⟨-, rfl⟩ := hY
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact GlobalTheory.Hk3.StepX.gram_posDef_X τ
  · obtain ⟨hi, rfl⟩ := hY
    have hV := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg, Nat.sub_self, Nat.zero_div] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  · exact hY.elim
  · have hV := G.isV (X := .top j) hY (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hr : Y.InRange D.R.m`. Apply the tactic sequence `rcases Y with ⟨i, j⟩ | i | j <;> simp only [DefNode, Node.InRange] at hY ⊢ <;> omega`. Establish `hpos` using `gram_posDef_def G hY τ`. Conclude with `GlobalTheory.StdUnn.isCartanInv_eq_of_commute _ _ _ _ (W.cart_is Y hr τ) ⟨Matrix.mul_one 1, by simp, by simpa using hpos⟩ (by simp)`.
-/
theorem cart_def (G : GridData L sc) (W : G.Weil) {Y : Node} (hY : DefNode D.R.m Y) : W.cart Y = fun _ => 1 := by
  funext τ
  have hr : Y.InRange D.R.m := by
    rcases Y with ⟨i, j⟩ | i | j <;> simp only [DefNode, Node.InRange] at hY ⊢ <;> omega
  have hpos := gram_posDef_def G hY τ
  exact GlobalTheory.StdUnn.isCartanInv_eq_of_commute _ _ _ _ (W.cart_is Y hr τ) ⟨Matrix.mul_one 1, by simp, by simpa using hpos⟩
    (by simp)

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem heq_one {V V' : HSp D} (h : V' = V) :
    HEq (fun _ : D.what₂.Tau => (1 : Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
      (fun _ : D.what₂.Tau => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) := by
  subst h; rfl

/- English proof (translation)
Substitute `h1 h2 h3` using the available equality. Both sides reduce to the same expression.
-/
theorem attChr_congr {C : Type} [CommGroup C] {a a' b b' : C} {n n' : ℕ} (h1 : a = a') (h2 : b = b') (h3 : n = n') :
    Formalism.IndefR.Lift.attChr a b n = Formalism.IndefR.Lift.attChr a' b' n' := by
  subst h1 h2 h3; rfl

section Transport

open GlobalTheory.Mem

/- English proof (translation)
Take `⟨B, C, Wr, V, Sg, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', Sg', N', Gj'⟩` from `X'`. Consider the cases of `B`. Consider the cases of `B'`. Simplify using `only at h`.

Substitute `h` using the available equality. Take `rfl` from `eq_of_heq hψ`. Take `rfl` from `eq_of_heq hS`. Take `rfl` from `eq_of_heq hT`. Take `rfl` from `eq_of_heq h1`.

Take `rfl` from `eq_of_heq h2`. Use `⟨ω, ?_, HEq.rfl⟩` and prove the remaining obligations. Conclude with `{ std := (by with_unfolding_all exact (hw.std :)) hecS := (by with_unfolding_all exact (hw.hecS :)) hecT := (by with_unfolding_all exact (hw.hecT :)) resS := (by with_unfolding_all exact (hw.resS :)) resT := (by with_unfolding_all exact (hw.resT :)) om_pres := fun p f hf =>`. Establish `r` using `hw.om_pres p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩`. Use the proof step `⟨(by with_unfolding_all exact (r.quasi :)), (by with_unfolding_all exact (r.level :)), (by with_unfolding_all exact (r.cont :)), (by with_unfolding_all exact (r.smooth :))⟩`.

Use `om_heis := fun g h w₀ f hf => hw.om_heis g h w₀ f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩`. Use `om_aut := fun γ hγ γ' hγ' f hf => hw.om_aut γ hγ γ' hγ' f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩`. Use `om_cont := fun f hf => hw.om_cont f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩`. Use `om_unit := fun μ 𝓕 hμ h𝓕 p f hf => hw.om_unit μ 𝓕 hμ h𝓕 p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩`. Use `om_split := fun e he g h hg hh x y hx hy => by`.

Take `⟨r, hr, hℓ⟩` from `hw.om_split e he g h hg hh x y hx hy`. Conclude with `⟨r, hr, fun ℓ hℓ' f hf => hℓ ℓ (fun u hu f' hf' => hℓ' u hu f' ⟨(by with_unfolding_all exact (hf'.quasi :)), (by with_unfolding_all exact (hf'.level :)), (by with_unfolding_all exact (hf'.cont :)), (by with_unfolding_all exact (hf'.smooth :))⟩) f ⟨(by with_unfolding_all exact (hf …`.
-/
theorem exists_om_tr {X X' : Stages} (h : X'.B.toPre = X.B.toPre) {ψ : AddChar (AF X.toD7.host.F) ℂ} {S T : HSp X.toD7}
    {χS χT : (AE X.toD7)ˣ →* Circle} {ω : GA X.toD7 S × GA X.toD7 T →* Module.End ℂ (WO S T → ℂ)}
    {ψ' : AddChar (AF X'.toD7.host.F) ℂ} {S' T' : HSp X'.toD7} {χS' χT' : (AE X'.toD7)ˣ →* Circle}
    (hψ : HEq ψ' ψ) (hS : HEq S' S) (hT : HEq T' T) (h1 : HEq χS' χS) (h2 : HEq χT' χT)
    (hw : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω' : GA X'.toD7 S' × GA X'.toD7 T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ' S' T' χS' χT' ω' ∧ HEq ω' ω := by
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B; cases B'
  dsimp only at h
  subst h
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  refine ⟨ω, ?_, HEq.rfl⟩
  exact
    { std := (by with_unfolding_all exact (hw.std :))
      hecS := (by with_unfolding_all exact (hw.hecS :))
      hecT := (by with_unfolding_all exact (hw.hecT :))
      resS := (by with_unfolding_all exact (hw.resS :))
      resT := (by with_unfolding_all exact (hw.resT :))
      om_pres := fun p f hf =>
        have r := hw.om_pres p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
        ⟨(by with_unfolding_all exact (r.quasi :)), (by with_unfolding_all exact (r.level :)), (by with_unfolding_all exact (r.cont :)), (by with_unfolding_all exact (r.smooth :))⟩
      om_heis := fun g h w₀ f hf => hw.om_heis g h w₀ f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_aut := fun γ hγ γ' hγ' f hf => hw.om_aut γ hγ γ' hγ' f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_cont := fun f hf => hw.om_cont f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_unit := fun μ 𝓕 hμ h𝓕 p f hf => hw.om_unit μ 𝓕 hμ h𝓕 p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_split := fun e he g h hg hh x y hx hy => by
        obtain ⟨r, hr, hℓ⟩ := hw.om_split e he g h hg hh x y hx hy
        exact ⟨r, hr, fun ℓ hℓ' f hf => hℓ ℓ (fun u hu f' hf' => hℓ' u hu f' ⟨(by with_unfolding_all exact (hf'.quasi :)), (by with_unfolding_all exact (hf'.level :)), (by with_unfolding_all exact (hf'.cont :)), (by with_unfolding_all exact (hf'.smooth :))⟩) f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩⟩ }

end Transport

end GlobalTheory.RowEx.CarryWeil

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowEx.CarryWeil in

/- English proof (translation)
Introduce `hW X X' T T' L Γ _ _ Pl0 A Ks _ _ _ R μ₀ ι hL hch hmod sc G G' hG W`. Take `⟨W1, hW1⟩` from `GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hW R hL.is' hch hmod sc G'`. Establish `hm : X'.toD7.R.m = X.toD7.R.m`. Establish `hpre` using `hL.pre`. Take `⟨B, C, Wr, V, S, N, Gj⟩` from `X`.

Take `⟨B', C', Wr', V', S', N', Gj'⟩` from `X'`. Consider the cases of `B`. Consider the cases of `B'`. Simplify using `only at hpre`. Substitute `hpre` using the available equality.

Both sides reduce to the same expression. Establish `F1 : HEq W1.ψ W.ψ`. Establish `hpre` using `hL.pre`. Take `⟨B, C, Wr, V, S, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', S', N', Gj'⟩` from `X'`.

Consider the cases of `B`. Consider the cases of `B'`. Simplify using `only at hpre`. Substitute `hpre` using the available equality. Conclude with `heq_of_eq ((GlobalTheory.StdAdelicChar.existsUnique_isStdChar _ (-1) (Or.inr rfl)).unique W1.ψ_std ((by with_unfolding_all exact (W.ψ_std :))))`.

Establish `F2 : HEq W1.θ W.θ`. Establish `hpre` using `hL.pre`. Take `⟨B, C, Wr, V, S, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', S', N', Gj'⟩` from `X'`. Consider the cases of `B`.

Consider the cases of `B'`. Simplify using `only at hpre`. Substitute `hpre` using the available equality. Conclude with `heq_of_eq ((GlobalTheory.SmoothForms.RealPts.realPoints _).1 _ _ W1.θ_is ((by with_unfolding_all exact (W.θ_is :))))`. Establish `F3 : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W1.cart Y) (W.cart Y)`.

Introduce `Y hY`. Rewrite using `[cart_def G' W1 hY, cart_def G W (hm ▸ hY)]`. Establish `hV : HEq (G'.V Y) (G.V Y)`. Break down `Y with ⟨_ | i, j⟩ | i | j` into its components or cases. Take `⟨-, rfl⟩` from `hY`.

Establish `hpre` using `hL.pre`. Take `⟨B, C, Wr, V, S, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', S', N', Gj'⟩` from `X'`. Consider the cases of `B`. Consider the cases of `B'`.

Simplify using `only at hpre`. Substitute `hpre` using the available equality. Conclude with `heq_of_eq ((congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm)`. Conclude with `(hG.grid i j).1`. Conclude with `hY.elim`.

Conclude with `(hG.top j).1`. Establish `hpre` using `hL.pre`. Take `⟨B, C, Wr, V, S, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', S', N', Gj'⟩` from `X'`. Consider the cases of `B`.

Consider the cases of `B'`. Simplify using `only at hpre`. Substitute `hpre` using the available equality. Conclude with `heq_one (eq_of_heq hV)`. Establish `F4 : ∀ p, DefPair X'.toD7.R.m p → ∃ ω, IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω ∧ HEq ω (W.om (mapPair ι p))`.

Introduce `p hp`. Establish `hr : (mapPair ι p).InRange X.toD7.R.m`. Rewrite using `[← hm]`. Apply the tactic sequence `rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;>`. Apply the tactic sequence `simp only [DefPair, mapPair, Pair.InRange, Pair.big, Node.InRange] at hp ⊢ <;> omega`.

Establish `key : HEq (G'.pS p) (G.pS (mapPair ι p)) ∧ HEq (G'.pT p) (G.pT (mapPair ι p)) ∧ HEq (G'.chrS p) (G.chrS (mapPair ι p)) ∧ HEq (G'.chrT p) (G.chrT (mapPair ι p))`. Establish `eta` using `hL.is.eta`. Establish `eta'` using `hL.is'.eta`. Establish `mu0` using `hL.is.mu0`. Establish `mu0'` using `hL.is'.mu0`.

Establish `xi` using `hL.is.xi`. Establish `xi'` using `hL.is'.xi`. Establish `hxi` using `hL.xi`. Take `⟨f, f', hff, hC, hC'⟩` from `hL.C`. Establish `hpre` using `hL.pre`.

Take `⟨B, C, Wr, V, S, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', S', N', Gj'⟩` from `X'`. Consider the cases of `B`. Consider the cases of `B'`. Simplify using `only at hpre`.

Substitute `hpre` using the available equality. Take `rfl` from `eq_of_heq hff`. Rewrite `eta`, `mu0` using `[hC]`. Rewrite `eta'`, `mu0'` using `[hC']`. Establish `eEta : R.toLevCh.eta = L.eta` using `(GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ eta' ((by with_unfolding_all exact (eta :)))`.

Break down `p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩` into its components or cases. Take `⟨hi, hj⟩` from `hp`. Establish `hS1 : G'.V (.grid (i + 1) j) = G.V (.grid (i + 1) j)` using `eq_of_heq (hG.grid i j).1`. Establish `hT1 : G'.V (.grid i j) = G.V (.grid i j)`. Consider the cases of `i with`.

Consider the case `zero`. Substitute `hj` using the available equality. Conclude with `(congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm`. Consider the case `succ k => exact eq_of_heq (hG.grid k j).1`. Establish `ech` using `eq_of_heq hG.chi`.

Conclude with `⟨heq_of_eq (congrArg negSp hS1), heq_of_eq hT1, heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => (negSp V).rank) hS1)), heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩`. Conclude with `hp.elim`. Conclude with `hp.elim`. Establish `hj` using `Nat.lt_of_succ_le hp`. Establish `emu : R.toLevCh.mu0 (j + 1) = L.mu0 (j + 1)` using `(GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (mu0' ⟨j, hj⟩) ((by with_unfolding_all exact ((mu0 ⟨j, hj⟩) :)))`.

Establish `exi : R.toLevCh.xi t = L.xi (ι t)`. Establish `h1` using `xi (ι t)`. Establish `h2` using `xi' t`. Rewrite `h2` using `[eq_of_heq (hxi t)]`. Conclude with `(GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ h2 ((by with_unfolding_all exact (h1 :)))`.

Establish `hS1 : G'.V (.top j) = G.V (.top j)` using `eq_of_heq (hG.top j).1`. Establish `hT1 : G'.V (.top (j + 1)) = G.V (.top (j + 1))` using `eq_of_heq (hG.top (j + 1)).1`. Establish `emu' : R.toLevCh.mu t (j + 1) = L.mu (ι t) (j + 1)` using `congrArg₂ (· * ·) emu exi`. Conclude with `⟨heq_of_eq hS1, heq_of_eq hT1, heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hS1)), heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩`. Conclude with `exists_om_tr hL.pre F1 key.1 key.2.1 key.2.2.1 key.2.2.2 (W.om_is (mapPair ι p) hr)`.

Establish `key : ∀ p : Pair T', ∃ ω, (p.InRange X'.toD7.R.m → IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω) ∧ (DefPair X'.toD7.R.m p → HEq ω (W.om (mapPair ι p))) ∧ (¬ DefPair X'.toD7.R.m p → ω = W1.om p)`. Introduce `p`. Distinguish the cases in `hp : DefPair X'.toD7.R.m p`. Take `⟨ω, h1, h2⟩` from `F4 p hp`. Conclude with `⟨ω, fun _ => h1, fun _ => h2, fun h => absurd hp h⟩`.

Conclude with `⟨W1.om p, W1.om_is p, fun h => absurd h hp, fun _ => rfl⟩`. Use `choose om hom hdef hnd using key`. Use `⟨{ W1 with om := om, om_is := hom }, ?_, F1, F2, F3, hdef⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8⟩` from `hW1`. Use `⟨a1, a2, a3, a4, a5, a6, fun t k hk => ?_, fun t k hk => ?_⟩` and prove the remaining obligations.

Use `show HEq (om (.mu t 0 k)) _`. Rewrite using `[hnd (.mu t 0 k) (fun h => h)]`. Conclude with `a7 t k hk`. Use `show HEq (om (.mu t 0 k)) _`. Rewrite using `[hnd (.mu t 0 k) (fun h => h)]`.

Conclude with `a8 t k hk`.
-/
theorem GlobalTheory.RowEx.carryW_of_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → CarryW := by
  intro hW X X' T T' L Γ _ _ Pl0 A Ks _ _ _ R μ₀ ι hL hch hmod sc G G' hG W
  obtain ⟨W1, hW1⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hW R hL.is' hch hmod sc G'
  have hm : X'.toD7.R.m = X.toD7.R.m := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    rfl
  have F1 : HEq W1.ψ W.ψ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.StdAdelicChar.existsUnique_isStdChar _ (-1) (Or.inr rfl)).unique W1.ψ_std ((by with_unfolding_all exact (W.ψ_std :))))
  have F2 : HEq W1.θ W.θ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.SmoothForms.RealPts.realPoints _).1 _ _ W1.θ_is ((by with_unfolding_all exact (W.θ_is :))))
  have F3 : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W1.cart Y) (W.cart Y) := by
    intro Y hY
    rw [cart_def G' W1 hY, cart_def G W (hm ▸ hY)]
    have hV : HEq (G'.V Y) (G.V Y) := by
      rcases Y with ⟨_ | i, j⟩ | i | j
      · obtain ⟨-, rfl⟩ := hY
        have hpre := hL.pre
        obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
        obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
        cases B; cases B'
        dsimp only at hpre
        subst hpre
        exact heq_of_eq ((congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm)
      · exact (hG.grid i j).1
      · exact hY.elim
      · exact (hG.top j).1
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_one (eq_of_heq hV)
  have F4 : ∀ p, DefPair X'.toD7.R.m p → ∃ ω, IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω ∧
      HEq ω (W.om (mapPair ι p)) := by
    intro p hp
    have hr : (mapPair ι p).InRange X.toD7.R.m := by
      rw [← hm]
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;>
        simp only [DefPair, mapPair, Pair.InRange, Pair.big, Node.InRange] at hp ⊢ <;> omega
    have key : HEq (G'.pS p) (G.pS (mapPair ι p)) ∧ HEq (G'.pT p) (G.pT (mapPair ι p)) ∧
        HEq (G'.chrS p) (G.chrS (mapPair ι p)) ∧ HEq (G'.chrT p) (G.chrT (mapPair ι p)) := by
      have eta := hL.is.eta
      have eta' := hL.is'.eta
      have mu0 := hL.is.mu0
      have mu0' := hL.is'.mu0
      have xi := hL.is.xi
      have xi' := hL.is'.xi
      have hxi := hL.xi
      obtain ⟨f, f', hff, hC, hC'⟩ := hL.C
      have hpre := hL.pre
      obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
      obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
      cases B; cases B'
      dsimp only at hpre
      subst hpre
      obtain rfl := eq_of_heq hff
      rw [hC] at eta mu0
      rw [hC'] at eta' mu0'
      have eEta : R.toLevCh.eta = L.eta := (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ eta' ((by with_unfolding_all exact (eta :)))
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
      · obtain ⟨hi, hj⟩ := hp
        have hS1 : G'.V (.grid (i + 1) j) = G.V (.grid (i + 1) j) := eq_of_heq (hG.grid i j).1
        have hT1 : G'.V (.grid i j) = G.V (.grid i j) := by
          cases i with
          | zero =>
            subst hj
            exact (congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm
          | succ k => exact eq_of_heq (hG.grid k j).1
        have ech := eq_of_heq hG.chi
        exact ⟨heq_of_eq (congrArg negSp hS1), heq_of_eq hT1,
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => (negSp V).rank) hS1)),
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
      · exact hp.elim
      · exact hp.elim
      · have hj := Nat.lt_of_succ_le hp
        have emu : R.toLevCh.mu0 (j + 1) = L.mu0 (j + 1) :=
          (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (mu0' ⟨j, hj⟩) ((by with_unfolding_all exact ((mu0 ⟨j, hj⟩) :)))
        have exi : R.toLevCh.xi t = L.xi (ι t) := by
          have h1 := xi (ι t)
          have h2 := xi' t
          rw [eq_of_heq (hxi t)] at h2
          exact (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ h2 ((by with_unfolding_all exact (h1 :)))
        have hS1 : G'.V (.top j) = G.V (.top j) := eq_of_heq (hG.top j).1
        have hT1 : G'.V (.top (j + 1)) = G.V (.top (j + 1)) := eq_of_heq (hG.top (j + 1)).1
        have emu' : R.toLevCh.mu t (j + 1) = L.mu (ι t) (j + 1) := congrArg₂ (· * ·) emu exi
        exact ⟨heq_of_eq hS1, heq_of_eq hT1,
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hS1)),
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
    exact exists_om_tr hL.pre F1 key.1 key.2.1 key.2.2.1 key.2.2.2 (W.om_is (mapPair ι p) hr)
  have key : ∀ p : Pair T', ∃ ω, (p.InRange X'.toD7.R.m →
      IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω) ∧
      (DefPair X'.toD7.R.m p → HEq ω (W.om (mapPair ι p))) ∧ (¬ DefPair X'.toD7.R.m p → ω = W1.om p) := by
    intro p
    by_cases hp : DefPair X'.toD7.R.m p
    · obtain ⟨ω, h1, h2⟩ := F4 p hp
      exact ⟨ω, fun _ => h1, fun _ => h2, fun h => absurd hp h⟩
    · exact ⟨W1.om p, W1.om_is p, fun h => absurd h hp, fun _ => rfl⟩
  choose om hom hdef hnd using key
  refine ⟨{ W1 with om := om, om_is := hom }, ?_, F1, F2, F3, hdef⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hW1
  refine ⟨a1, a2, a3, a4, a5, a6, fun t k hk => ?_, fun t k hk => ?_⟩
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a7 t k hk
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a8 t k hk

end
