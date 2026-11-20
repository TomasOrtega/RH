import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionCommutesOnGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopFormsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridSquareFlipSmallRouteEqInvSmulBigRouteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridPathCutAtSquareSwapRouteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenOppositeGridPathsAndDeterminedByEdgesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePathStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type}

/- English proof (translation)
The claim follows from `| [], γ, h => by cases h with | cons hp _ => exact hp | y :: l, γ, h => by cases h with | cons _ hc => exact passesThrough_of_canFlip l _ hc`.
-/
theorem passesThrough_of_canFlip {x : ℕ × ℕ} {r : List (ℕ × ℕ)} :
    ∀ (l : List (ℕ × ℕ)) (γ : List GlobalTheory.SplitFlip.Edge), GlobalTheory.SplitFlip.CanFlip γ (l ++ x :: r) →
      GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (l.foldl (fun γ y => GlobalTheory.SplitFlip.flipPath y.1 y.2 γ) γ)
  | [], γ, h => by cases h with | cons hp _ => exact hp
  | y :: l, γ, h => by
    cases h with
    | cons _ hc => exact passesThrough_of_canFlip l _ hc

/- English proof (translation)
Simplify using `only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at h`. Take `⟨i, hi, j, hj, rfl⟩` from `h`. Conclude with `⟨hi, hj⟩`.
-/
theorem lt_of_mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (h : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  exact ⟨hi, hj⟩

/- English proof (translation)
The claim follows from `| 0 => by simp | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_map_range f n, Finset.prod_range_succ]; simp`.
-/
theorem prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_map_range f n, Finset.prod_range_succ]; simp

/- English proof (translation)
Establish `: ∀ l : List ℕ, ((l.flatMap fun i => (List.range m).map fun j => (i, j)).map f).prod = (l.map fun i => ((List.range m).map fun j => f (i, j)).prod).prod`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_map, Function.comp_def]`.

Rewrite using `[flipOrder, this, prod_map_range]`. Conclude with `Finset.prod_congr rfl fun i _ => prod_map_range _ _`.
-/
theorem prod_flipOrder {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ × ℕ → M) :
    ((flipOrder m).map f).prod = ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, f (i, j) := by
  have : ∀ l : List ℕ, ((l.flatMap fun i => (List.range m).map fun j => (i, j)).map f).prod =
      (l.map fun i => ((List.range m).map fun j => f (i, j)).prod).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_map, Function.comp_def]
  rw [flipOrder, this, prod_map_range]
  exact Finset.prod_congr rfl fun i _ => prod_map_range _ _

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨Pg, hPg⟩` from `hD`. Use `choose z hz hPg using hPg`. Use `⟨(GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg).mapDomain GlobalTheory.FlipRun.toOpp, z, fun t => ⟨hz t, fun Φ => ?_⟩⟩` and prove the remaining obligations. Take `⟨τg, hRg, hg⟩` from `hPg t Φ`. Set `c' : ℕ × ℕ → ℂ` to `fun x => if h : x.1 < D.R.m ∧ x.2 < D.R.m then ch.c ⟨x.1, h.1⟩ ⟨x.2, h.2⟩ t else 1`.

Set `S : ℕ → ∀ w, (locGrid ch.G t w).PiLocalization₂` to `fun k w => (givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)`. Establish `hlev : ∀ k w, (S k w).level = givenLevel ch.G t w` using `fun k w => flips_level _ _ _ _ _ _ fun _ _ => rfl`. Establish `hpath : ∀ k w, (S k w).path = ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m)` using `fun k w => flips_path _ _ _ _ _ _`. Establish `hlen : (flipOrder D.R.m).length = D.R.m ^ 2` using `(canFlip_flipOrder D.R.m).2.1`. Establish `key : ∀ k, k ≤ D.R.m ^ 2 → ∃ p : Path T (.grid 0 D.R.m) (.grid D.R.m 0), GlobalTheory.FlipRun.OnGrid D.R.m t p ∧ GlobalTheory.FlipRun.edges p = ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m) ∧ ∃ τ : …`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Take `⟨⟨h1, h2⟩, -, -⟩` from `GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t`.

Use `⟨GlobalTheory.FunObj.givenPath t D.R.m, h1, by simpa using h2, τg, hRg, fun M hM y => ?_⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `hg M hM y`. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify `b` using `[GlobalTheory.FlipRun.flipsPolE]`. Consider the case `succ k ih`.

Introduce `hk`. Take `⟨p, hp, hedge, τ, hR, hI⟩` from `ih (by omega)`. Establish `hkl : k < (flipOrder D.R.m).length` using `by omega`. Use `set x := (flipOrder D.R.m)[k] with hx`. Establish `hxm : x ∈ flipOrder D.R.m` using `List.getElem_mem hkl`.

Take `⟨hi, hj⟩` from `lt_of_mem_flipOrder hxm`. Establish `htake : (flipOrder D.R.m).take (k + 1) = (flipOrder D.R.m).take k ++ [x]` using `List.take_succ_eq_append_getElem hkl`. Establish `hpass : GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (GlobalTheory.FlipRun.edges p)`. Rewrite using `[hedge]`. Establish `hc` using `(canFlip_flipOrder D.R.m).1`.

Rewrite `hc` using `[← List.take_append_drop k (flipOrder D.R.m), List.drop_eq_getElem_cons hkl]`. Conclude with `passesThrough_of_canFlip _ _ hc`. Take `⟨A, Bp, rfl, hA', hB', hN, hNe⟩` from `GlobalTheory.T.gridPath_cut_at_square_swap_route D.R.m t x.1 x.2 hi hj p hp hpass`. Establish `hT : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t x.1 x.2)).comp Bp)) (S k w).tensor` using `fun w hw => by`. Use `hE t Φ w hw k (by omega)` as an intermediate fact.

Rewrite `this` using `[hpath, ← hedge]`. Then use the resulting hypothesis. Establish `hS : ∀ w, (S (k + 1) w).tensor = (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w) (S k w).tensor` using `fun w => by`. Rewrite using `[← hlev k w]`. Use `show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (k + 1))).tensor = _`. Rewrite using `[htake]`.

Simplify using `only [GlobalTheory.SplitFlip.Grid.PiLocalization₂.flips, List.foldl_append, List.foldl_cons, List.foldl_nil]`. Both sides reduce to the same expression. Establish `hTb : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t x.1 x.2)).comp Bp)) ((locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w) (S k w).tensor)` using `fun w hw => by`. Use `hE t Φ w hw (k + 1) hk` as an intermediate fact. Rewrite using `[← hS w, hNe, hedge]`.

Establish `e2` using `hpath (k + 1) w`. Rewrite `e2` using `[htake, List.foldl_append]`. Establish `e3 : (S (k + 1) w).path = GlobalTheory.SplitFlip.flipPath x.1 x.2 (((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m))` using `e2`. Rewrite using `[← e3]`. Conclude with `this`.

Take `⟨τ', hR', hF⟩` from `GlobalTheory.T.gridSquareFlip_smallRoute_eq_inv_smul_bigRoute hL ch.W ch.S.B ch.rm t x.1 x.2 hi hj _ (hK _ _ t) (hA t ⟨x.1, hi⟩ ⟨x.2, hj⟩) A Bp hA' hB' (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ (fun w => (S k w).tensor) hT hTb hR`. Use `⟨(A.comp (routeBig t x.1 x.2)).comp Bp, hN, ?_, τ', ?_, fun M hM y => ?_⟩` and prove the remaining obligations. Rewrite using `[hNe, hedge, htake, List.foldl_append]`. Both sides reduce to the same expression. Establish `e : (fun w => (S (k + 1) w).tensor) = fun w => (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w) (S k w).tensor` using `funext hS`.

Rewrite using `[e]`. Conclude with `hR'`. Take `⟨hc1, hc2⟩` from `hI M hM y`. Take `⟨hn1, hn2⟩` from `hF M hM (hB t M hM) _ (hC t y) hc1`. Establish `ep : GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take (k + 1)) Pg = GlobalTheory.FlipRun.flipPolE ch.rm x.1 x.2 (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg)`.

Rewrite using `[htake, GlobalTheory.FlipRun.flipsPolE, GlobalTheory.FlipRun.flipsPolE, List.foldl_append]`. Both sides reduce to the same expression. Establish `ec : c' x = ch.c ⟨x.1, hi⟩ ⟨x.2, hj⟩ t` using `dif_pos ⟨hi, hj⟩`. Rewrite using `[ep]`. Use `⟨hn1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc2, hn2, smul_smul, htake, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ec]`. Use `congr 1`. Conclude with `(mul_inv _ _).symm.trans (by rw [mul_assoc])`. Take `⟨p, hp, hedge, τ, hR, hI⟩` from `key (D.R.m ^ 2) le_rfl`. Establish `htk : (flipOrder D.R.m).take (D.R.m ^ 2) = flipOrder D.R.m` using `List.take_of_length_le (by rw [hlen])`.

Take `⟨-, ⟨h1, h2⟩, h3⟩` from `GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t`. Establish `hp' : p = oppPath t D.R.m` using `h3 p _ hp h1 (by rw [hedge, h2, htk]; exact (canFlip_flipOrder D.R.m).2.2)`. Substitute `hp'` using the available equality. Establish `hTf : (fun w => (S (D.R.m ^ 2) w).tensor) = Tflip ch.W ch.S.B t Φ`. Use function extensionality and compare the values at `w`.

Use `show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (D.R.m ^ 2))).tensor = _`. Rewrite using `[htk]`. Both sides reduce to the same expression. Rewrite `hR` using `[hTf]`. Take `⟨τ', hτ', heq⟩` from `GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath ch.W ch.S.B ch.rm t Φ (GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg) τ hR`.

Establish `hprod : ((flipOrder D.R.m).map c').prod = cTot ch t`. Rewrite using `[prod_flipOrder, cTot, Finset.prod_range]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_range]`. Conclude with `Finset.prod_congr rfl fun j _ => dif_pos ⟨i.2, j.2⟩`.

Use `⟨τ', hτ', fun M hM y => ?_⟩` and prove the remaining obligations. Take `⟨hc1, hc2⟩` from `hI M hM y`. Rewrite `hc1`, `hc2` using `[htk, heq]`. Rewrite `hc2` using `[hprod]`. Conclude with `⟨hc1, hc2⟩`.
-/
theorem flipAt_of (hL : R.toLevCh.Is A.μ0) (ch : Choice R)
    (hA : ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t))
    (hB : ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t)
    (hC : ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y))
    (hD : ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum,
        ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m),
          GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧
          ∀ M : Vol ch.G, M.Is t → ∀ y,
            TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧
            thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) =
              (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y))
    (hE : ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 →
      (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
        ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path
        ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor)
    (hK : ∀ i j (t : T), ch.c i j t ≠ 0) : FlipAt ch := by
  obtain ⟨Pg, hPg⟩ := hD
  choose z hz hPg using hPg
  refine ⟨(GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg).mapDomain GlobalTheory.FlipRun.toOpp, z, fun t => ⟨hz t, fun Φ => ?_⟩⟩
  obtain ⟨τg, hRg, hg⟩ := hPg t Φ
  let c' : ℕ × ℕ → ℂ := fun x => if h : x.1 < D.R.m ∧ x.2 < D.R.m then ch.c ⟨x.1, h.1⟩ ⟨x.2, h.2⟩ t else 1
  let S : ℕ → ∀ w, (locGrid ch.G t w).PiLocalization₂ := fun k w =>
    (givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)
  have hlev : ∀ k w, (S k w).level = givenLevel ch.G t w := fun k w =>
    flips_level _ _ _ _ _ _ fun _ _ => rfl
  have hpath : ∀ k w, (S k w).path =
      ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m) := fun k w =>
    flips_path _ _ _ _ _ _
  have hlen : (flipOrder D.R.m).length = D.R.m ^ 2 := (canFlip_flipOrder D.R.m).2.1
  have key : ∀ k, k ≤ D.R.m ^ 2 → ∃ p : Path T (.grid 0 D.R.m) (.grid D.R.m 0), GlobalTheory.FlipRun.OnGrid D.R.m t p ∧
      GlobalTheory.FlipRun.edges p = ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ)
        (GlobalTheory.SplitFlip.givenPath D.R.m) ∧
      ∃ τ : TotT ch.G p, GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t p τ (fun w => (S k w).tensor) ∧
        ∀ M : Vol ch.G, M.Is t → ∀ y,
          TotConv ch.W M p (GlobalTheory.FlipRun.tensE ch.W p (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ)
            (GlobalTheory.RowClaim.formTop ch t y) ∧
          thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = ((z t : ℂ) * (((flipOrder D.R.m).take k).map c').prod)⁻¹ •
            liftT ch.W M p (GlobalTheory.FlipRun.tensE ch.W p (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ)
              (GlobalTheory.RowClaim.formTop ch t y) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨⟨h1, h2⟩, -, -⟩ := GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t
      refine ⟨GlobalTheory.FunObj.givenPath t D.R.m, h1, by simpa using h2, τg, hRg, fun M hM y => ?_⟩
      obtain ⟨a, b⟩ := hg M hM y
      refine ⟨a, ?_⟩
      simpa [GlobalTheory.FlipRun.flipsPolE] using b
    | succ k ih =>
      intro hk
      obtain ⟨p, hp, hedge, τ, hR, hI⟩ := ih (by omega)
      have hkl : k < (flipOrder D.R.m).length := by omega
      set x := (flipOrder D.R.m)[k] with hx
      have hxm : x ∈ flipOrder D.R.m := List.getElem_mem hkl
      obtain ⟨hi, hj⟩ := lt_of_mem_flipOrder hxm
      have htake : (flipOrder D.R.m).take (k + 1) = (flipOrder D.R.m).take k ++ [x] := List.take_succ_eq_append_getElem hkl
      have hpass : GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (GlobalTheory.FlipRun.edges p) := by
        rw [hedge]
        have hc := (canFlip_flipOrder D.R.m).1
        rw [← List.take_append_drop k (flipOrder D.R.m), List.drop_eq_getElem_cons hkl] at hc
        exact passesThrough_of_canFlip _ _ hc
      obtain ⟨A, Bp, rfl, hA', hB', hN, hNe⟩ := GlobalTheory.T.gridPath_cut_at_square_swap_route D.R.m t x.1 x.2 hi hj p hp hpass
      have hT : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
          (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t x.1 x.2)).comp Bp)) (S k w).tensor := fun w hw => by
        have := hE t Φ w hw k (by omega)
        rwa [hpath, ← hedge] at this
      have hS : ∀ w, (S (k + 1) w).tensor = (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w)
          x.1 x.2 (givenLevel ch.G t w) (S k w).tensor := fun w => by
        rw [← hlev k w]
        show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (k + 1))).tensor = _
        rw [htake]
        simp only [GlobalTheory.SplitFlip.Grid.PiLocalization₂.flips, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hTb : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
          (GlobalTheory.FlipRun.edges ((A.comp (routeBig t x.1 x.2)).comp Bp))
          ((locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w)
            (S k w).tensor) := fun w hw => by
        have := hE t Φ w hw (k + 1) hk
        rw [← hS w, hNe, hedge]
        have e2 := hpath (k + 1) w
        rw [htake, List.foldl_append] at e2
        have e3 : (S (k + 1) w).path = GlobalTheory.SplitFlip.flipPath x.1 x.2
            (((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m)) := e2
        rw [← e3]
        exact this
      obtain ⟨τ', hR', hF⟩ := GlobalTheory.T.gridSquareFlip_smallRoute_eq_inv_smul_bigRoute hL ch.W ch.S.B ch.rm t x.1 x.2 hi hj _ (hK _ _ t) (hA t ⟨x.1, hi⟩ ⟨x.2, hj⟩)
        A Bp hA' hB' (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ (fun w => (S k w).tensor) hT hTb hR
      refine ⟨(A.comp (routeBig t x.1 x.2)).comp Bp, hN, ?_, τ', ?_, fun M hM y => ?_⟩
      · rw [hNe, hedge, htake, List.foldl_append]; rfl
      · have e : (fun w => (S (k + 1) w).tensor) = fun w => (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w)
            (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w) (S k w).tensor := funext hS
        rw [e]; exact hR'
      · obtain ⟨hc1, hc2⟩ := hI M hM y
        obtain ⟨hn1, hn2⟩ := hF M hM (hB t M hM) _ (hC t y) hc1
        have ep : GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take (k + 1)) Pg =
            GlobalTheory.FlipRun.flipPolE ch.rm x.1 x.2 (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) := by
          rw [htake, GlobalTheory.FlipRun.flipsPolE, GlobalTheory.FlipRun.flipsPolE, List.foldl_append]; rfl
        have ec : c' x = ch.c ⟨x.1, hi⟩ ⟨x.2, hj⟩ t := dif_pos ⟨hi, hj⟩
        rw [ep]
        refine ⟨hn1, ?_⟩
        rw [hc2, hn2, smul_smul, htake, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ec]
        congr 1
        exact (mul_inv _ _).symm.trans (by rw [mul_assoc])
  obtain ⟨p, hp, hedge, τ, hR, hI⟩ := key (D.R.m ^ 2) le_rfl
  have htk : (flipOrder D.R.m).take (D.R.m ^ 2) = flipOrder D.R.m := List.take_of_length_le (by rw [hlen])
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t
  have hp' : p = oppPath t D.R.m := h3 p _ hp h1 (by rw [hedge, h2, htk]; exact (canFlip_flipOrder D.R.m).2.2)
  subst hp'
  have hTf : (fun w => (S (D.R.m ^ 2) w).tensor) = Tflip ch.W ch.S.B t Φ := by
    funext w
    show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (D.R.m ^ 2))).tensor = _
    rw [htk]; rfl
  rw [hTf] at hR
  obtain ⟨τ', hτ', heq⟩ := GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath ch.W ch.S.B ch.rm t Φ (GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg) τ hR
  have hprod : ((flipOrder D.R.m).map c').prod = cTot ch t := by
    rw [prod_flipOrder, cTot, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => dif_pos ⟨i.2, j.2⟩
  refine ⟨τ', hτ', fun M hM y => ?_⟩
  obtain ⟨hc1, hc2⟩ := hI M hM y
  rw [htk, heq] at hc1 hc2
  rw [hprod] at hc2
  exact ⟨hc1, hc2⟩

end GlobalTheory.FlipRun

open GlobalTheory.RowClaim in

/- English proof (translation)
Introduce `hP hLC hWC hTI hCK`. Take `⟨C0, H⟩` from `(((((GlobalTheory.T.weil_action_commutes_on_grid hP hWC hTI).and (GlobalTheory.T.cuspidal_flip_on_volumes hLC hP)).and (GlobalTheory.T.cuspidal_listed_top_forms hP)).and (GlobalTheory.T.given_path_representation_finite hP hLC)).and GlobalTheory.T.localFlipStage_isTensor_placeDept …`. Use `⟨C0, fun ε CF h => ?_⟩` and prove the remaining obligations. Take `⟨x₀, H⟩` from `H ε CF h`. Use `⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩` and prove the remaining obligations.

Take `⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩` from `H D large₂ e hx Γ Pl0 T A Ks R F s ch i j`. Conclude with `GlobalTheory.FlipRun.flipAt_of s.core.lev ch a b c d f (fun i j t => (g i j t).2)`.
-/
theorem GlobalTheory.FlipRun.stepFlip_of : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.SquareSt.WeilConvergence →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → ConstK → StepFlip := by
  intro hP hLC hWC hTI hCK
  obtain ⟨C0, H⟩ := (((((GlobalTheory.T.weil_action_commutes_on_grid hP hWC hTI).and (GlobalTheory.T.cuspidal_flip_on_volumes hLC hP)).and
    (GlobalTheory.T.cuspidal_listed_top_forms hP)).and (GlobalTheory.T.given_path_representation_finite hP hLC)).and GlobalTheory.T.localFlipStage_isTensor_placeDepth).and hCK
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact GlobalTheory.FlipRun.flipAt_of s.core.lev ch a b c d f (fun i j t => (g i j t).2)

end
