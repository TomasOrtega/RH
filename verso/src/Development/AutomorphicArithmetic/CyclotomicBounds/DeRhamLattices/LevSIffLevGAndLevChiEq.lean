import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

/- English proof (translation)
Introduce `D X X0 Y S YS Z c w j H ι hι k`. Establish `hB` using `Z.good.base (c.twI w) j (c.sd w)`. Establish `hbo` using `GlobalTheory.PinBase.baseOf_of_pin D X Z.ρ Z.good Z.pin (c.twI w) j (c.sd w)`. Establish `hL : X.R.toLevCh.Is X.A3.A.μ0` using `X.char.lev`. Take `⟨hψ, hAdm, -⟩` from `GlobalTheory.PlaceRead.twVia_good D c w Z.ρ Z.good H.ok j ι`.

Establish `ht` using `H.tup ι hι`. Take `⟨hPg, hQ, hcg, hxq⟩` from `GlobalTheory.ConjTwist.Test.levS_chars hbo hL hB hψ hAdm ht`. Establish `rV : (Vc D j).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) j.2`. Establish `rW : (Wc D j).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) j.2`. Establish `htW : (Vc D j).rank - (Wc D j).rank = D.R.t` using `by omega`.

Establish `eβ : (Z.ρ.B (c.twI w) j (c.sd w)).F.βS = X.R.βV j` using `hbo.βS`. Establish `ebo : blkOf ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).t = blkOf (n` using `(Vc D j).rank) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).t := by show blkOf (Wc D j).rank ((Vc D j).ra …`. Rewrite using `[htW, rW]`. Establish `eb2 : blk2 (n` using `(Vc D j).rank) ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r = blk2 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r := by show blk2 (Wc D j).rank = blk2 D.R.r`. Rewrite using `[rW]`.

Establish `hPg' : ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Pg = (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Pg` using `hPg`. Establish `hQ' : ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Q = (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Q` using `hQ`. Establish `hpar : ∀ y, y ∈ parLev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) ↔ y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 fals …`. Introduce `y`. Rewrite using `[mem_parLev, mem_parLev, eβ, ebo, eb2, hPg', hQ']`.

Establish `hrt : ∀ y (hy : y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false))), rTup (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) y = Z.ρ.eG (c.twI w) …`. Introduce `y hy`. Establish `hy'` using `(hpar y).2 hy`. Use function extensionality and compare the values at `PP`. Take `⟨P, hP⟩` from `PP`.

Establish `h' : P ∈ X.R.Pg` using `by rw [← hbo.Pg]; exact hP`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Establish `hg` using `Z.pin.grp (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)) P hP h' a b`. Use `Eq.trans ?_ hg.symm` and prove the remaining obligations.

Establish `m1` using `blockTri_blkOf_le _ _ (parLev_g hy' hP)`. Establish `m2` using `blockTri_blkOf_le _ _ (parLev_g hy h')`. Establish `hz` using `X.cG.symm_apply_apply (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)`. Rewrite using `[hz]`. Simplify using `only [rTup]`.

Rewrite using `[upper_block_val_submatrix _ m1, upper_block_val_submatrix _ m2]`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[eβ]`. Both sides reduce to the same expression. Establish `hH : ∀ g : G0 X.R.Pg D.R.r, g ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H ↔ X.cG g ∈ D.nexp.U`.

Introduce `g`. Establish `h1` using `H.U_eq (X.R.eG.symm g)`. Rewrite `h1` using `[MulEquiv.apply_symm_apply]`. Rewrite using `[h1]`. Conclude with `Iff.rfl`.

Establish `hlev : ∀ x, x ∈ lev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) ↔ x ∈ lev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι))`. Introduce `x`. Rewrite using `[mem_lev, mem_lev, hpar x]`. Use `and_congr_right fun hx => ?_` and prove the remaining obligations. Rewrite using `[hrt x hx]`.

Conclude with `(hH _).trans ((Z.tie (c.twI w) j (c.sd w)).U_eq _).symm`. Use `⟨and_congr_right fun _ => hlev _, fun hk => ?_⟩` and prove the remaining obligations. Establish `hk' : Lev.finE (Vc D j) k ∈ lev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι))` using `hk.2`. Unfold `Lev.levChi`. Generalize the expression as in `Lev.finE (Vc D j) k = x at hk'`.

Take `⟨hx, hm⟩` from `mem_lev.1 ((hlev x).2 hk')`. Establish `hmem'` using `(mem_lev.1 hk').2`. Establish `hu : X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x) ∈ D.nexp.U` using `(hH _).1 hm`. Establish `hmem : Z.ρ.eG (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x)) ∈ (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H` using `((Z.tie (c.twI w) j (c.sd w)).U_eq _).2 hu`. Establish `f1 : ext1 ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).P.H ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).P.chi (rTup (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) x) = (Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi ⟨_, hmem⟩`.

Rewrite using `[extendOne_of_mem _ hmem']`. Use `congr 1`. Conclude with `Subtype.ext (hrt x hx)`. Establish `hchi : ∀ (g : G0 X.R.Pg D.R.r) (hg : g ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H) (hu : X.cG g ∈ D.nexp.U), (((Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F. …`. Introduce `g hg hu`.

Take `⟨g₀, rfl⟩` from `X.R.eG.surjective g`. Establish `h0 : g₀ ∈ X.F.P0` using `(H.U_eq g₀).1 hu`. Rewrite using `[H.psi_eq (c.twI w) (c.sd w) ⟨g₀, h0⟩ hu]`. Establish `h1 : X.R.eG.symm (X.R.eG g₀) ∈ X.F.P0` using `by rw [MulEquiv.symm_apply_apply]; exact h0`. Establish `e : (⟨g₀, h0⟩ : X.F.P0) = ⟨_, h1⟩` using `Subtype.ext (X.R.eG.symm_apply_apply g₀).symm`.

Rewrite using `[e]`. Conclude with `Units.val_inv_eq_inv_val _`. Establish `f1' : ext1 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.chi (rTup (X.R.βV j) (Formalism.IndefR.RecTie …`. Rewrite using `[extendOne_of_mem _ hm]`. Conclude with `Units.ext ((hchi _ hm hu).trans ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ hmem).symm)`.

Establish `f2 : (∏ PP ∈ ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Pg, ∏ b ∈ Finset.range ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).s, ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).cg (b + 1) PP (dBlk (blkOf ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r ((Z.ρ.B (c.t …`. Use `Finset.prod_congr hPg' fun PP hP => Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `h' : PP ∈ X.R.Pg` using `hP`. Rewrite using `[hcg _ PP h', ebo, eβ]`. Both sides reduce to the same expression.

Establish `f3 : (∏ PP ∈ ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Q, ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).xq PP (dBlk (blk2 ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r) 1 (redFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS PP x))) = ∏ PP ∈ (Formalism.IndefR.RecTie.datVP X. …`. Use `Finset.prod_congr hQ' fun PP hP => ?_` and prove the remaining obligations. Establish `h' : PP ∈ X.R.Q (Y.tupT (D.what₂.muTw w))` using `hP`. Rewrite using `[hxq PP h', eb2, eβ]`. Both sides reduce to the same expression.

Use `show ((levFn (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x : ℂˣ) : ℂ) = ((levFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) x : ℂˣ) : ℂ)`. Unfold `levFn`. Rewrite using `[f1, f1', f2, f3]`.
-/
theorem _root_.UpperTheory.KN.levS_iff_levG_and_levChi_eq :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ k : GA D (Vc D j), (k ∈ levS (Vc D j) (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) ↔ k ∈ Lev.levG (Vc D j) (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι))) ∧
      (k ∈ Lev.levG (Vc D j) (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) → Lev.levChi (Vc D j) (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) k = Lev.levChi (Vc D j) (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) k) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι k
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hbo := GlobalTheory.PinBase.baseOf_of_pin D X Z.ρ Z.good Z.pin (c.twI w) j (c.sd w)
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  obtain ⟨hψ, hAdm, -⟩ := GlobalTheory.PlaceRead.twVia_good D c w Z.ρ Z.good H.ok j ι
  have ht := H.tup ι hι
  obtain ⟨hPg, hQ, hcg, hxq⟩ := GlobalTheory.ConjTwist.Test.levS_chars hbo hL hB hψ hAdm ht
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have htW : (Vc D j).rank - (Wc D j).rank = D.R.t := by omega
  have eβ : (Z.ρ.B (c.twI w) j (c.sd w)).F.βS = X.R.βV j := hbo.βS
  have ebo : blkOf ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).t =
      blkOf (n := (Vc D j).rank) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).t := by
    show blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) = blkOf D.R.r D.R.t
    rw [htW, rW]
  have eb2 : blk2 (n := (Vc D j).rank) ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r = blk2 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r := by
    show blk2 (Wc D j).rank = blk2 D.R.r
    rw [rW]
  have hPg' : ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Pg = (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Pg := hPg
  have hQ' : ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Q = (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Q := hQ
  have hpar : ∀ y, y ∈ parLev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) ↔
      y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) := by
    intro y
    rw [mem_parLev, mem_parLev, eβ, ebo, eb2, hPg', hQ']
  have hrt : ∀ y (hy : y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false))),
      rTup (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) y =
        Z.ρ.eG (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)) := by
    intro y hy
    have hy' := (hpar y).2 hy
    funext PP
    obtain ⟨P, hP⟩ := PP
    have h' : P ∈ X.R.Pg := by rw [← hbo.Pg]; exact hP
    apply Units.ext
    ext a b
    have hg := Z.pin.grp (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)) P hP h' a b
    refine Eq.trans ?_ hg.symm
    have m1 := blockTri_blkOf_le _ _ (parLev_g hy' hP)
    have m2 := blockTri_blkOf_le _ _ (parLev_g hy h')
    have hz := X.cG.symm_apply_apply (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) y)
    rw [hz]
    simp only [rTup]
    rw [upper_block_val_submatrix _ m1, upper_block_val_submatrix _ m2]
    simp only [Matrix.submatrix_apply]
    rw [eβ]
    rfl
  have hH : ∀ g : G0 X.R.Pg D.R.r, g ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H ↔ X.cG g ∈ D.nexp.U := by
    intro g
    have h1 := H.U_eq (X.R.eG.symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    exact Iff.rfl
  have hlev : ∀ x, x ∈ lev D.sp.cm (Vc D j).gram (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) ↔
      x ∈ lev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) := by
    intro x
    rw [mem_lev, mem_lev, hpar x]
    refine and_congr_right fun hx => ?_
    rw [hrt x hx]
    exact (hH _).trans ((Z.tie (c.twI w) j (c.sd w)).U_eq _).symm
  refine ⟨and_congr_right fun _ => hlev _, fun hk => ?_⟩
  have hk' : Lev.finE (Vc D j) k ∈ lev D.sp.cm (Vc D j).gram (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) := hk.2
  unfold Lev.levChi
  generalize Lev.finE (Vc D j) k = x at hk'
  obtain ⟨hx, hm⟩ := mem_lev.1 ((hlev x).2 hk')
  have hmem' := (mem_lev.1 hk').2
  have hu : X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x) ∈ D.nexp.U := (hH _).1 hm
  have hmem : Z.ρ.eG (c.twI w) j (c.sd w) (X.cG (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x)) ∈ (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H :=
    ((Z.tie (c.twI w) j (c.sd w)).U_eq _).2 hu
  have f1 : ext1 ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).P.H ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).P.chi (rTup (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) x) =
      (Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi ⟨_, hmem⟩ := by
    rw [extendOne_of_mem _ hmem']
    congr 1
    exact Subtype.ext (hrt x hx)
  have hchi : ∀ (g : G0 X.R.Pg D.R.r) (hg : g ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H) (hu : X.cG g ∈ D.nexp.U),
      (((Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.chi ⟨g, hg⟩ : ℂˣ) : ℂ) =
        Z.ρ.e (c.twI w) (c.sd w) (D.nexp.psiU (c.twI w) (c.sd w) ⟨_, hu⟩ : (FractionRing (D.ntw.O (c.twI w)))ˣ) := by
    intro g hg hu
    obtain ⟨g₀, rfl⟩ := X.R.eG.surjective g
    have h0 : g₀ ∈ X.F.P0 := (H.U_eq g₀).1 hu
    rw [H.psi_eq (c.twI w) (c.sd w) ⟨g₀, h0⟩ hu]
    have h1 : X.R.eG.symm (X.R.eG g₀) ∈ X.F.P0 := by rw [MulEquiv.symm_apply_apply]; exact h0
    have e : (⟨g₀, h0⟩ : X.F.P0) = ⟨_, h1⟩ := Subtype.ext (X.R.eG.symm_apply_apply g₀).symm
    rw [e]
    exact Units.val_inv_eq_inv_val _
  have f1' : ext1 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.H (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).P.chi (rTup (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x) = (Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi ⟨_, hmem⟩ := by
    rw [extendOne_of_mem _ hm]
    exact Units.ext ((hchi _ hm hu).trans ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ hmem).symm)
  have f2 : (∏ PP ∈ ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Pg, ∏ b ∈ Finset.range ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).s,
        ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).cg (b + 1) PP (dBlk (blkOf ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).t) (b + 1) (redFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS PP x))) =
      ∏ PP ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Pg, ∏ b ∈ Finset.range (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).s,
        (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).cg (b + 1) PP (dBlk (blkOf (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).t) (b + 1) (redFn (X.R.βV j) PP x)) := by
    refine Finset.prod_congr hPg' fun PP hP => Finset.prod_congr rfl fun b _ => ?_
    have h' : PP ∈ X.R.Pg := hP
    rw [hcg _ PP h', ebo, eβ]
    rfl
  have f3 : (∏ PP ∈ ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).Q, ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).xq PP (dBlk (blk2 ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)).r) 1 (redFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS PP x))) =
      ∏ PP ∈ (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).Q, (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).xq PP (dBlk (blk2 (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)).r) 1 (redFn (X.R.βV j) PP x)) := by
    refine Finset.prod_congr hQ' fun PP hP => ?_
    have h' : PP ∈ X.R.Q (Y.tupT (D.what₂.muTw w)) := hP
    rw [hxq PP h', eb2, eβ]
    rfl
  show ((levFn (X.R.βV j) (Formalism.IndefR.RecTie.datVP X.R.toRealDat j (Y.tupT (D.what₂.muTw w)) (X.R.toRealDat.levR X.F.lv2 false)) x : ℂˣ) : ℂ) = ((levFn (Z.ρ.B (c.twI w) j (c.sd w)).F.βS ((Z.ρ.B (c.twI w) j (c.sd w)).levS (twVia Z.ρ ι)) x : ℂˣ) : ℂ)
  unfold levFn
  rw [f1, f1', f2, f3]
