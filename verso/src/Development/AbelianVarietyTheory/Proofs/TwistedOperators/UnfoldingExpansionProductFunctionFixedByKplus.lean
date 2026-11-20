import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColAtFirstPt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedTensorEigenvalueLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepPointMulPeriodUnipotentGLMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopZeroInv GlobalTheory.TopLevelInv GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroFirst

section Local

open GlobalTheory.FunObj.FiniteSupport GlobalTheory.TopLevelInv.FlatStep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in

/- English proof (translation)
Use function extensionality and compare the values at `b`. Consider the cases of `b with`. Consider the case `theta i l`. Distinguish the cases in `hi : i = Γ.m`. Substitute `hi` using the available equality.

Rewrite using `[moveArgs_theta, fill_theta, fill_theta, transpose_transpose]`. Establish `h2 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (Γ.m, l + 1) = 1` using `Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _`. Distinguish the cases in `hl : l = 0`. Substitute `hl` using the available equality. Rewrite using `[h2, Pi.mulSingle_eq_same, inv_one, Units.val_one, Matrix.one_mul, h0]`.

Establish `h1 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (Γ.m, l) = 1` using `Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _`. Simplify using `only [h1, h2, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hrest l hl]`. Simplify using `[fill, Grid.moveArgs, hi]`. Consider the case `ex i l`. Distinguish the cases in `hl : l = Γ.m`.

Substitute `hl` using the available equality. Establish `h1 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (i, Γ.m) = 1` using `Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _`. Establish `h2 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (i + 1, Γ.m) = 1` using `Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _`. Simplify using `only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex, h1, h2, map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]`. Simplify using `[fill, Grid.moveArgs, hl]`.
-/
theorem fill_moveEnd {Γ : Grid k} (hs : 1 ≤ Γ.s) (hm : 0 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, 0))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ)
    (hrest : ∀ l, l ≠ 0 → downMap hs x' e' l = downMap hs x e l)
    (h0 : downMap hs x' e' 0 = downMap hs x e 0 * g.val) :
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, 0) g) (fill hs x y e) = fill hs x' y e' := by
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = Γ.m
    · subst hi
      rw [moveArgs_theta, fill_theta, fill_theta, transpose_transpose]
      have h2 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (Γ.m, l + 1) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
      by_cases hl : l = 0
      · subst hl
        rw [h2, Pi.mulSingle_eq_same, inv_one, Units.val_one, Matrix.one_mul, h0]
      · have h1 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
        simp only [h1, h2, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hrest l hl]
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = Γ.m
    · subst hl
      have h1 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (i, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) (i + 1, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

/- English proof (translation)
Use `set x' : ColArgs Γ := Function.update x 0 (x 0 * κ.val) with hx'`. Establish `hcol : ∀ i, i ≠ 0 → x' i = x i` using `fun i h => Function.update_of_ne h _ _`. Establish `hc0 : x' 0 = x 0 * κ.val` using `Function.update_self _ _ _`. Take `⟨φ₀, hφ₀, H⟩` from `StepMove.exists_embX_mp (ν := ν) (n := Fin (topRank Γ (0 + 1))) (c := Γ.m - 2 - 0) κ hdet (x 0)`. Set `Ψ0 : StepFam Γ` to `fun i => MeasurableEquiv.refl _`.

Set `Ψ1 : StepFam Γ` to `Function.update Ψ0 ⟨0, by omega⟩ φ₀`. Set `Φ : Vars Γ ≃ᵐ Vars Γ` to `MeasurableEquiv.piCongrRight Ψ1`. Establish `hΦ0 : ∀ e, Φ e ⟨0, by omega⟩ = φ₀ (e ⟨0, by omega⟩)` using `fun e => by show Function.update Ψ0 ⟨0, by omega⟩ φ₀ ⟨0, by omega⟩ (e ⟨0, by omega⟩) = _`. Rewrite using `[Function.update_self]`. Establish `hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ 0 → Φ e i = e i` using `fun e i h1 => by show Function.update Ψ0 ⟨0, by omega⟩ φ₀ i (e i) = _`.

Rewrite using `[Function.update_of_ne (fun h => h1 (by rw [h]))]`. Both sides reduce to the same expression. Establish `hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν)` using `measurePreserving_stepFam ν Ψ1 (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨0, by omega⟩ φ₀ hφ₀)`. Establish `hf : frameGL (show topRank Γ 0 + (Γ.m - 2 - 0 + 1) = Γ.rank (Γ.m, 0) by`. Use `topRank_add hs 0` as an intermediate fact.

Use the proof step `omega) g = embX (Γ.m - 2 - 0 + 1) κ :=`. Use `frameGL_embX_congr (by omega) _ _ hg`. Use `flatTensor_comp_of_equiv hs ψ ν F _ x x' y Φ hMP (fun e => ?_) (fun e => ?_)` and prove the remaining obligations. Use `fill_moveEnd hs (by omega) g x x' y e (Φ e) (fun l h1 => ?_) ?_` and prove the remaining obligations. Conclude with `downMap_congr hs (hcol l h1) fun h => hΦo e ⟨l, h⟩ h1`.

Rewrite using `[downMap, dif_pos (show 0 < Γ.m - 1 by omega), downMap, dif_pos (show 0 < Γ.m - 1 by omega), hc0, hΦ0, ← H, reindex_mul_frameGL, hf]`. Establish `hent : ∀ (j : Fin (Γ.m - 1)) r s, stepPt (x j) (e j) r (.inr s) = stepPt (x' j) (Φ e j) r (.inr s)`. Introduce and unpack `⟨j, hj⟩ r s`. Break down `eq_or_ne j 0 with rfl | h` into its components or cases. Establish `hgv : (embX (Γ.m - 2 - 0 + 1) κ).val = fromBlocks κ.val 0 0 1` using `rfl`.

Establish `h1` using `congrFun (congrFun (H (e ⟨0, hj⟩)) r) (.inr s)`. Rewrite `h1` using `[hgv, GlobalTheory.RootEx.OpELevi.right_inr, ← hc0, ← hΦ0]`. Conclude with `h1`. Rewrite using `[hΦo e ⟨j, hj⟩ h]`. Conclude with `congrArg (fun z => stepPt z (e ⟨j, hj⟩) r (.inr s)) (hcol j h).symm`.

Establish `hrow : ∀ j r, rowVar x e (j + 1) r = rowVar x' (Φ e) (j + 1) r` using `fun j r => by`. Unfold `rowVar`. Use `split_ifs with h`. Rewrite using `[hcol (j + 1) j.succ_ne_zero, hΦo e ⟨j + 1, h⟩ j.succ_ne_zero]`. Rewrite using `[hcol (j + 1) j.succ_ne_zero]`.

Simplify using `only [phase, ch, colVar, hent, hrow]`.
-/
theorem flatTensor_moveEnd {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (F : Γ.Args → ℂ) (hm : 2 ≤ Γ.m) (g : GL (Fin (Γ.rank (Γ.m, 0))) k) (κ : GL (Fin (topRank Γ 0)) k)
    (hdet : valuation k (gdet κ : k) = 1) (hg : toFrame hs (show 0 < Γ.m by omega) g = embX _ κ) (x : ColArgs Γ) (y : RowArgs Γ) :
    flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, 0) g) z)) x y =
      flatTensor hs ψ ν F (Function.update x 0 (x 0 * κ.val)) y := by
  set x' : ColArgs Γ := Function.update x 0 (x 0 * κ.val) with hx'
  have hcol : ∀ i, i ≠ 0 → x' i = x i := fun i h => Function.update_of_ne h _ _
  have hc0 : x' 0 = x 0 * κ.val := Function.update_self _ _ _
  obtain ⟨φ₀, hφ₀, H⟩ := StepMove.exists_embX_mp (ν := ν) (n := Fin (topRank Γ (0 + 1))) (c := Γ.m - 2 - 0) κ hdet (x 0)
  let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
  let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨0, by omega⟩ φ₀
  let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ1
  have hΦ0 : ∀ e, Φ e ⟨0, by omega⟩ = φ₀ (e ⟨0, by omega⟩) := fun e => by
    show Function.update Ψ0 ⟨0, by omega⟩ φ₀ ⟨0, by omega⟩ (e ⟨0, by omega⟩) = _
    rw [Function.update_self]
  have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ 0 → Φ e i = e i := fun e i h1 => by
    show Function.update Ψ0 ⟨0, by omega⟩ φ₀ i (e i) = _
    rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
    rfl
  have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
    measurePreserving_stepFam ν Ψ1 (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨0, by omega⟩ φ₀ hφ₀)
  have hf : frameGL (show topRank Γ 0 + (Γ.m - 2 - 0 + 1) = Γ.rank (Γ.m, 0) by
      have := topRank_add hs 0; omega) g = embX (Γ.m - 2 - 0 + 1) κ :=
    frameGL_embX_congr (by omega) _ _ hg
  refine flatTensor_comp_of_equiv hs ψ ν F _ x x' y Φ hMP (fun e => ?_) (fun e => ?_)
  · refine fill_moveEnd hs (by omega) g x x' y e (Φ e) (fun l h1 => ?_) ?_
    · exact downMap_congr hs (hcol l h1) fun h => hΦo e ⟨l, h⟩ h1
    · rw [downMap, dif_pos (show 0 < Γ.m - 1 by omega), downMap, dif_pos (show 0 < Γ.m - 1 by omega), hc0, hΦ0,
        ← H, reindex_mul_frameGL, hf]
  · have hent : ∀ (j : Fin (Γ.m - 1)) r s, stepPt (x j) (e j) r (.inr s) = stepPt (x' j) (Φ e j) r (.inr s) := by
      rintro ⟨j, hj⟩ r s
      rcases eq_or_ne j 0 with rfl | h
      · have hgv : (embX (Γ.m - 2 - 0 + 1) κ).val = fromBlocks κ.val 0 0 1 := rfl
        have h1 := congrFun (congrFun (H (e ⟨0, hj⟩)) r) (.inr s)
        rw [hgv, GlobalTheory.RootEx.OpELevi.right_inr, ← hc0, ← hΦ0] at h1
        exact h1
      · rw [hΦo e ⟨j, hj⟩ h]
        exact congrArg (fun z => stepPt z (e ⟨j, hj⟩) r (.inr s)) (hcol j h).symm
    have hrow : ∀ j r, rowVar x e (j + 1) r = rowVar x' (Φ e) (j + 1) r := fun j r => by
      unfold rowVar
      split_ifs with h
      · rw [hcol (j + 1) j.succ_ne_zero, hΦo e ⟨j + 1, h⟩ j.succ_ne_zero]
      · rw [hcol (j + 1) j.succ_ne_zero]
    simp only [phase, ch, colVar, hent, hrow]

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hS : x ∈ St β` using `(GlobalTheory.LevSplit.mem_St_iff _ _ hβ x).2 (GlobalTheory.CongMember.stab_of_mem_congLev hx)`. Use `GivenAdm.mem_glLatCong.2 ⟨LevRowSucc.KO_of_St h β w hS, GivenAdm.mem_matLat_smul.1 ((Comparison₂.mem_matLat_pow w _ _).2 fun a b => ?_)⟩` and prove the remaining obligations. Establish `hz` using `(hβ (β.1 *ᵥ Pi.single (Fin.cast h b) 1)).2 fun i => by`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Take `⟨s, hs, e⟩` from `GlobalTheory.FrameCong.coord_mem_idS β Λ hβ G.modul _ (hx.2.2 _ hz) (Fin.cast h a)`. Establish `e1 : (inBasis h β w x).val a b - (1 : Matrix (Fin n) (Fin n) (Kw w)) a b = cpt w (s : Lev.EAf D)`. Rewrite using `[← e, Matrix.mulVec_sub, Pi.sub_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_single_one, map_sub, LevRowSucc.inBasis_val, Pi.single_apply, Matrix.one_apply]`.

Use `congr 1`. Distinguish the cases in `hab : a = b`. Rewrite using `[if_pos hab, if_pos (by rw [hab]), map_one]`. Rewrite using `[if_neg hab, if_neg (fun h' => hab (Fin.cast_injective h h')), map_zero]`. Rewrite using `[Matrix.sub_apply, e1]`.

Distinguish the cases in `hw : w ∈ G.pl.W0`. Conclude with `(Comparison₂.mem_idS_modul G s).1 hs w hw`. Rewrite using `[(depthAt_of_notMem G hw).1, Nat.cast_zero, neg_zero, WithZero.exp_zero]`. Conclude with `(mem_OA_iff _).1 s.2 w`.
-/
theorem inBasis_mem_glLatCong (G : GridData L sc) {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {β x : GL (Fin V.rank) (Lev.EAf D)} (hβ : IsFrame β Λ) (hx : x ∈ congLev D.sp.cm V.gram Λ G.modul) {n : ℕ} (h : n = V.rank)
    (w : Pl D.host.E) : inBasis h β w x ∈ glLatCong (unifAt w ^ cosExp G w) (SplitFlip.stdLat (Kw w) _) := by
  have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff _ _ hβ x).2 (GlobalTheory.CongMember.stab_of_mem_congLev hx)
  refine GivenAdm.mem_glLatCong.2 ⟨LevRowSucc.KO_of_St h β w hS, GivenAdm.mem_matLat_smul.1 ((Comparison₂.mem_matLat_pow w _ _).2 fun a b => ?_)⟩
  have hz := (hβ (β.1 *ᵥ Pi.single (Fin.cast h b) 1)).2 fun i => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  obtain ⟨s, hs, e⟩ := GlobalTheory.FrameCong.coord_mem_idS β Λ hβ G.modul _ (hx.2.2 _ hz) (Fin.cast h a)
  have e1 : (inBasis h β w x).val a b - (1 : Matrix (Fin n) (Fin n) (Kw w)) a b = cpt w (s : Lev.EAf D) := by
    rw [← e, Matrix.mulVec_sub, Pi.sub_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec, Matrix.mulVec_single_one, map_sub, LevRowSucc.inBasis_val, Pi.single_apply, Matrix.one_apply]
    congr 1
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab]), map_one]
    · rw [if_neg hab, if_neg (fun h' => hab (Fin.cast_injective h h')), map_zero]
  rw [Matrix.sub_apply, e1]
  by_cases hw : w ∈ G.pl.W0
  · exact (Comparison₂.mem_idS_modul G s).1 hs w hw
  · rw [(depthAt_of_notMem G hw).1, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact (mem_OA_iff _).1 s.2 w

/- English proof (translation)
The claim follows from `inBasis_mem_glLatCong G (S.βp_is 0 (Nat.zero_le _)) hk _ w`.
-/
theorem kapTop0_mem (S : GridChoice W U) (t : T) (k : FinPt G (.top 0)) (hk : finG (G.V (.top 0)) k ∈ G.Kplus)
    (w : Pl D.host.E) : kapTop0 S t k w ∈ glLatCong (unifAt w ^ cosExp G w) (SplitFlip.stdLat (Kw w) _) :=
  inBasis_mem_glLatCong G (S.βp_is 0 (Nat.zero_le _)) hk _ w

open GlobalTheory.RowVacScalar in

/- English proof (translation)
Establish `h0` using `notMem_S0_of_no_place_above G t hv`. Establish `hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ v` using `fun P hP => hv P (Finset.mem_union_right _ hP)`. Use `GlobalTheory.SeeSaw.WeilLines.charUnram_mul (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_) (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_)` and prove the remaining obligations. Use `(GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨0, zero_lt_m D⟩) w).2 ((L.C.isMu0 ⟨0, zero_lt_m D⟩).unr w fun k hk => h0 (G.pl.mem_S0_of_sum_eq.2 (.inr ?_)))` and prove the remaining obligations. Rewrite using `[← hw, S1_mem_OmF, Good.natCast_mem_under, Good.natCast_mem_under]`.

Use `fin_cases k`. Conclude with `.inl hk`. Conclude with `.inr (.inl hk)`. Use `(GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Break down `(hL.Q_ram t w).1 h with h | ⟨P, hP, h⟩` into its components or cases. Conclude with `hQ w h hw`. Conclude with `hQ P hP (by rw [← hw, (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP])`.
-/
theorem mu_one_unramAt {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (L.mu t (0 + 1)) v := by
  classical
  have h0 := notMem_S0_of_no_place_above G t hv
  have hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ v := fun P hP => hv P (Finset.mem_union_right _ hP)
  refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_)
    (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_)
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨0, zero_lt_m D⟩) w).2
      ((L.C.isMu0 ⟨0, zero_lt_m D⟩).unr w fun k hk => h0 (G.pl.mem_S0_of_sum_eq.2 (.inr ?_)))
    rw [← hw, S1_mem_OmF, Good.natCast_mem_under, Good.natCast_mem_under]
    fin_cases k
    · exact .inl hk
    · exact .inr (.inl hk)
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra h
    rcases (hL.Q_ram t w).1 h with h | ⟨P, hP, h⟩
    · exact hQ w h hw
    · exact hQ P hP (by rw [← hw, (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP])

open GlobalTheory.RowVacScalar in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hj` using `zero_lt_m D`. Establish `hp : DefPair D.R.m (.top t 0 : Pair T)` using `show 0 + 1 ≤ D.R.m from hj`. Establish `hn` using `hp.nodes`. Establish `hW` using `W.om_is (.top t 0) (show 0 + 1 ≤ D.R.m from hj)`. Establish `hv` using `(S.Z.vac_is _ hp).2`.

Establish `hchr : ∀ n, n ≤ D.R.m → Formalism.IndefR.Lift.attChr (G.chr (.top t 0)) L.eta (G.V (.top n)).rank = L.mu t (0 + 1)` using `fun n hn => by`. Establish `hrank : (G.V (.top n)).rank = rankX D n` using `(G.isV (X := .top n) hn (fun _ h => by cases h)).rank`. Rewrite using `[hrank]`. Simplify using `[Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D n)]`. Establish `hS : G.chrS (.top t 0) = L.mu t (0 + 1)` using `hchr _ hj.le`.

Establish `hT : G.chrT (.top t 0) = L.mu t (0 + 1)` using `hchr _ hj`. Establish `h2` using `GlobalTheory.LastColLat.conj_stab S.N (X := .top 0) (by simp [DefNode]) k (mem_congLev.1 hk).2.1`. Establish `hdet : ∀ w : locPl G t, detIdl (idemAt w.1) (G.V (.top 0)) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 = GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapTop0 S t k w))` using `fun w => GlobalTheory.RowDetLocal.detIdl_conj_eq_locIdele _ _ _ k (S.N.u (.top 0)) w.1 ⟨_, isIdemAt_idemAt hL G t w.2⟩`. Establish `hfin` using `((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).2`. Generalize the expression as in `((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 = g at h2 hdet hfin ⊢`.

Establish `h1 : ∀ (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) y, y ∈ latHat D.host.F D.host.E Λ ↔ ((Formalism.L2.Theta.mt V 1).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E Λ` using `fun V Λ y => by`. Rewrite using `[GlobalTheory.LatStabScalar.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Establish `d1 : ∀ (e : AE D) (V : HSp D), detIdl e V 1 = 1` using `fun e V => by`. Unfold `detIdl`. Use `split_ifs`.

Conclude with `map_one _`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW (S.N.selfDual hn.1) (S.N.selfDual hn.2) (locPl G t) (fun w hw => isIdemAt_idemAt hL G t hw) (Good.under_injOn hL G t) (fun v hv' => by rw [hS, hT]; exact ⟨mu_one_unramAt hL G t hv', mu_one_unramAt hL G t hv'⟩) g hfin 1 (one_mem _) …`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_coe_sort (locPl G t)]`.

Use `congrArg (· • S.Z.vac (.top t 0)) (Finset.prod_congr rfl fun w _ => ?_)` and prove the remaining obligations. Establish `hE : ChrEq (L.mu t (0 + 1)) (muBase L (0 + 1) * L.xiH t)`. Establish `h1 : muBase L (0 + 1) = L.C.mu0 ⟨0, hj⟩` using `dif_pos hj`. Rewrite using `[h1]`. Conclude with `GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨0, hj⟩) (hL.xi t)`.

Establish `hd : detIdl (idemAt w.1) (G.pS (.top t 0 : Pair T)) g = GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapTop0 S t k w))` using `hdet w`. Rewrite using `[splitFacO, d1, map_one, mul_one, hd, hT, Circle.coe_inv, Units.val_inv_eq_inv_val]`. Conclude with `congrArg (fun f => ((f (gdet (kapTop0 S t k w)) : ℂˣ) : ℂ)⁻¹) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)`.
-/
theorem om_first_vac (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.top 0))
    (hk : finG (G.V (.top 0)) k ∈ G.Kplus) :
    W.om (.top t 0) (G.toPair (.top t 0 : Pair T) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (S.Z.vac (.top t 0)) =
      (∏ w : locPl G t, ((((locGrid G t w).mu 1 (gdet (kapTop0 S t k w)))⁻¹ : ℂˣ) : ℂ)) • S.Z.vac (.top t 0) := by
  classical
  have hj := zero_lt_m D
  have hp : DefPair D.R.m (.top t 0 : Pair T) := show 0 + 1 ≤ D.R.m from hj
  have hn := hp.nodes
  have hW := W.om_is (.top t 0) (show 0 + 1 ≤ D.R.m from hj)
  have hv := (S.Z.vac_is _ hp).2
  have hchr : ∀ n, n ≤ D.R.m → Formalism.IndefR.Lift.attChr (G.chr (.top t 0)) L.eta (G.V (.top n)).rank = L.mu t (0 + 1) :=
    fun n hn => by
      have hrank : (G.V (.top n)).rank = rankX D n := (G.isV (X := .top n) hn (fun _ h => by cases h)).rank
      rw [hrank]
      simp [Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D n)]
  have hS : G.chrS (.top t 0) = L.mu t (0 + 1) := hchr _ hj.le
  have hT : G.chrT (.top t 0) = L.mu t (0 + 1) := hchr _ hj
  have h2 := GlobalTheory.LastColLat.conj_stab S.N (X := .top 0) (by simp [DefNode]) k (mem_congLev.1 hk).2.1
  have hdet : ∀ w : locPl G t, detIdl (idemAt w.1) (G.V (.top 0)) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 =
      GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapTop0 S t k w)) := fun w =>
    GlobalTheory.RowDetLocal.detIdl_conj_eq_locIdele _ _ _ k (S.N.u (.top 0)) w.1 ⟨_, isIdemAt_idemAt hL G t w.2⟩
  have hfin := ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).2
  generalize ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 = g at h2 hdet hfin ⊢
  have h1 : ∀ (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) y, y ∈ latHat D.host.F D.host.E Λ ↔
      ((Formalism.L2.Theta.mt V 1).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E Λ := fun V Λ y => by
    rw [GlobalTheory.LatStabScalar.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have d1 : ∀ (e : AE D) (V : HSp D), detIdl e V 1 = 1 := fun e V => by
    unfold detIdl
    split_ifs
    · exact map_one _
    · rfl
  have key := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW (S.N.selfDual hn.1) (S.N.selfDual hn.2) (locPl G t)
    (fun w hw => isIdemAt_idemAt hL G t hw) (Good.under_injOn hL G t) (fun v hv' => by rw [hS, hT]; exact ⟨mu_one_unramAt hL G t hv', mu_one_unramAt hL G t hv'⟩)
    g hfin 1 (one_mem _) (GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ _ _ h2) (h1 _ _) _ hv.theta hv.lat
  refine key.trans ?_
  rw [← Finset.prod_coe_sort (locPl G t)]
  refine congrArg (· • S.Z.vac (.top t 0)) (Finset.prod_congr rfl fun w _ => ?_)
  have hE : ChrEq (L.mu t (0 + 1)) (muBase L (0 + 1) * L.xiH t) := by
    have h1 : muBase L (0 + 1) = L.C.mu0 ⟨0, hj⟩ := dif_pos hj
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨0, hj⟩) (hL.xi t)
  have hd : detIdl (idemAt w.1) (G.pS (.top t 0 : Pair T)) g = GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapTop0 S t k w)) := hdet w
  rw [splitFacO, d1, map_one, mul_one, hd, hT, Circle.coe_inv, Units.val_inv_eq_inv_val]
  exact congrArg (fun f => ((f (gdet (kapTop0 S t k w)) : ℂˣ) : ℂ)⁻¹) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)

section EndVertex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hd : ∀ Y, gdet ((Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) Y) = if Y = (Γ.m, 0) then gdet g else 1` using `fun Y => by split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hv : ∀ Y, valuation k (((if Y = (Γ.m, 0) then gdet g else 1 : kˣ)⁻¹ : kˣ) : k) = 1` using `fun Y => by split_ifs`.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hg, inv_one]`. Simplify using the standard rewrite rules. Establish `hf : ∀ b, Γ.edgeFactor .one (Pi.mulSingle (Γ.m, 0) g) b = (Γ.kappa b b.src (if b.src = (Γ.m, 0) then gdet g else 1) : ℂ) * (((Γ.kappa b b.tgt (if b.tgt = (Γ.m, 0) then gdet g else 1))⁻¹ : ℂˣ) : ℂ)` using `fun b => by`. Simplify using `only [Grid.edgeFactor, Assignment.read, gdet_invT, hd, apow_of_valuation_eq_one (hv _), mul_one]`. Rewrite using `[oppositePath, List.map_append, List.prod_append, List.map_map, List.map_map, List.map_reverse, List.prod_reverse, List.prod_eq_one, one_mul, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]`.

Simplify using `only [Function.comp, hf]`. Rewrite using `[Finset.prod_eq_single 0]`. Simplify using `[Grid.kappa, Grid.blockChar, hη _ hg]`. Introduce `b _ hb`. Simplify using `[hb]`.

Introduce `h`. Simplify using `at h`. Use linear arithmetic over natural numbers and integers. Introduce `c hc`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hc`.

Simplify using `[hf, hm.ne']`.
-/
theorem prod_edgeFactor_end {Γ : Grid k} (hm : 0 < Γ.m) (hη : IsUnram Γ.eta) (g : GL (Fin (Γ.rank (Γ.m, 0))) k)
    (hg : valuation k (gdet g : k) = 1) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (Γ.m, 0) g))).prod = (((Γ.mu 1 (gdet g))⁻¹ : ℂˣ) : ℂ) := by
  have hd : ∀ Y, gdet ((Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) Y) = if Y = (Γ.m, 0) then gdet g else 1 := fun Y => by
    split_ifs with h
    · subst h; simp
    · simp [h]
  have hv : ∀ Y, valuation k (((if Y = (Γ.m, 0) then gdet g else 1 : kˣ)⁻¹ : kˣ) : k) = 1 := fun Y => by
    split_ifs
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hg, inv_one]
    · simp
  have hf : ∀ b, Γ.edgeFactor .one (Pi.mulSingle (Γ.m, 0) g) b =
      (Γ.kappa b b.src (if b.src = (Γ.m, 0) then gdet g else 1) : ℂ) *
        (((Γ.kappa b b.tgt (if b.tgt = (Γ.m, 0) then gdet g else 1))⁻¹ : ℂˣ) : ℂ) := fun b => by
    simp only [Grid.edgeFactor, Assignment.read, gdet_invT, hd, apow_of_valuation_eq_one (hv _), mul_one]
  rw [oppositePath, List.map_append, List.prod_append, List.map_map, List.map_map, List.map_reverse, List.prod_reverse,
    List.prod_eq_one, one_mul, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  · simp only [Function.comp, hf]
    rw [Finset.prod_eq_single 0]
    · simp [Grid.kappa, Grid.blockChar, hη _ hg]
    · intro b _ hb; simp [hb]
    · intro h; simp at h; omega
  · intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    simp [hf, hm.ne']

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Use `set h' := ρ.elt β with hh'`. Establish `hb : h' (Γ.m, 0) = ρ.base` using `by rw [hh', Reps.elt, onColumn_apply]`. Use `set g := ρ.base * u * ρ.base⁻¹ with hg`. Establish `hgd : gdet g = gdet κ`. Rewrite using `[← gdet_toFrame hs (show 0 < Γ.m by omega), h, gdet_embX]`.

Establish `hcomm : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) * h' = h' * Pi.mulSingle (Γ.m, 0) u`. Use function extensionality and compare the values at `Y`. Distinguish the cases in `hY : Y = (Γ.m, 0)`. Substitute `hY` using the available equality. Simplify using `[hg, hb]`.

Simplify using `[hY]`. Establish `hinv : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (Γ.m, 0) g) (Γ.pathAct .one (oppositePath Γ.m) h' F) = Γ.pathAct .one (oppositePath Γ.m) h' F`. Rewrite using `[← Grid.pathAct_mul, hcomm, Grid.pathAct_mul, hF]`. Establish `hmv : moved Γ keep h' F = fun z => (((Γ.mu 1 (gdet κ))⁻¹ : ℂˣ) : ℂ) * moved Γ keep h' F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, 0) g) z)`. Use function extensionality and compare the values at `z`.

Use `congrFun hinv z` as an intermediate fact. Rewrite `this` using `[Grid.pathAct, prod_edgeFactor_end (by omega) hη g (by rw [hgd, hκ]), hgd]`. Rewrite using `[moved, moved, ← this]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `_ * flatTensor hs ψ ν (moved Γ keep h' F) _ _ = flatTensor hs ψ ν (moved Γ keep h' F) _ _`.

Rewrite using `[← flatTensor_moveEnd hs ψ ν (moved Γ keep h' F) hm g κ hκ h x y]`. Use `conv_rhs => rw [hmv]`. Simplify using `only [flatTensor, flatIntegrand, mul_assoc, integral_const_mul]`.
-/
theorem datum_end {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] {J : Γ.Level}
    (keep : Bool) (ρ : Reps hs J) {F : Γ.Args → ℂ} (hm : 2 ≤ Γ.m) (hη : IsUnram Γ.eta) (β : Cosets hs J)
    {κ : GL (Fin (topRank Γ 0)) k} (hκ : valuation k (gdet κ : k) = 1) {u : GL (Fin (Γ.rank (Γ.m, 0))) k}
    (hF : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (Γ.m, 0) u) F = F)
    (h : toFrame hs (show 0 < Γ.m by omega) (ρ.base * u * ρ.base⁻¹) = embX _ κ) (x : ColArgs Γ) (y : RowArgs Γ) :
    (((Γ.mu 1 (gdet κ))⁻¹ : ℂˣ) : ℂ) * (unfTerm ψ ν keep ρ F β).datum (Function.update x 0 (x 0 * κ.val)) y =
      (unfTerm ψ ν keep ρ F β).datum x y := by
  set h' := ρ.elt β with hh'
  have hb : h' (Γ.m, 0) = ρ.base := by rw [hh', Reps.elt, onColumn_apply]
  set g := ρ.base * u * ρ.base⁻¹ with hg
  have hgd : gdet g = gdet κ := by
    rw [← gdet_toFrame hs (show 0 < Γ.m by omega), h, gdet_embX]
  have hcomm : (Pi.mulSingle (Γ.m, 0) g : Γ.VertexGroup) * h' = h' * Pi.mulSingle (Γ.m, 0) u := by
    funext Y
    by_cases hY : Y = (Γ.m, 0)
    · subst hY; simp [hg, hb]
    · simp [hY]
  have hinv : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (Γ.m, 0) g) (Γ.pathAct .one (oppositePath Γ.m) h' F) =
      Γ.pathAct .one (oppositePath Γ.m) h' F := by
    rw [← Grid.pathAct_mul, hcomm, Grid.pathAct_mul, hF]
  have hmv : moved Γ keep h' F = fun z => (((Γ.mu 1 (gdet κ))⁻¹ : ℂˣ) : ℂ) *
      moved Γ keep h' F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, 0) g) z) := by
    funext z
    have := congrFun hinv z
    rw [Grid.pathAct, prod_edgeFactor_end (by omega) hη g (by rw [hgd, hκ]), hgd] at this
    rw [moved, moved, ← this]
    ring
  change _ * flatTensor hs ψ ν (moved Γ keep h' F) _ _ = flatTensor hs ψ ν (moved Γ keep h' F) _ _
  rw [← flatTensor_moveEnd hs ψ ν (moved Γ keep h' F) hm g κ hκ h x y]
  conv_rhs => rw [hmv]
  simp only [flatTensor, flatIntegrand, mul_assoc, integral_const_mul]

omit [MeasurableSpace k] [BorelSpace k] in

/- English proof (translation)
Take `⟨h1, h2⟩` from `GivenAdm.mem_glLatCong.1 hκ`. Establish `hfr : topRank Γ 0 + (Γ.m - 1 - 0) = Γ.rank (Γ.m, 0)` using `by have := topRank_add hs 0; omega`. Establish `hval : ∀ κ' : GL (Fin (topRank Γ 0)) k, ∀ a b, ((toFrame hs hm).symm (embX _ κ')).val a b = fromBlocks κ'.val 0 0 (1 : Matrix (Fin (Γ.m - 1 - 0)) (Fin (Γ.m - 1 - 0)) k) ((frame hfr).symm a) ((frame hfr).symm b)` using `fun _ _ _ => rfl`. Establish `hint : ∀ κ' : GL (Fin (topRank Γ 0)) k, (∀ a b, κ'.val a b ∈ 𝒪[k]) → ∀ a b, ((toFrame hs hm).symm (embX _ κ')).val a b ∈ 𝒪[k]` using `fun κ' h a b => by`. Rewrite using `[hval]`.

Apply the tactic sequence `rcases (frame hfr).symm a with a | a <;> rcases (frame hfr).symm b with b | b`. Conclude with `h a b`. Conclude with `zero_mem _`. Conclude with `zero_mem _`. Rewrite using `[fromBlocks_apply₂₂, Matrix.one_apply]`.

Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Use `⟨(toFrame hs hm).symm (embX _ κ), GivenAdm.mem_glLatCong.2 ⟨(mem_KO_iff _).2 ⟨hint κ ((mem_KO_iff _).1 h1).1, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv, ← map_inv]`. Conclude with `hint _ ((mem_KO_iff _).1 h1).2`.

Introduce `a b`. Take `⟨a, rfl⟩` from `(frame hfr).surjective a`. Take `⟨b, rfl⟩` from `(frame hfr).surjective b`. Rewrite using `[Matrix.sub_apply, hval, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`.

Use `h2 a b` as an intermediate fact. Simplify `this` using `[Matrix.one_apply]`. Apply the tactic sequence `all_goals simp [Matrix.one_apply]`. Rewrite using `[map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_inv_eq_iff_eq_mul, toFrame_stair]`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul, SplitFlip.diagGL_val]`. Express the relevant statement in the definitionally equal form `_ * fromBlocks κ.val 0 0 1 = fromBlocks κ.val 0 0 1 * _`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Matrix.one_apply]`. Use `split_ifs with hab`. Rewrite using `[hab]`.

Both sides reduce to the same expression.
-/
theorem exists_end_lift {Γ : Grid k} (hs : 1 ≤ Γ.s) (hm : 0 < Γ.m) (ϖ c : kˣ) (e : ℕ) {κ : GL (Fin (topRank Γ 0)) k}
    (hκ : κ ∈ glLatCong c (SplitFlip.stdLat k _)) :
    ∃ u ∈ glLatCong c (SplitFlip.stdLat k (Fin (Γ.rank (Γ.m, 0)))),
      toFrame hs hm (stair Γ ϖ e 0 * u * (stair Γ ϖ e 0)⁻¹) = embX _ κ := by
  obtain ⟨h1, h2⟩ := GivenAdm.mem_glLatCong.1 hκ
  have hfr : topRank Γ 0 + (Γ.m - 1 - 0) = Γ.rank (Γ.m, 0) := by have := topRank_add hs 0; omega
  have hval : ∀ κ' : GL (Fin (topRank Γ 0)) k, ∀ a b, ((toFrame hs hm).symm (embX _ κ')).val a b =
      fromBlocks κ'.val 0 0 (1 : Matrix (Fin (Γ.m - 1 - 0)) (Fin (Γ.m - 1 - 0)) k) ((frame hfr).symm a) ((frame hfr).symm b) :=
    fun _ _ _ => rfl
  have hint : ∀ κ' : GL (Fin (topRank Γ 0)) k, (∀ a b, κ'.val a b ∈ 𝒪[k]) →
      ∀ a b, ((toFrame hs hm).symm (embX _ κ')).val a b ∈ 𝒪[k] := fun κ' h a b => by
    rw [hval]
    rcases (frame hfr).symm a with a | a <;> rcases (frame hfr).symm b with b | b
    · exact h a b
    · exact zero_mem _
    · exact zero_mem _
    · rw [fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  refine ⟨(toFrame hs hm).symm (embX _ κ), GivenAdm.mem_glLatCong.2 ⟨(mem_KO_iff _).2 ⟨hint κ ((mem_KO_iff _).1 h1).1, ?_⟩, ?_⟩, ?_⟩
  · rw [← map_inv, ← map_inv]
    exact hint _ ((mem_KO_iff _).1 h1).2
  · intro a b
    obtain ⟨a, rfl⟩ := (frame hfr).surjective a
    obtain ⟨b, rfl⟩ := (frame hfr).surjective b
    rw [Matrix.sub_apply, hval, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b
    · have := h2 a b
      simpa [Matrix.one_apply] using this
    all_goals simp [Matrix.one_apply]
  · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_inv_eq_iff_eq_mul, toFrame_stair]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, SplitFlip.diagGL_val]
    change _ * fromBlocks κ.val 0 0 1 = fromBlocks κ.val 0 0 1 * _
    ext (a | a) (b | b) <;> simp [Matrix.one_apply]
    split_ifs with hab
    · rw [hab]
    · rfl

end EndVertex

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Grid.pathAct, Grid.lines₂, ← List.prod_map_mul]`. Use `congrArg List.prod (List.map_congr_left fun b hb => ?_)` and prove the remaining obligations. Take `⟨j, -, rfl⟩ | ⟨i, hi, rfl⟩` from `GivenAdm.mem_givenPath hb`. Simplify using `[Grid.edgeFactor, Grid.moveArgs, h0]`.

Conclude with `GivenAdm.row_law B Φ hL hw g hg i hi x`.
-/
theorem given_end {μ₀ : T} (hL : L.Is μ₀) (B : Frames G) {t : T} (Φ : G.Datum) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    {g : (locGrid G t w).VertexGroup} (hg : ∀ Y, g Y ∈ givenLevel G t w Y) (h0 : ∀ j, g (0, j) = 1) :
    (locGrid G t w).pathAct .one (SplitFlip.givenPath D.R.m) g
        ((locGrid G t w).lines₂ (SplitFlip.givenPath D.R.m) (givenDatum t w B Φ)) =
      (locGrid G t w).lines₂ (SplitFlip.givenPath D.R.m) (givenDatum t w B Φ) := by
  funext x
  simp only [Grid.pathAct, Grid.lines₂, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun b hb => ?_)
  obtain ⟨j, -, rfl⟩ | ⟨i, hi, rfl⟩ := GivenAdm.mem_givenPath hb
  · simp [Grid.edgeFactor, Grid.moveArgs, h0]
  · exact GivenAdm.row_law B Φ hL hw g hg i hi x

/- English proof (translation)
Establish `hg` using `(Good.locGrid_isGood hL G W t hde hc).1 w hw`. Establish `hm : 0 < D.R.m` using `zero_lt_m D`. Establish `h00` using `hg.square 0 hm 0 hm`. Establish `hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2)`. Introduce `x hx`.

Simplify using `only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx`. Take `⟨i, hi, j, hj, rfl⟩` from `hx`. Rewrite using `[← Grid.alpha_div_beta]`. Conclude with `(hg.square i hi j hj).condν`. Establish `hg1 : ∀ x ∈ flipOrder D.R.m, (Pi.mulSingle (D.R.m, 0) u : (locGrid G t w).VertexGroup) x = 1`.

Introduce `x hx`. Simplify using `only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx`. Take `⟨i, hi, j, hj, rfl⟩` from `hx`. Conclude with `Pi.mulSingle_eq_of_ne (by simp; omega) _`. Establish `hJ : ∀ Y, (Pi.mulSingle (D.R.m, 0) u : (locGrid G t w).VertexGroup) Y ∈ givenLevel G t w Y` using `fun Y => by`.

Distinguish the cases in `hY : Y = (D.R.m, 0)`. Substitute `hY` using the available equality. Simplify using `using hu`. Rewrite using `[Pi.mulSingle_eq_of_ne hY]`. Conclude with `one_mem _`.

Establish `hbase` using `given_end hL B Φ hw hJ fun j => Pi.mulSingle_eq_of_ne (by simp; omega) _`. Establish `key` using `GlobalTheory.FirstRowEndLaw.flips_law h00.unif h00.cond h00.one_le _ (fun Y => (GivenAdm.givenLevel_open hL hw Y).2 (hJ Y)) 1 (flipOrder D.R.m) (givenStage t w B Φ) hν hg1 (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL B t …`. Express the relevant statement in the definitionally equal form `(locGrid G t w).pathAct .one (flipStage t w B W Φ).path _ (flipStage t w B W Φ).tensor = _ • (flipStage t w B W Φ).tensor at key`. Rewrite `key` using `[(flipStage_path_level t w B W Φ).1, one_smul]`. Conclude with `key`.
-/
theorem tflip_end {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    {u : GL (Fin ((locGrid G t w).rank (D.R.m, 0))) (Kw w)} (hu : u ∈ givenLevel G t w (D.R.m, 0)) :
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (D.R.m, 0) u) (Tflip W B t Φ w) = Tflip W B t Φ w := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := zero_lt_m D
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  have hg1 : ∀ x ∈ flipOrder D.R.m, (Pi.mulSingle (D.R.m, 0) u : (locGrid G t w).VertexGroup) x = 1 := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    exact Pi.mulSingle_eq_of_ne (by simp; omega) _
  have hJ : ∀ Y, (Pi.mulSingle (D.R.m, 0) u : (locGrid G t w).VertexGroup) Y ∈ givenLevel G t w Y := fun Y => by
    by_cases hY : Y = (D.R.m, 0)
    · subst hY; simpa using hu
    · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have hbase := given_end hL B Φ hw hJ fun j => Pi.mulSingle_eq_of_ne (by simp; omega) _
  have key := GlobalTheory.FirstRowEndLaw.flips_law h00.unif h00.cond h00.one_le _
    (fun Y => (GivenAdm.givenLevel_open hL hw Y).2 (hJ Y)) 1 (flipOrder D.R.m) (givenStage t w B Φ) hν hg1
    (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL B t Φ hw)
    (hbase.trans (one_smul _ _).symm)
  change (locGrid G t w).pathAct .one (flipStage t w B W Φ).path _ (flipStage t w B W Φ).tensor =
    _ • (flipStage t w B W Φ).tensor at key
  rw [(flipStage_path_level t w B W Φ).1, one_smul] at key
  exact key

/- English proof (translation)
Take `⟨e', -, hsupp, hF⟩` from `hexp`. Use `set g : FinPt G (.top 0) := (S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) with hg`. Establish `hhalf : ∀ j, IsHalf e' (firstPt t g x j) ↔ IsHalf e' (x j)` using `fun j => by`. Break down `eq_or_ne j ⟨0, zero_lt_m D⟩ with rfl | h1` into its components or cases. Simplify using `only [firstPt, Function.update_self]`.

Conclude with `GlobalTheory.SchrMove.isHalf_actO_iff _ _ _`. Simplify using `only [firstPt, Function.update_of_ne h1]`. Establish `hzero : ∀ x' : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)), ¬ ((∀ j', IsHalf e' (x' j')) ∧ ∀ i, IsHalf e' (y i)) → (τ.sum fun d a => a * (∏ j', (d.1 j').fn (x' j')) * ∏ i, (d.2 i).fn (y i)) = 0` using `fun x' hx' => by`. Use `Finset.sum_eq_zero fun d hd => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Use `hx' ⟨fun j' => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← ((hsupp d hd).1 j').2.1]`. Conclude with `(d.1 j').sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun j' => (d.1 j').fn (x' j')) (Finset.mem_univ j') h]; simp)`. Rewrite using `[← ((hsupp d hd).2 i).2.1]`. Conclude with `(d.2 i).sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun i => (d.2 i).fn (y i)) (Finset.mem_univ i) h]; simp)`.

Distinguish the cases in `hx : (∀ j', IsHalf e' (x j')) ∧ ∀ i, IsHalf e' (y i)`. Rewrite using `[hF _ y (fun j' => (hhalf j').2 (hx.1 j')) hx.2, hF x y hx.1 hx.2, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[colAt_firstPt S ht k w.2 x]`. Use `haveI := (isUnitVol_unitVol w.1).1`.

Establish `hκ` using `kapTop0_mem S t k hk w.1`. Take `⟨u, hu, hfr⟩` from `exists_end_lift (Γ := locGrid G t w.1) one_le_sLen (zero_lt_m D) (unifAt w.1) _ (cosExp G w.1) hκ`. Conclude with `datum_end (Γ := locGrid G t w.1) one_le_sLen _ _ _ (repsAt G t w.1) D.R.two_le_m ((Good.locGrid_isGood hL G W t hde hc).1 w.1 w.2).eta (β w) (GivenAdm.gdet_mem_unitCong hκ).1 (tflip_end hL W S.B t Φ hde hc w.2 hu) hfr _ _`. Rewrite using `[hzero x hx, hzero _ fun h => hx ⟨fun j' => (hhalf j').1 (h.1 j'), h.2⟩, mul_zero]`.
-/
theorem fn_invariant (S : GridChoice W U) {t μ₀ : T} (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U) {Φ : G.Datum}
    {β : CosFam G t} {τ : PureDat G t →₀ ℂ} (hexp : S.IsExpansion t Φ β τ) (k : FinPt G (.top 0))
    (hk : finG (G.V (.top 0)) k ∈ G.Kplus)
    (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    (∏ w : locPl G t, ((((locGrid G t w).mu 1 (gdet (kapTop0 S t k w)))⁻¹ : ℂˣ) : ℂ)) *
      (τ.sum fun d a => a * (∏ j, (d.1 j).fn (firstPt t ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) x j)) *
        ∏ i, (d.2 i).fn (y i)) =
      τ.sum fun d a => a * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i) := by
  classical
  obtain ⟨e', -, hsupp, hF⟩ := hexp
  set g : FinPt G (.top 0) := (S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) with hg
  have hhalf : ∀ j, IsHalf e' (firstPt t g x j) ↔ IsHalf e' (x j) := fun j => by
    rcases eq_or_ne j ⟨0, zero_lt_m D⟩ with rfl | h1
    · simp only [firstPt, Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · simp only [firstPt, Function.update_of_ne h1]
  have hzero : ∀ x' : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      ¬ ((∀ j', IsHalf e' (x' j')) ∧ ∀ i, IsHalf e' (y i)) →
      (τ.sum fun d a => a * (∏ j', (d.1 j').fn (x' j')) * ∏ i, (d.2 i).fn (y i)) = 0 := fun x' hx' => by
    refine Finset.sum_eq_zero fun d hd => ?_
    by_contra h0
    refine hx' ⟨fun j' => ?_, fun i => ?_⟩
    · rw [← ((hsupp d hd).1 j').2.1]
      exact (d.1 j').sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun j' => (d.1 j').fn (x' j')) (Finset.mem_univ j') h]; simp)
    · rw [← ((hsupp d hd).2 i).2.1]
      exact (d.2 i).sb.1 _ fun h => h0 (by beta_reduce; rw [Finset.prod_eq_zero (f := fun i => (d.2 i).fn (y i)) (Finset.mem_univ i) h]; simp)
  by_cases hx : (∀ j', IsHalf e' (x j')) ∧ ∀ i, IsHalf e' (y i)
  · rw [hF _ y (fun j' => (hhalf j').2 (hx.1 j')) hx.2, hF x y hx.1 hx.2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [colAt_firstPt S ht k w.2 x]
    haveI := (isUnitVol_unitVol w.1).1
    have hκ := kapTop0_mem S t k hk w.1
    obtain ⟨u, hu, hfr⟩ := exists_end_lift (Γ := locGrid G t w.1) one_le_sLen (zero_lt_m D) (unifAt w.1) _ (cosExp G w.1) hκ
    exact datum_end (Γ := locGrid G t w.1) one_le_sLen _ _ _ (repsAt G t w.1) D.R.two_le_m
      ((Good.locGrid_isGood hL G W t hde hc).1 w.1 w.2).eta (β w) (GivenAdm.gdet_mem_unitCong hκ).1
      (tflip_end hL W S.B t Φ hde hc w.2 hu) hfr _ _
  · rw [hzero x hx, hzero _ fun h => hx ⟨fun j' => (hhalf j').1 (h.1 j'), h.2⟩, mul_zero]

/- English proof (translation)
Establish `h2` using `GlobalTheory.LastColLat.conj_stab S.N (X := .top 0) (by simp [DefNode]) k (mem_congLev.1 hk).2.1`. Establish `h3` using `GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ _ _ h2`. Use `set g : GA D (G.V (.top 0)) := (((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) : FinPt G (.top 0)) : GA D (G.V (.top 0)))`. Establish `h4` using `GlobalTheory.LatStabScalar.keeps_inv h3`. Establish `h1 : ∀ y ∈ latHat D.host.F D.host.E (S.N.latT (.top t 0) : Set (Fin (G.pT (.top t 0 : Pair T)).rank → D.host.E)), ((Formalism.L2.Theta.mt (G.pT (.top t 0 : Pair T)) 1).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (S.N.latT (.top t 0) : Set (Fin (G.pT (.top t 0 : Pair T)). …` using `fun y hy => by`.

Rewrite using `[GlobalTheory.LatStabScalar.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]` and apply the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `GlobalTheory.LocalLatStab.actO_mem _ _ _ _ _ g 1 (fun y hy => (h3 y).1 hy) h1 _ hx` as an intermediate fact. Rewrite `this` using `[GlobalTheory.AdelicLatMove.actO_actO_inv]`. Then use the resulting hypothesis.

Introduce `hx`. Rewrite using `[inv_one]`. Conclude with `GlobalTheory.LocalLatStab.actO_mem _ _ _ _ _ g⁻¹ 1 (fun y hy => (h4 y).1 hy) h1 _ hx`.
-/
theorem first_mem_stdLat_iff (S : GridChoice W U) (t : T) (k : FinPt G (.top 0)) (hk : finG (G.V (.top 0)) k ∈ G.Kplus)
    (x : WO (G.pS (.top t 0 : Pair T)) (G.pT (.top t 0 : Pair T))) :
    actO _ _ (((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) : FinPt G (.top 0)) : GA D (G.V (.top 0)))⁻¹ 1⁻¹ x ∈
      GlobalTheory.LastVertexMove.stdLat S (.top t 0) ↔ x ∈ GlobalTheory.LastVertexMove.stdLat S (.top t 0) := by
  have h2 := GlobalTheory.LastColLat.conj_stab S.N (X := .top 0) (by simp [DefNode]) k (mem_congLev.1 hk).2.1
  have h3 := GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ _ _ h2
  set g : GA D (G.V (.top 0)) := (((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) : FinPt G (.top 0)) : GA D (G.V (.top 0)))
  have h4 := GlobalTheory.LatStabScalar.keeps_inv h3
  have h1 : ∀ y ∈ latHat D.host.F D.host.E (S.N.latT (.top t 0) : Set (Fin (G.pT (.top t 0 : Pair T)).rank → D.host.E)),
      ((Formalism.L2.Theta.mt (G.pT (.top t 0 : Pair T)) 1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.top t 0) : Set (Fin (G.pT (.top t 0 : Pair T)).rank → D.host.E)) := fun y hy => by
    rwa [GlobalTheory.LatStabScalar.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  constructor
  · intro hx
    have := GlobalTheory.LocalLatStab.actO_mem _ _ _ _ _ g 1 (fun y hy => (h3 y).1 hy) h1 _ hx
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  · intro hx
    rw [inv_one]
    exact GlobalTheory.LocalLatStab.actO_mem _ _ _ _ _ g⁻¹ 1 (fun y hy => (h4 y).1 hy) h1 _ hx

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D T L sc G W U S t ht Φ β τ μ₀ hL hde hc _ _ hexp hv k hk z`. Establish `hfn` using `fn_invariant S hL hde hc ht hexp k hk`. Establish `hvac` using `om_first_vac S hL t k hk`. Generalize the expression as in `(∏ w : locPl G t, ((((locGrid G t w).mu 1 (gdet (kapTop0 S t k w)))⁻¹ : ℂˣ) : ℂ)) = c at hfn hvac`. Establish `hlat` using `first_mem_stdLat_iff S t k hk`.

Use `set g : FinPt G (.top 0) := (S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) with hg`. Take `⟨e, he, hsupp, -⟩` from `hexp`. Simplify using `only [Finsupp.sum] at hfn ⊢`. Break down `Finset.eq_empty_or_nonempty τ.support with h0 | ⟨d₀, hd₀⟩` into its components or cases. Simplify using `[h0]`.

Establish `hT : ∀ l : Arr D, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (arrP t l)) 1 (S.Z.vac (arrP t l)) Tm`. Introduce and unpack `(j | i)`. Take `⟨f, hf⟩` from `(hv d₀ hd₀).1 j`. Unfold `FinDatum.IsTheta at hf`. Rewrite `hf` using `[((hsupp d₀ hd₀).1 j).2.1]`.

Conclude with `hf.1`. Take `⟨f, hf⟩` from `(hv d₀ hd₀).2 i`. Unfold `FinDatum.IsTheta at hf`. Rewrite `hf` using `[((hsupp d₀ hd₀).2 i).2.1]`. Conclude with `hf.1`.

Use `choose Tm hTm using hT`. Establish `hvec : ∀ d ∈ τ.support, ∀ l, vecsOf S d l = Tm l (datFn d l)`. Introduce and unpack `d hd (j | i)`. Conclude with `vec_eq_model S (d.1 j) ((hsupp d hd).1 j).2.2 ((hv d hd).1 j) _ (((hsupp d hd).1 j).2.1 ▸ hTm (.inl j))`. Conclude with `vec_eq_model S (d.2 i) ((hsupp d hd).2 i).2.2 ((hv d hd).2 i) _ (((hsupp d hd).2 i).2.1 ▸ hTm (.inr i))`.

Set `F' : PureDat G t → ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ` to `fun d => Function.update (datFn d) first fun y => (d.1 ⟨0, zero_lt_m D⟩).fn (actO _ _ (g : GA D (G.V (.top 0)))⁻¹ 1⁻¹ y)`. Establish `hp : DefPair D.R.m (.top t 0 : Pair T)` using `show 0 + 1 ≤ D.R.m from zero_lt_m D`. Establish `hmove : ∀ d ∈ τ.support, ∏ l, moveFirst W g (vecsOf S d) l (z l) = c * ∏ l, Tm l (F' d l) (z l)` using `fun d hd => by`. Establish `hsb` using `GlobalTheory.LastVertexMove.isSBHalf_stdLat S ht hp (d.1 ⟨0, zero_lt_m D⟩) ((hsupp d hd).1 _).1`. Rewrite `hsb` using `[((hsupp d hd).1 _).2.1]`.

Establish `h1` using `GlobalTheory.LastVertexTensor.om_model S hp (show 0 + 1 ≤ D.R.m from zero_lt_m D) he (Tm first) (hTm first) (G.toPair (.top t 0 : Pair T) g.1 1) c hlat hvac _ hsb`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ first), ← Finset.mul_prod_erase _ _ (Finset.mem_univ first), ← mul_assoc]`. Use `congr 1`. Simplify using `only [moveFirst, F', Function.update_self, hvec d hd]`. Conclude with `congrFun h1 (z first)`.

Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hne` using `Finset.ne_of_mem_erase hl`. Establish `a1 : moveFirst W g (vecsOf S d) l = vecsOf S d l` using `Function.update_of_ne hne _ _`. Establish `a2 : F' d l = datFn d l` using `Function.update_of_ne hne _ _`. Rewrite using `[a1, a2, hvec d hd]`.

Establish `key` using `sum_prod_map_congr Tm τ.support τ.support (fun d => τ d) (fun d => τ d * c) datFn F' (fun x => by`. Establish `h1` using `hfn (fun j => x (.inl j)) (fun i => x (.inr i))`. Rewrite `h1` using `[Finset.mul_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun d _ => ?_) (h1.trans (Finset.sum_congr rfl fun d _ => ?_))` and prove the remaining obligations. Establish `e1 : ∀ j, F' d (.inl j) (x (.inl j)) = (d.1 j).fn (firstPt t g (fun j => x (.inl j)) j)` using `fun j => by`.

Break down `eq_or_ne j ⟨0, zero_lt_m D⟩ with rfl | hj` into its components or cases. Simplify using `only [firstPt, Function.update_self]`. Conclude with `congrFun (Function.update_self first _ (datFn d)) _`. Establish `a1 : firstPt t g (fun j => x (.inl j)) j = x (.inl j)` using `Function.update_of_ne hj _ _`. Rewrite using `[a1]`.

Conclude with `congrFun (Function.update_of_ne (show (Sum.inl j : Arr D) ≠ first from fun h => hj (Sum.inl.inj h)) _ (datFn d)) _`. Establish `e2 : ∀ i, F' d (.inr i) (x (.inr i)) = (d.2 i).fn (x (.inr i))` using `fun i => congrFun (Function.update_of_ne (show (Sum.inr i : Arr D) ≠ first from Sum.inr_ne_inl) _ (datFn d)) _`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Fintype.prod_sum_type, mul_assoc] rfl) z`. Use `Eq.trans (Finset.sum_congr rfl fun d hd => ?_) (key.trans (Finset.sum_congr rfl fun d hd => ?_))` and prove the remaining obligations. Rewrite using `[hmove d hd, mul_assoc]`. Simplify using `only [hvec d hd]`.
-/
theorem product_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.top 0), finG (G.V (.top 0)) k ∈ G.Kplus →
    ∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (τ.sum fun d b => b * ∏ l, moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l (z l)) =
        τ.sum fun d b => b * ∏ l, vecsOf S d l (z l) := by
  intro D T L sc G W U S t ht Φ β τ μ₀ hL hde hc _ _ hexp hv k hk z
  classical
  have hfn := fn_invariant S hL hde hc ht hexp k hk
  have hvac := om_first_vac S hL t k hk
  generalize (∏ w : locPl G t, ((((locGrid G t w).mu 1 (gdet (kapTop0 S t k w)))⁻¹ : ℂˣ) : ℂ)) = c at hfn hvac
  have hlat := first_mem_stdLat_iff S t k hk
  set g : FinPt G (.top 0) := (S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0) with hg
  obtain ⟨e, he, hsupp, -⟩ := hexp
  simp only [Finsupp.sum] at hfn ⊢
  rcases Finset.eq_empty_or_nonempty τ.support with h0 | ⟨d₀, hd₀⟩
  · simp [h0]
  have hT : ∀ l : Arr D, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (arrP t l)) 1 (S.Z.vac (arrP t l)) Tm := by
    rintro (j | i)
    · obtain ⟨f, hf⟩ := (hv d₀ hd₀).1 j
      unfold FinDatum.IsTheta at hf
      rw [((hsupp d₀ hd₀).1 j).2.1] at hf
      exact hf.1
    · obtain ⟨f, hf⟩ := (hv d₀ hd₀).2 i
      unfold FinDatum.IsTheta at hf
      rw [((hsupp d₀ hd₀).2 i).2.1] at hf
      exact hf.1
  choose Tm hTm using hT
  have hvec : ∀ d ∈ τ.support, ∀ l, vecsOf S d l = Tm l (datFn d l) := by
    rintro d hd (j | i)
    · exact vec_eq_model S (d.1 j) ((hsupp d hd).1 j).2.2 ((hv d hd).1 j) _ (((hsupp d hd).1 j).2.1 ▸ hTm (.inl j))
    · exact vec_eq_model S (d.2 i) ((hsupp d hd).2 i).2.2 ((hv d hd).2 i) _ (((hsupp d hd).2 i).2.1 ▸ hTm (.inr i))
  let F' : PureDat G t → ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ := fun d =>
    Function.update (datFn d) first fun y => (d.1 ⟨0, zero_lt_m D⟩).fn (actO _ _ (g : GA D (G.V (.top 0)))⁻¹ 1⁻¹ y)
  have hp : DefPair D.R.m (.top t 0 : Pair T) := show 0 + 1 ≤ D.R.m from zero_lt_m D
  have hmove : ∀ d ∈ τ.support, ∏ l, moveFirst W g (vecsOf S d) l (z l) = c * ∏ l, Tm l (F' d l) (z l) := fun d hd => by
    have hsb := GlobalTheory.LastVertexMove.isSBHalf_stdLat S ht hp (d.1 ⟨0, zero_lt_m D⟩) ((hsupp d hd).1 _).1
    rw [((hsupp d hd).1 _).2.1] at hsb
    have h1 := GlobalTheory.LastVertexTensor.om_model S hp (show 0 + 1 ≤ D.R.m from zero_lt_m D) he (Tm first) (hTm first)
      (G.toPair (.top t 0 : Pair T) g.1 1) c hlat hvac _ hsb
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ first), ← Finset.mul_prod_erase _ _ (Finset.mem_univ first), ← mul_assoc]
    congr 1
    · simp only [moveFirst, F', Function.update_self, hvec d hd]
      exact congrFun h1 (z first)
    · refine Finset.prod_congr rfl fun l hl => ?_
      have hne := Finset.ne_of_mem_erase hl
      have a1 : moveFirst W g (vecsOf S d) l = vecsOf S d l := Function.update_of_ne hne _ _
      have a2 : F' d l = datFn d l := Function.update_of_ne hne _ _
      rw [a1, a2, hvec d hd]
  have key := sum_prod_map_congr Tm τ.support τ.support (fun d => τ d) (fun d => τ d * c) datFn F' (fun x => by
    have h1 := hfn (fun j => x (.inl j)) (fun i => x (.inr i))
    rw [Finset.mul_sum] at h1
    refine Eq.trans (Finset.sum_congr rfl fun d _ => ?_) (h1.trans (Finset.sum_congr rfl fun d _ => ?_))
    · have e1 : ∀ j, F' d (.inl j) (x (.inl j)) = (d.1 j).fn (firstPt t g (fun j => x (.inl j)) j) := fun j => by
        rcases eq_or_ne j ⟨0, zero_lt_m D⟩ with rfl | hj
        · simp only [firstPt, Function.update_self]
          exact congrFun (Function.update_self first _ (datFn d)) _
        · have a1 : firstPt t g (fun j => x (.inl j)) j = x (.inl j) := Function.update_of_ne hj _ _
          rw [a1]
          exact congrFun (Function.update_of_ne (show (Sum.inl j : Arr D) ≠ first from fun h => hj (Sum.inl.inj h)) _ (datFn d)) _
      have e2 : ∀ i, F' d (.inr i) (x (.inr i)) = (d.2 i).fn (x (.inr i)) := fun i =>
        congrFun (Function.update_of_ne (show (Sum.inr i : Arr D) ≠ first from Sum.inr_ne_inl) _ (datFn d)) _
      rw [Fintype.prod_sum_type]
      simp only [e1, e2]
      ring
    · rw [Fintype.prod_sum_type, mul_assoc]
      rfl) z
  refine Eq.trans (Finset.sum_congr rfl fun d hd => ?_) (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [hmove d hd, mul_assoc]
  · simp only [hvec d hd]

end GlobalTheory.TopZeroFirst

end
