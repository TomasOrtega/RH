import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackTwistPlaceProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

/- English proof (translation)
Introduce `D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Use `GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])` as an intermediate fact. Establish `e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0` using `by show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0`.

Rewrite using `[show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]`. Rewrite `this` using `[e0, sub_zero]`. Then use the resulting hypothesis. Introduce `hv`. Take `⟨z, hz⟩` from `Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)`. Establish `h1` using `GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz`.

Establish `h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1`. Establish `e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E))` using `by ring`. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)`. Take `⟨π', hπ, hred, -⟩` from `GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP`.

Establish `h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z)` using `(hπ _).symm`. Rewrite `h2` using `[h6, ← hred.ker, Formalism.L2.DIV.resS_oToS]`. Rewrite using `[← hz, h2]`.
-/
theorem GlobalTheory.TopLevQ.red_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) V t β N → (Formalism.L2.Theta.mt V h).map q.pr * N = N * M → Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β → ∀ i j, ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j = 0 ↔ ValuativeRel.valuation k (M i j) < 1) := by
  intro D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j
  constructor
  · intro h0
    have := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])
    have e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0 := by
      show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0
      rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]
    rwa [e0, sub_zero] at this
  · intro hv
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)
    have h1 := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz
    have h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1 := by
      have e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
    obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
    have h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
    rw [h6, ← hred.ker, Formalism.L2.DIV.resS_oToS] at h2
    rw [← hz, h2]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg`. Establish `hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁` using `by show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _`. Rewrite using `[GlobalTheory.StepData.Level.mem_map]`. Establish `e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x`. Use extensionality with `i j`.

Simplify using `[GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `GlobalTheory.StepData.mem_parahoric`. Rewrite using `[hTop]`.

Take `⟨e, he, hmv⟩` from `(a.Q PP ⟨t, hP⟩).frameTop`. Establish `hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (I.rec7 l Z).sp.X' a.g.bT (pk W).βX ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm)` using `hmv`. Establish `hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP` using `(a.Q PP ⟨t, hP⟩).idem`. Establish `hβX : Formalism.IndefR.Links.IsSDFrame (I.rec7 l Z).sp.X' (pk W).βX (pk W).ΛX 1` using `W.Q.charW.base.lev.βX`. Take `⟨hGfC, hStIff, hoff⟩` from `GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (I.rec7 l Z) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX (pk W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg`.

Take `⟨hsupp, hmat⟩` from `hg`. Establish `hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm = (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm`. Establish `h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ` using `hmat`. Rewrite using `[h1]`. Conclude with `GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e`.

Establish `hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT)` using `GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp`. Establish `hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1)`. Use `(a.Q PP ⟨t, hP⟩).hs` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.

Establish `hPg` using `(GlobalTheory.PkFrame.pk_frame_places W hW t PP hP 0 (by have := (a.Q PP ⟨t, hP⟩).hs; omega)).2`. Establish `hord` using `GlobalTheory.TopLevQ.blk_iff e he x.val`. Rewrite `hord` using `[← hr]`. Rewrite using `[GlobalTheory.TopLevQ.mem_levS_iff]`. Establish `hred` using `GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX a.g.bT g _ _ hmv' hM`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, ⟨hSt, -, hQt⟩, -⟩`. Use `⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩` and prove the remaining obligations. Conclude with `(hQt PP hP) hij`. Introduce and unpack `⟨hx', hmax⟩`.

Establish `hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (pk W).βX` using `hStIff.2 hx'`. Establish `hone : ∀ PP' : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) → Formalism.L2.DIV.redFn (pk W).βX PP' (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1` using `fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne`. Use `⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hone PP' (hPg PP' hPP')]`. Conclude with `Subgroup.one_mem _`.

Distinguish the cases in `hPe : PP' = PP`. Substitute `hPe` using the available equality. Introduce `i j hij`. Conclude with `(hred hSt i j).2 (hord.2 hmax i j hij)`. Rewrite using `[hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]`.

Conclude with `Subgroup.one_mem _`. Establish `h1 : Formalism.L2.DIV.rTup (pk W).βX (datXP (pk W) (lvP W) t) (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1`. Use function extensionality and compare the values at `PP'`. Use `show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (pk W).βX PP'.1 _) = 1`. Rewrite using `[hone PP'.1 (hPg PP'.1 PP'.2)]`.

Conclude with `Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _`. Rewrite using `[h1]`. Conclude with `Subgroup.one_mem _`.
-/
theorem GlobalTheory.TopLevQ.mem_levS_top_iff : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg
  have hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁ := by
    show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _
    rw [GlobalTheory.StepData.Level.mem_map]
    have e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x := by
      ext i j
      simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]
      rfl
    rw [e1]
    exact GlobalTheory.StepData.mem_parahoric
  rw [hTop]
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frameTop
  have hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (I.rec7 l Z).sp.X' a.g.bT (pk W).βX
      ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm) := hmv
  have hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP := (a.Q PP ⟨t, hP⟩).idem
  have hβX : Formalism.IndefR.Links.IsSDFrame (I.rec7 l Z).sp.X' (pk W).βX (pk W).ΛX 1 := W.Q.charW.base.lev.βX
  obtain ⟨hGfC, hStIff, hoff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (I.rec7 l Z) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX
    (pk W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg
  obtain ⟨hsupp, hmat⟩ := hg
  have hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm =
      (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm := by
    have h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ := hmat
    rw [h1]
    exact GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e
  have hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT) := GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Ranks.r
    omega
  have hPg := (GlobalTheory.PkFrame.pk_frame_places W hW t PP hP 0 (by have := (a.Q PP ⟨t, hP⟩).hs; omega)).2
  have hord := GlobalTheory.TopLevQ.blk_iff e he x.val
  rw [← hr] at hord
  rw [GlobalTheory.TopLevQ.mem_levS_iff]
  have hred := GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX a.g.bT g _ _ hmv' hM
  constructor
  · rintro ⟨-, ⟨hSt, -, hQt⟩, -⟩
    refine ⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩
    exact (hQt PP hP) hij
  · rintro ⟨hx', hmax⟩
    have hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (pk W).βX := hStIff.2 hx'
    have hone : ∀ PP' : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) →
        Formalism.L2.DIV.redFn (pk W).βX PP' (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 :=
      fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne
    refine ⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩
    · rw [hone PP' (hPg PP' hPP')]
      exact Subgroup.one_mem _
    · by_cases hPe : PP' = PP
      · subst hPe
        intro i j hij
        exact (hred hSt i j).2 (hord.2 hmax i j hij)
      · rw [hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]
        exact Subgroup.one_mem _
    · have h1 : Formalism.L2.DIV.rTup (pk W).βX (datXP (pk W) (lvP W) t) (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 := by
        funext PP'
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (pk W).βX PP'.1 _) = 1
        rw [hone PP'.1 (hPg PP'.1 PP'.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact Subgroup.one_mem _

end
