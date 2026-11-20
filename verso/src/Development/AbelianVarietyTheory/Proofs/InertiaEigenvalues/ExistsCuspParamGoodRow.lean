import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspOfGoodRow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NodupIntShift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

/- English proof (translation)
Unfold `isoInf`. Rewrite using `[List.map_append, List.sum_append]`.
-/
theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

/- English proof (translation)
Unfold `isoInf`. Conclude with `(h.map _).sum_eq`.
-/
theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

/- English proof (translation)
Break down `h with rfl | rfl` into its components or cases. Use `⟨fun _ => rfl, fun h' => ?_⟩` and prove the remaining obligations. Rewrite `h'` using `[Multiset.map_singleton, Multiset.singleton_inj]`. Evaluate the numerical expressions using `at h'`. Use `⟨fun h' => ?_, fun _ => rfl⟩` and prove the remaining obligations.

Rewrite `h'` using `[Multiset.map_singleton, Multiset.singleton_inj]`. Evaluate the numerical expressions using `at h'`.
-/
theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

/- English proof (translation)
Simplify using `[isoInf]`.
-/
theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

/- English proof (translation)
Introduce `D Rw hP j σ π μ Pa hL hR hB hm hg`. Establish `hLP : SumRepresentations.At.TieLP D.nd D.naut` using `hP.tie0.1`. Establish `hAut : SumRepresentations.At.TieAut D.nd D.naut` using `hP.tie0.2.1`. Establish `hC` using `hP.cancel`. Take `⟨l₁, l₂, rfl⟩` from `List.append_of_mem hm`.

Use `set m : Part D.naut.CG := ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ with hmdef`. Use `set L := l₁ ++ l₂ with hLdef`. Establish `hperm : (l₁ ++ m :: l₂).Perm (L ++ [m])` using `List.perm_middle.trans (List.perm_append_singleton _ _).symm`. Establish `hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂` using `fun p hp => by`. Break down `List.mem_append.1 hp with h | h` into its components or cases.

Conclude with `List.mem_append_left _ h`. Conclude with `List.mem_append_right _ (List.mem_cons_of_mem _ h)`. Take `⟨hB1, -, hB3, hB4, hB5, hB6⟩` from `hB`. Establish `hpos : ∀ p ∈ twistIso D.nd D.naut L D.naut.etaT, 1 ≤ p.a ∧ 1 ≤ p.d`. Introduce `p hp`.

Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hp`. Conclude with `⟨(hB1 q (hLmem q hq)).1, (hB1 q (hLmem q hq)).2.1⟩`. Establish `hrank : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = D.R.r`. Establish `e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L`. Unfold `rankIso twistIso`.

Rewrite using `[List.map_map]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Establish `hr : rankIso D.nd D.naut (L ++ [m]) = D.R.nV`. Rewrite using `[← hB3]`.

Unfold `rankIso`. Conclude with `((hperm.map _).sum_eq).symm`. Unfold `rankIso at hr ⊢`. Rewrite `hr` using `[List.map_append, List.sum_append]`. Simplify using `only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr`.

Establish `: D.R.nV = D.R.r + D.R.t` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hloc : ∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) w = Rw.locR σ w`. Introduce `w hw`. Establish `e1` using `hB4 w hw`.

Rewrite `e1` using `[hL.loc w hw, GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, (hLP w (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w) (D.naut.locG_dim _ w) …`. Establish `e2 : isoLoc D.nd D.naut [m] w = D.naut.lpChar (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w)`. Rewrite using `[GlobalTheory.RowThetaParam.isoLoc_cons, GlobalTheory.RowThetaParam.isoLoc_nil, D.naut.lpSum_zero]`. Conclude with `GlobalTheory.RowThetaParam.spehLoc_tw D.nd D.naut hLP hC ⟨1, μ, D.R.t⟩ D.naut.etaTinv w`. Rewrite `e1` using `[e2]`.

Establish `e3` using `hC w _ _ _ e1`. Rewrite using `[GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, e3, (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2]`. Take `⟨π', hπ'⟩` from `GlobalTheory.RowCuspLabels.cusp_of_goodRow D Rw hP.lab σ hg _ hpos hrank hloc`. Take `⟨q, hLq, hq⟩` from `List.map_eq_singleton_iff.1 (show L.map _ = _ from hπ')`. Take `⟨a, ρ, d⟩` from `q`.

Simplify using `only [Formalism.BasicNotions.Part.mk.injEq] at hq`. Take `⟨rfl, h2, rfl⟩` from `hq`. Establish `h2'` using `eq_of_heq h2`. Substitute `h2'` using the available equality. Establish `hmemq : (⟨D.R.r, ρ, 1⟩ : Part D.naut.CG) ∈ l₁ ++ m :: l₂` using `hLmem _ (by rw [hLq]; exact List.mem_singleton_self _)`.

Establish `hsplit : ∀ w, IsSplitPl D.host w → D.naut.locG (D.naut.tw ρ D.naut.etaT) w = Rw.locR σ w`. Introduce `w hw`. Establish `hs` using `hloc w hw`. Rewrite `hs` using `[hπ', SphericalInertData.isoLoc_single]`. Conclude with `hs`.

Establish `hinf : ∀ τ : D.what₂.Tau, D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) ∧ D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSid …`. Introduce `τ`. Establish `eA` using `hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)`. Establish `eB` using `hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)`. Rewrite `eA` using `[isoInf_perm D hperm, isoInf_append, (hL.inf τ).1]`.

Rewrite `eB` using `[isoInf_perm D hperm, isoInf_append, (hL.inf τ).2]`. Establish `fA` using `add_right_cancel eA`. Establish `fB` using `add_right_cancel eB`. Rewrite `fA`, `fB` using `[hLq, isoInf_one]`. Establish `gA` using `(eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1).1 (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2).symm.trans (hL.eta τ).1)`.

Establish `gB` using `(eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).1).2 (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).2).symm.trans (hL.eta τ).2)`. Rewrite using `[D.naut.infG_tw _ _ _ _ gA, D.naut.infG_tw _ _ _ _ gB, fA, fB]`. Simplify using `[Multiset.map_map, Function.comp_def]`. Use `⟨D.naut.tw ρ D.naut.etaT, D.naut.csd_tw ρ D.naut.etaT hAut.1.1 (hB1 _ hmemq).2.2, GlobalTheory.RowRegAlg.ralg_of_infG D _ hinf, hsplit, fun w hw => ?_, fun w hw hw' => ?_, hinf⟩` and prove the remaining obligations. Establish `hu` using `(hB5 w hw).1`.

Rewrite `hu` using `[GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.unr_sum, hLq, SphericalInertData.isoLoc_single]`. Rewrite using `[D.naut.locG_tw]`. Conclude with `D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu.1 (D.naut.etaT_unr w)`. Rewrite using `[hsplit w hw]`. Conclude with `(hR w hw hw').1`.
-/
theorem cuspParam_of_lift : ∀ (D : D7) (Rw : RowSide D), ParLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa →
    D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  intro D Rw hP j σ π μ Pa hL hR hB hm hg
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := hP.tie0.1
  have hAut : SumRepresentations.At.TieAut D.nd D.naut := hP.tie0.2.1
  have hC := hP.cancel
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  obtain ⟨hB1, -, hB3, hB4, hB5, hB6⟩ := hB

  have hpos : ∀ p ∈ twistIso D.nd D.naut L D.naut.etaT, 1 ≤ p.a ∧ 1 ≤ p.d := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hB1 q (hLmem q hq)).1, (hB1 q (hLmem q hq)).2.1⟩
  have hrank : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = D.R.r := by
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    have hr : rankIso D.nd D.naut (L ++ [m]) = D.R.nV := by
      rw [← hB3]; unfold rankIso; exact ((hperm.map _).sum_eq).symm
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hloc : ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have e1 := hB4 w hw
    rw [hL.loc w hw, GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append,
      (hLP w (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)
        (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w)
        (D.naut.locG_dim _ w)).1] at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [GlobalTheory.RowThetaParam.isoLoc_cons, GlobalTheory.RowThetaParam.isoLoc_nil, D.naut.lpSum_zero]
      exact GlobalTheory.RowThetaParam.spehLoc_tw D.nd D.naut hLP hC ⟨1, μ, D.R.t⟩ D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, e3,
      (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2]
  obtain ⟨π', hπ'⟩ := GlobalTheory.RowCuspLabels.cusp_of_goodRow D Rw hP.lab σ hg _ hpos hrank hloc
  obtain ⟨q, hLq, hq⟩ := List.map_eq_singleton_iff.1 (show L.map _ = _ from hπ')
  obtain ⟨a, ρ, d⟩ := q
  simp only [Formalism.BasicNotions.Part.mk.injEq] at hq
  obtain ⟨rfl, h2, rfl⟩ := hq
  have h2' := eq_of_heq h2
  subst h2'
  have hmemq : (⟨D.R.r, ρ, 1⟩ : Part D.naut.CG) ∈ l₁ ++ m :: l₂ := hLmem _ (by rw [hLq]; exact List.mem_singleton_self _)
  have hsplit : ∀ w, IsSplitPl D.host w → D.naut.locG (D.naut.tw ρ D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have hs := hloc w hw
    rw [hπ', SphericalInertData.isoLoc_single] at hs
    exact hs
  have hinf : ∀ τ : D.what₂.Tau, D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) ∧
      D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun z => -z) := by
    intro τ
    have eA := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)
    have eB := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).1] at eA
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).2] at eB
    have fA := add_right_cancel eA
    have fB := add_right_cancel eB
    rw [hLq, isoInf_one] at fA fB
    have gA := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1).1
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2).symm.trans (hL.eta τ).1)
    have gB := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).1).2
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).2).symm.trans (hL.eta τ).2)
    rw [D.naut.infG_tw _ _ _ _ gA, D.naut.infG_tw _ _ _ _ gB, fA, fB]
    simp [Multiset.map_map, Function.comp_def]
  refine ⟨D.naut.tw ρ D.naut.etaT, D.naut.csd_tw ρ D.naut.etaT hAut.1.1 (hB1 _ hmemq).2.2, GlobalTheory.RowRegAlg.ralg_of_infG D _ hinf, hsplit,
    fun w hw => ?_, fun w hw hw' => ?_, hinf⟩
  · have hu := (hB5 w hw).1
    rw [GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.unr_sum, hLq,
      SphericalInertData.isoLoc_single] at hu
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu.1 (D.naut.etaT_unr w)
  · rw [hsplit w hw]
    exact (hR w hw hw').1

end GlobalTheory.RowCuspFromLift

end
