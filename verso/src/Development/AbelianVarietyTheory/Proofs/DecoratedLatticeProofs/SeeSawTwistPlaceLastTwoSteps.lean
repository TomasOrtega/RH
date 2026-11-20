import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvariStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QLastOne

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u`. Take `⟨hfin, -, hsymm, htrans, hstab⟩` from `GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable D c v χ Q`. Establish `hcomb : ∀ {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame Q.k S.rank Y') (FT : GlobalTheory.LocMod.Frame Q.k T.rank Y) (Ξ : Matrix Y Y' Q.k → ℂ), Ξ ∈ SB _ → ∃ d, (ofSplit Q.q).IsCombAt c.ψ FS FT d Ξ`. Introduce `S T Y Y' _ _ _ _ FS FT Ξ hΞ`. Set `O : SB (Matrix Y Y' Q.k)` to `⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Y Y'⟩`.

Establish `hO : O ≠ 0`. Introduce `h0`. Use `congrFun (congrArg Subtype.val h0) 0` as an intermediate fact. Simplify using `[O, Set.indicator_apply] at this`. Take `⟨d, hd, hT⟩` from `GlobalTheory.T.exists_heisenberg_combination_split_place_datum D Q.k (ofSplit Q.q) Y Y' S T FS FT c.ψ hc.std O ⟨Ξ, hΞ⟩ hO`.

Use `⟨d, hd, fun Tm hTm Φ₀ Φ h0 h1 => ?_⟩` and prove the remaining obligations. Establish `e0 : Φ₀ = O` using `Subtype.ext h0`. Establish `e1 : Φ = ⟨Ξ, hΞ⟩` using `Subtype.ext h1`. Rewrite using `[e0, e1]`. Conclude with `hT Tm hTm`.

Use `choose d₁ hd₁ using fun yb => hcomb (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1`. Use `choose d₂ hd₂ using fun yb => hcomb (Q.FX (Q.s + 1) le_rfl) Q.FM _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2`. Use `set S := hfin.toFinset with hS`. Establish `hSc : Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S` using `by simp [S]`. Establish `hmemS : ∀ yb, yb ∈ S ↔ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)` using `fun yb => by simp [S]`.

Use `set C := c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂ with hC`. Establish `hpt` using `GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α S hSc d₁ d₂ hd₁ hd₂`. Establish `hlin` using `GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1 φ hφ`. Rewrite using `[hpt, hlin _ S d₁ d₂ (fun i => (hd₁ i).1) (fun i => (hd₂ i).1)]`. Use `set B : Q.Ch (Q.s + 1) → GA D (c.X (Q.s + 1 + 1)) → ℂ := fun y => c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) with hB`.

Establish `hterm : ∀ yb ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ yb]) (aconv [c₂, d₂ yb]) C) = ∑ y, if SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb then B y else 0`. Introduce `yb hyb`. Take `⟨y₀, hy₀⟩` from `Q.cos_cov yb ((hmemS yb).1 hyb)`. Rewrite using `[Finset.sum_eq_single y₀]`. Rewrite using `[if_pos hy₀]`.

Conclude with `GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u y₀ yb hy₀ (d₁ yb) (d₂ yb) (hd₁ yb) (hd₂ yb)`. Introduce `y _ hy`. Rewrite using `[if_neg]`. Introduce `h'`. Conclude with `hy (Q.cos_inj y y₀ (htrans _ _ _ h' (hsymm _ _ hy₀)))`.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]`.

Distinguish the cases in `hy : Q.cos y ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)`. Establish `hset : {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} = ↑(S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb)`. Use extensionality with `yb`. Simplify using `only [Set.mem_setOf_eq, Finset.coe_filter]`. Conclude with `⟨fun h' => ⟨(hmemS yb).2 (hstab _ hy yb h'), h'⟩, fun h' => h'.2⟩`.

Rewrite using `[hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.cast_smul_eq_nsmul]`. Establish `hempty : (S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) = ∅`. Rewrite using `[Finset.filter_eq_empty_iff]`. Introduce `yb hyb h'`. Conclude with `hy (hstab yb ((hmemS yb).1 hyb) _ (hsymm _ _ h'))`.

Establish `hnot : Q.cos y ∉ S` using `fun h' => hy ((hmemS _).1 h')`. Establish `hz : biComb c.ψ _ _ _ (Q.dL Q.s α y) (Q.dL (Q.s + 1) y u) C = 0`. Establish `h2` using `GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α (insert (Q.cos y) S) (hSc.trans (by simp)) (Function.update d₁ (Q.cos y) (Q.dL Q.s α y)) (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u)) (fun yb => by`. Distinguish the cases in `e : yb = Q.cos y`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `Q.dL_pen α y`. Rewrite using `[Function.update_of_ne e]`. Conclude with `hd₁ yb)`. Use the proof step `(fun yb => by`.

Distinguish the cases in `e : yb = Q.cos y`. Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Q.dL_top y u`. Rewrite using `[Function.update_of_ne e]`.

Conclude with `hd₂ yb)`. Rewrite `h2` using `[hpt, Finset.sum_insert hnot, Function.update_self, Function.update_self]`. Establish `h3 : ∑ yb ∈ S, biComb c.ψ _ _ _ (Function.update d₁ (Q.cos y) (Q.dL Q.s α y) yb) (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u) yb) C = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C`. Use `Finset.sum_congr rfl fun yb hyb => ?_` and prove the remaining obligations. Establish `e : yb ≠ Q.cos y` using `fun e => hnot (e ▸ hyb)`.

Rewrite using `[Function.update_of_ne e, Function.update_of_ne e]`. Rewrite `h2` using `[h3]`. Rewrite `h2` using `[← hC]`. Establish `h4` using `congrArg (fun F => F - ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C) h2`. Simplify using `only [sub_self, add_sub_cancel_right] at h4`.

Conclude with `h4.symm`. Establish `hB0 : c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) = 0`. Establish `e1` using `hlin Unit (Finset.univ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u) (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)`. Establish `e2` using `hlin Unit (∅ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u) (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton, Finset.sum_empty] at e1 e2`.

Rewrite `e1` using `[hz]`. Rewrite using `[← e1, e2]`. Rewrite using `[hempty, Finset.card_empty, zero_smul, hB0, smul_zero]`.
-/
theorem lastOne : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂))) = ∑ y, (Nat.card {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} : ℂ) • c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by

  intro D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u
  classical
  obtain ⟨hfin, -, hsymm, htrans, hstab⟩ := GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable D c v χ Q

  have hcomb : ∀ {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
      (FS : GlobalTheory.LocMod.Frame Q.k S.rank Y') (FT : GlobalTheory.LocMod.Frame Q.k T.rank Y) (Ξ : Matrix Y Y' Q.k → ℂ),
      Ξ ∈ SB _ → ∃ d, (ofSplit Q.q).IsCombAt c.ψ FS FT d Ξ := by
    intro S T Y Y' _ _ _ _ FS FT Ξ hΞ
    let O : SB (Matrix Y Y' Q.k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Y Y'⟩
    have hO : O ≠ 0 := by
      intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      simp [O, Set.indicator_apply] at this
    obtain ⟨d, hd, hT⟩ := GlobalTheory.T.exists_heisenberg_combination_split_place_datum D Q.k (ofSplit Q.q) Y Y' S T FS FT c.ψ hc.std O ⟨Ξ, hΞ⟩ hO
    refine ⟨d, hd, fun Tm hTm Φ₀ Φ h0 h1 => ?_⟩
    have e0 : Φ₀ = O := Subtype.ext h0
    have e1 : Φ = ⟨Ξ, hΞ⟩ := Subtype.ext h1
    rw [e0, e1]
    exact hT Tm hTm
  choose d₁ hd₁ using fun yb => hcomb (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1
  choose d₂ hd₂ using fun yb => hcomb (Q.FX (Q.s + 1) le_rfl) Q.FM _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2
  set S := hfin.toFinset with hS
  have hSc : Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S := by simp [S]
  have hmemS : ∀ yb, yb ∈ S ↔ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := fun yb => by simp [S]
  set C := c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂ with hC
  have hpt := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α S hSc d₁ d₂ hd₁ hd₂
  have hlin := GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1 φ hφ
  rw [hpt, hlin _ S d₁ d₂ (fun i => (hd₁ i).1) (fun i => (hd₂ i).1)]

  set B : Q.Ch (Q.s + 1) → GA D (c.X (Q.s + 1 + 1)) → ℂ := fun y =>
    c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) with hB

  have hterm : ∀ yb ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ yb]) (aconv [c₂, d₂ yb]) C) =
      ∑ y, if SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb then B y else 0 := by
    intro yb hyb
    obtain ⟨y₀, hy₀⟩ := Q.cos_cov yb ((hmemS yb).1 hyb)
    rw [Finset.sum_eq_single y₀]
    · rw [if_pos hy₀]
      exact GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u y₀ yb hy₀
        (d₁ yb) (d₂ yb) (hd₁ yb) (hd₂ yb)
    · intro y _ hy
      rw [if_neg]
      intro h'
      exact hy (Q.cos_inj y y₀ (htrans _ _ _ h' (hsymm _ _ hy₀)))
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  by_cases hy : Q.cos y ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)
  · have hset : {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} =
        ↑(S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) := by
      ext yb
      simp only [Set.mem_setOf_eq, Finset.coe_filter]
      exact ⟨fun h' => ⟨(hmemS yb).2 (hstab _ hy yb h'), h'⟩, fun h' => h'.2⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.cast_smul_eq_nsmul]
  · have hempty : (S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro yb hyb h'
      exact hy (hstab yb ((hmemS yb).1 hyb) _ (hsymm _ _ h'))
    have hnot : Q.cos y ∉ S := fun h' => hy ((hmemS _).1 h')

    have hz : biComb c.ψ _ _ _ (Q.dL Q.s α y) (Q.dL (Q.s + 1) y u) C = 0 := by
      have h2 := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α (insert (Q.cos y) S)
        (hSc.trans (by simp)) (Function.update d₁ (Q.cos y) (Q.dL Q.s α y))
        (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u))
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_pen α y
          · rw [Function.update_of_ne e]; exact hd₁ yb)
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_top y u
          · rw [Function.update_of_ne e]; exact hd₂ yb)
      rw [hpt, Finset.sum_insert hnot, Function.update_self, Function.update_self] at h2
      have h3 : ∑ yb ∈ S, biComb c.ψ _ _ _ (Function.update d₁ (Q.cos y) (Q.dL Q.s α y) yb)
          (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u) yb) C =
          ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C := by
        refine Finset.sum_congr rfl fun yb hyb => ?_
        have e : yb ≠ Q.cos y := fun e => hnot (e ▸ hyb)
        rw [Function.update_of_ne e, Function.update_of_ne e]
      rw [h3] at h2
      rw [← hC] at h2
      have h4 := congrArg (fun F => F - ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C) h2
      simp only [sub_self, add_sub_cancel_right] at h4
      exact h4.symm
    have hB0 : c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) = 0 := by
      have e1 := hlin Unit (Finset.univ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      have e2 := hlin Unit (∅ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.sum_empty] at e1 e2
      rw [hz] at e1
      rw [← e1, e2]
    rw [hempty, Finset.card_empty, zero_smul, hB0, smul_zero]

end GlobalTheory.QLastOne
end
