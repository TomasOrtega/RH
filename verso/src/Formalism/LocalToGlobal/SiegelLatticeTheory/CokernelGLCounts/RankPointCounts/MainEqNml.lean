import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormals
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps
  Formalism.L2.SG.NGCut.NormalVectorPairings

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqNml

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def OccTG (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ clsG Y u t = c ∧ ptPN t = γ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, h1, h2, h3, h4, h5⟩`. Establish `e : t ∈ (Y.tO u u).genSet`. Simplify using `only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢`. Conclude with `h1`.

Conclude with `⟨t, ⟨e, h2, h3, h4⟩, h5⟩`. Introduce and unpack `⟨t, ⟨h1, h2, h3, h4⟩, h5⟩`. Establish `e : t ∈ (genT (Y.tO u u)).ngSet`. Simplify using `only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢`. Conclude with `h1`.

Conclude with `⟨t, e, h2, h3, h4, h5⟩`.
-/
theorem occ_iffG (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν ↔ ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    have e : t ∈ (Y.tO u u).genSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, ⟨e, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    have e : t ∈ (genT (Y.tO u u)).ngSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, e, h2, h3, h4, h5⟩

variable {Y u}

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.MainEqSteps.ScalEquivOn at hE`. Take `⟨h01, h02, h03, h04⟩` from `h0`. Take `⟨h1, h2, h3, h4⟩` from `h`. Establish `hmem : t ∈ clsG Y u t` using `⟨h1, rfl, (hE.1 t h1).1, (hE.1 t h1).2⟩`. Rewrite `hmem` using `[h3, ← h03]`.

Conclude with `⟨hmem.2.1, hmem.2.2.1⟩`.
-/
theorem relC_of_occG (hE : ScalEquivOn (Y.tO u u)) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : OccTG Y u c γ t0) (h : OccTG Y u c γ t) : RelC Y u u t0 t := by
  unfold Formalism.L2.SG.Pf.MainEqSteps.ScalEquivOn at hE
  obtain ⟨h01, h02, h03, h04⟩ := h0
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hmem : t ∈ clsG Y u t := ⟨h1, rfl, (hE.1 t h1).1, (hE.1 t h1).2⟩
  rw [h3, ← h03] at hmem
  exact ⟨hmem.2.1, hmem.2.2.1⟩

end Formalism.L2.SG.Pf.MainEqNml

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqNml

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Take `⟨a1, b1, H1⟩` from `hL Cg cb Cw cT CT C0`. Take `⟨a2, b2, H2⟩` from `hI Cg cb Cw cT CT C0`. Take `⟨a3, b3, H3⟩` from `hS Cg cb Cw cT CT C0`. Use `⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩` and prove the remaining obligations.

Establish `hC1 : a1 ≤ C'` using `le_trans (le_max_left _ _) hC`. Establish `hC2 : a2 ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC`. Establish `hC3 : a3 ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC`. Establish `hl1 : b1 ≤ Cl` using `le_trans (le_max_left _ _) hCl`. Establish `hl2 : b2 ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl`.

Establish `hl3 : b3 ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl`. Take `⟨ν0, hν0⟩` from `hocc`. Take `⟨t0, ht0, -⟩` from `(occ_iffG Y u νL νB ng c γ ν0).1 hν0`. Establish `hE : ScalEquivOn (Y.tO u u)` using `stepClassG_holds D X Y u (g_ge_three hctx) hctx.2.2`. Establish `hG0 : Gt t0 ≠ 0` using `ht0.1.1`.

Take `⟨J, J', hJ, hJ', hmem, hb, hb'⟩` from `H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2`. Use `set pick : NuC D → TauC Y u u := fun ν => if h : ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick`. Establish `hpick_spec : ∀ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν → OccTG Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν`. Introduce `ν hν`. Establish `h` using `(occ_iffG Y u νL νB ng c γ ν).1 hν`.

Simplify using `only [hpick, dif_pos h]`. Conclude with `h.choose_spec`. Use `⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero, one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨hp, -⟩` from `hpick_spec ν hν`. Take `⟨m1, m2⟩` from `hmem _ hp.1.1 hp.2.2.2 (relC_of_occG hE ht0 hp)`.

Take `⟨n1, n2⟩` from `H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2 (relC_of_occG hE ht0 hp)`. Conclude with `⟨m1, n1, m2, n2⟩`. Take `⟨hp1, he1⟩` from `hpick_spec ν₁ h₁`. Take `⟨hp2, he2⟩` from `hpick_spec ν₂ h₂`. Establish `hk1` using `congrArg Prod.fst hκ`.

Establish `hk2` using `congrArg Prod.snd hκ`. Simplify using `only at hk1 hk2`. Rewrite using `[← he1, ← he2]`. Conclude with `H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2 (relC_of_occG hE ht0 hp1) (relC_of_occG hE ht0 hp2) hk1 hk2`. Rewrite using `[map_one]`.

Simplify using `using hb`. Rewrite using `[map_one]`. Simplify using `using hb'`.
-/
theorem nmlInvG_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iffG Y u νL νB ng c γ ν0).1 hν0
  have hE : ScalEquivOn (Y.tO u u) := stepClassG_holds D X Y u (g_ge_three hctx) hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν →
      OccTG Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occ_iffG Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occG hE ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occG hE ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occG hE ht0 hp1) (relC_of_occG hE ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.Pf
