import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One.NormalsProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def IsGenericCorankOneTerm (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ cls1 Y u t = c ∧ ptPN t = γ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, h1, h2, h3, h4, h5⟩`. Rewrite `h1` using `[genT_ngSet]`. Conclude with `⟨t, ⟨h1, h2, h3, h4⟩, h5⟩`. Introduce and unpack `⟨t, ⟨h1, h2, h3, h4⟩, h5⟩`.

Use `⟨t, ?_, h2, h3, h4, h5⟩` and prove the remaining obligations. Rewrite using `[genT_ngSet]`. Conclude with `h1`.
-/
theorem occurs_iff_generic_corank_one (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν ↔ ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    rw [genT_ngSet] at h1
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨t, ?_, h2, h3, h4, h5⟩
    rw [genT_ngSet]
    exact h1

variable {Y u}

/- English proof (translation)
Establish `hrefl : (Y.tO u u).s0 t t = 1` using `(hE D X Y u u hT).1 t h.1.1`. Establish `ht : t ∈ cls1 Y u t` using `⟨h.1, rfl, hrefl⟩`. Rewrite `ht` using `[h.2.2.1, ← h0.2.2.1]`. Conclude with `⟨ht.2.1, ht.2.2⟩`.
-/
theorem related_of_generic_corank_one (hE : CorankOneIsEquivalenceOnRow) (hT : ConcTie X Y) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : IsGenericCorankOneTerm Y u c γ t0) (h : IsGenericCorankOneTerm Y u c γ t) : RelC Y u u t0 t := by
  have hrefl : (Y.tO u u).s0 t t = 1 := (hE D X Y u u hT).1 t h.1.1
  have ht : t ∈ cls1 Y u t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨clsG Y u t, nmlOf Y u u t, (occ_iffG Y u νL νB ng _ γ _).2 ⟨t, ⟨h.1, h.2.1, rfl, h.2.2.2⟩, rfl⟩⟩`.
-/
theorem isPoint_of_generic_corank_one {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ}
    {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS} {t : TauC Y u u} (h : IsGenericCorankOneTerm Y u c γ t) :
    PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ :=
  ⟨clsG Y u t, nmlOf Y u u t, (occ_iffG Y u νL νB ng _ γ _).2 ⟨t, ⟨h.1, h.2.1, rfl, h.2.2.2⟩, rfl⟩⟩

end GlobalTheory.Core.One.NormalsProof

namespace GlobalTheory.Core.One.NormalsProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml Formalism.L2.SG.NGCut.NormalInvariants

def NmlInvOne : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν₁ →
            PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Take `⟨a1, b1, H1⟩` from `hL Cg cb Cw cT CT C0`. Take `⟨a2, b2, H2⟩` from `hI Cg cb Cw cT CT C0`. Take `⟨a3, b3, H3⟩` from `hS Cg cb Cw cT CT C0`. Use `⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩` and prove the remaining obligations.

Establish `hC1 : a1 ≤ C'` using `le_trans (le_max_left _ _) hC`. Establish `hC2 : a2 ≤ C'` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC`. Establish `hC3 : a3 ≤ C'` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC`. Establish `hl1 : b1 ≤ Cl` using `le_trans (le_max_left _ _) hCl`. Establish `hl2 : b2 ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl`.

Establish `hl3 : b3 ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl`. Establish `hT : ConcTie X Y` using `hctx.2.2`. Take `⟨ν0, hν0⟩` from `hocc`. Take `⟨t0, ht0, -⟩` from `(occurs_iff_generic_corank_one Y u νL νB ng c γ ν0).1 hν0`. Establish `hG0 : Gt t0 ≠ 0` using `ht0.1.1`.

Take `⟨J, J', hJ, hJ', hmem, hb, hb'⟩` from `H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2`. Use `set pick : NuC D → TauC Y u u := fun ν => if h : ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick`. Establish `hpick_spec : ∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν → IsGenericCorankOneTerm Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν`. Introduce `ν hν`. Establish `h` using `(occurs_iff_generic_corank_one Y u νL νB ng c γ ν).1 hν`.

Simplify using `only [hpick, dif_pos h]`. Conclude with `h.choose_spec`. Use `⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero, one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨hp, -⟩` from `hpick_spec ν hν`. Take `⟨m1, m2⟩` from `hmem _ hp.1.1 hp.2.2.2 (related_of_generic_corank_one hE hT ht0 hp)`.

Take `⟨n1, n2⟩` from `H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2 (related_of_generic_corank_one hE hT ht0 hp)`. Conclude with `⟨m1, n1, m2, n2⟩`. Take `⟨hp1, he1⟩` from `hpick_spec ν₁ h₁`. Take `⟨hp2, he2⟩` from `hpick_spec ν₂ h₂`. Establish `hk1` using `congrArg Prod.fst hκ`.

Establish `hk2` using `congrArg Prod.snd hκ`. Simplify using `only at hk1 hk2`. Rewrite using `[← he1, ← he2]`. Conclude with `H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2 (related_of_generic_corank_one hE hT ht0 hp1) (related_of_generic_corank_one hE hT ht0 hp2) hk1 hk2`. Rewrite using `[map_one]`.

Simplify using `using hb`. Rewrite using `[map_one]`. Simplify using `using hb'`.
-/
theorem nmlInvOne_of (hE : CorankOneIsEquivalenceOnRow) (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NmlInvOne := by
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
  have hT : ConcTie X Y := hctx.2.2
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occurs_iff_generic_corank_one Y u νL νB ng c γ ν0).1 hν0
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν →
      IsGenericCorankOneTerm Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occurs_iff_generic_corank_one Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (related_of_generic_corank_one hE hT ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (related_of_generic_corank_one hE hT ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (related_of_generic_corank_one hE hT ht0 hp1) (related_of_generic_corank_one hE hT ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end GlobalTheory.Core.One.NormalsProof

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml Formalism.L2.SG.NGCut.NormalInvariants GlobalTheory.Core.One.NormalsProof

/- English proof (translation)
Introduce `hE hL hI hS hB hO`. Establish `hA` using `nmlInvOne_of hE hL hI hS`. Introduce `Cg cb Cw cT CT C0`. Take `⟨a₀, b₀, hA2⟩` from `hA Cg cb Cw cT CT C0`. Take `⟨o₀, p₀, hO2⟩` from `hO Cg cb Cw cT CT C0`.

Use `⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng => ?_⟩` and prove the remaining obligations. Introduce `cl γ S hS`. Establish `hrd` using `rd_one_le D`. Establish `hv : 2 * D.host.v = D.host.rdE` using `by unfold Host.v; ring`. Establish `hstand` using `hc.2.1`.

Use `show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) * (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) * NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6`. Establish `eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) * (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) * ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ) ^ 6 = (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG …`. Establish `hR` using `rd_cancel D`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [hR, one_mul]`. Rewrite using `[hv, ngPt_eq, eR]`. Establish `hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ)` using `by exact_mod_cast hstand.2.2.2.1`. Establish `hT2 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ)` using `by exact_mod_cast hstand.2.2.2.2.1`. Break down `S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩` into its components or cases.

Rewrite using `[hSe]`. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Use `mul_nonneg (pow_nonneg (by nlinarith) _) ?_` and prove the remaining obligations. Rewrite using `[show PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 3) ^ 2 by ring]`. Conclude with `sq_nonneg _`.

Establish `hocc : ∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) cl γ ν` using `⟨ν0, hS ν0 hν0⟩`. Take `⟨t0, ht0, -⟩` from `(occurs_iff_generic_corank_one Y u νL νB ng cl γ ν0).1 (hS ν0 hν0)`. Establish `hIsPt : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ` using `isPoint_of_generic_corank_one ht0`. Establish `hNG0` using `(hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u hc νL νB ng γ hIsPt).1`. Take `⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩` from `hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u hc νL νB ng cl γ hocc hNG0`.

Establish `hNG` using `hNG0`. Rewrite `hNG` using `[ngPt_eq]`. Establish `hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ`. Establish `hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f` using `one_le_pow₀ (one_le_pow₀ hrd)`. Establish `hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f` using `lt_of_lt_of_le one_pos hX`.

Rewrite `hNG` using `[inv_mul_eq_div, le_div_iff₀ hpos, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `T1` to `S.image (fun ν => (κ ν).1)`. Set `T2` to `S.image (fun ν => (κ ν).2)`. Establish `hcard : S.card ≤ T1.card * T2.card`.

Combine the equalities or inequalities in the displayed calculation. Introduce `p hp`. Take `⟨ν, hν, rfl⟩` from `Finset.mem_image.1 hp`. Conclude with `Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)`. Use `_ = T1.card * T2.card := Finset.card_product _ _`.

Establish `hB1` using `hB D J m hJ hm T1 (by`. Introduce `x hx`. Take `⟨ν, hν, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)`. Establish `hB2` using `hB D J' m' hJ' hm' T2 (by`.

Introduce `x hx`. Take `⟨ν, hν, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)`. Establish `hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ)`. Establish `h0 : FractionalIdeal.absNorm J ≠ 0` using `by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]`.

Use `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ)`. Establish `h0 : FractionalIdeal.absNorm J' ≠ 0` using `by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]`. Use `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Generalize the expression as in `PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ = P at hN hN' hP1 ⊢`. Generalize the expression as in `((Tu D u : ℕ) : ℝ) = T at hN hN' hT1 hT2 ⊢`. Generalize the expression as in `((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp`. Generalize the expression as in `((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'`.

Generalize the expression as in `|((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN`. Generalize the expression as in `|((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'`. Establish `hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)`. Establish `h` using `hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))`. Establish `h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h' (by positivity)`. Establish `hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)`. Establish `h` using `hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))`. Establish `h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h' (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem stepNormals1_of : CorankOneIsEquivalenceOnRow → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt →
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep → Formalism.L2.SG.NGCut.NormalInvariants.NormCount → StepNormOneG → StepNormals1 := by
  intro hE hL hI hS hB hO
  have hA := nmlInvOne_of hE hL hI hS
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  obtain ⟨t0, ht0, -⟩ := (occurs_iff_generic_corank_one Y u νL νB ng cl γ ν0).1 (hS ν0 hν0)
  have hIsPt : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ := isPoint_of_generic_corank_one ht0
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith
  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hN' hT1 hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.Core.One
