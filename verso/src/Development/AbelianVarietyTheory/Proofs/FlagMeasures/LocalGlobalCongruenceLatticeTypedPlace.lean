import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaLocGlob

open Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : D7}

/- English proof (translation)
Rewrite using `[Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]`.
-/
theorem bcP_osmul (p : PlF D) (a : 𝓞 D.host.E) (y : (VS D).V) :
    baseChange₂ D p (a • y) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]

/- English proof (translation)
Rewrite using `[GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `IotaBP.typed_q_mem Z p g hs F F' hv`.
-/
theorem smulLat_le (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') :
    (locH Z p).smulLat (algebraMap _ _ (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) ≤
      lattice₂ D Z.M p (NgX Λ (gS D) F F') := by
  rw [GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  exact IotaBP.typed_q_mem Z p g hs F F' hv

/- English proof (translation)
Establish `hsat` using `Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp F) hΛ`. Establish `hsp : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp F : Set (VS D).V))`. Use `(Submodule.span_le.2 ?_) hX` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `e : scaled Z p (frame F) a.castSucc = frFac Z.δ p a.castSucc • baseChange₂ D p (F.fl.e a)`.

Simplify using `only [scaled, GlobalTheory.LocExt.frame_castSucc]`. Use `show scaled Z p (frame F) a.castSucc ∈ _`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨F.fl.e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩)`. Establish `h : v ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp F)) : Set (Vp D p))`.

Rewrite using `[hsat]`. Conclude with `⟨hv, hsp⟩`. Conclude with `h`.
-/
theorem mem_latP_XLam (Z : LocDat D) (p : PlF D) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) {T : D.host.E}
    (F : LFlag (VS D) D.R.rS T) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ)
    (hX : v ∈ (locH Z p).X (scaled Z p (frame F))) : v ∈ lattice₂ D Z.M p (XLam Λ F) := by
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp F) hΛ
  have hsp : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp F : Set (VS D).V)) := by
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨a, rfl⟩
    have e : scaled Z p (frame F) a.castSucc = frFac Z.δ p a.castSucc • baseChange₂ D p (F.fl.e a) := by
      simp only [scaled, GlobalTheory.LocExt.frame_castSucc]
    show scaled Z p (frame F) a.castSucc ∈ _
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F.fl.e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩)
  have h : v ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp F)) : Set (Vp D p)) := by
    rw [hsat]; exact ⟨hv, hsp⟩
  exact h

/- English proof (translation)
Introduce `D Z p hsp a ⟨o, ho, hao⟩ hoth Λ hΛ T T' F F' y hy`. Take `⟨g, hs⟩` from `Option.ne_none_iff_exists'.1 hsp`. Establish `hyp : baseChange₂ D p y ∈ lattice₂ D Z.M p Λ` using `BwdNP.baseChange_mem_localLattice Z hy p`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨μ, hμ, ξ, hξ, ξ', hξ', e⟩` from `IotaBP.NgX_dec h`. Take `⟨w, hw, w', -, hgq, -⟩` from `IotaBP.gS_typed Z p g hs`. Establish `h2 : baseChange₂ D p (a • y) = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • baseChange₂ D p μ + baseChange₂ D p ξ + baseChange₂ D p ξ'`. Rewrite using `[e, map_add, map_add, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]`. Establish `key : baseChange₂ D p y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • (baseChange₂ D p μ - o • baseChange₂ D p y)) + baseChange₂ D p ξ + baseChange₂ D p ξ'`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Use `_ = _ := by`. Rewrite using `[hao, ← bcP_osmul, h2, hgq]`.

Simplify using `only [smul_sub, smul_smul, mul_assoc]`. Normalize the expressions using the abelian group laws. Use `⟨_, ?_, baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ) p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ') p, GlobalTheory.LocExt.bcP_Xsp_mem Z p F (Submodule.mem_inf.1 hξ).2, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' (Submodule. …` and prove the remaining obligations. Rewrite using `[GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]`. Use `Submodule.subset_span ⟨w • (baseChange₂ D p μ - o • baseChange₂ D p y), ?_, rfl⟩` and prove the remaining obligations.

Conclude with `Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw (sub_mem (BwdNP.baseChange_mem_localLattice Z hμ p) (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))`. Introduce and unpack `⟨A, hA, B, hB, C, hC, hBX, hCX, he⟩`. Use `BwdNP.mem_of_bcP Z (IotaBP.isLattice_NgX hΛ F F') fun p' => ?_` and prove the remaining obligations. Distinguish the cases in `hp : p' = p`. Rewrite using `[hp, bcP_osmul]`.

Establish `e : (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y = baseChange₂ D p y + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • baseChange₂ D p y)`. Rewrite using `[smul_smul, ← hao, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem ?_ (IotaBP.smul_gS_mem Z p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))` and prove the remaining obligations.

Rewrite using `[he]`. Use `add_mem (add_mem (smulLat_le Z p g hs Λ F F' hA) ?_) ?_` and prove the remaining obligations. Conclude with `IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (mem_latP_XLam Z p hΛ.fg F hB hBX)`. Conclude with `IotaBP.localLattice_mono Z p le_sup_right (mem_latP_XLam Z p hΛ.fg F' hC hCX)`. Take `⟨o', ho', hao'⟩` from `hoth p' hp`.

Establish `e : baseChange₂ D p' (a • y) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • (o' • baseChange₂ D p' y)`. Rewrite using `[bcP_osmul, smul_smul, ← hao']`. Rewrite using `[e]`. Conclude with `IotaBP.smul_gS_mem Z p' F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p' ho' (BwdNP.baseChange_mem_localLattice Z hy p'))`.
-/
theorem locglob : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (Z.M p).split ≠ none → ∀ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - 1 = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → (∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), ∀ y ∈ Λ, (a • y ∈ NgX Λ (gS D) F F' ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p y)) := by
  intro D Z p hsp a ⟨o, ho, hao⟩ hoth Λ hΛ T T' F F' y hy
  obtain ⟨g, hs⟩ := Option.ne_none_iff_exists'.1 hsp
  have hyp : baseChange₂ D p y ∈ lattice₂ D Z.M p Λ := BwdNP.baseChange_mem_localLattice Z hy p
  constructor
  · intro h
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', e⟩ := IotaBP.NgX_dec h
    obtain ⟨w, hw, w', -, hgq, -⟩ := IotaBP.gS_typed Z p g hs
    have h2 : baseChange₂ D p (a • y) = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • baseChange₂ D p μ + baseChange₂ D p ξ + baseChange₂ D p ξ' := by
      rw [e, map_add, map_add, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    have key : baseChange₂ D p y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) •
        (w • (baseChange₂ D p μ - o • baseChange₂ D p y)) + baseChange₂ D p ξ + baseChange₂ D p ξ' := by
      calc baseChange₂ D p y = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y - ((D.s.atP p).ιE (a : D.host.E) - 1) • baseChange₂ D p y := by
            rw [sub_smul, one_smul]; abel
        _ = _ := by
            rw [hao, ← bcP_osmul, h2, hgq]
            simp only [smul_sub, smul_smul, mul_assoc]
            abel
    refine ⟨_, ?_, baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ) p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ') p,
      GlobalTheory.LocExt.bcP_Xsp_mem Z p F (Submodule.mem_inf.1 hξ).2, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' (Submodule.mem_inf.1 hξ').2, key⟩
    rw [GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]
    refine Submodule.subset_span ⟨w • (baseChange₂ D p μ - o • baseChange₂ D p y), ?_, rfl⟩
    exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw
      (sub_mem (BwdNP.baseChange_mem_localLattice Z hμ p) (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))
  · rintro ⟨A, hA, B, hB, C, hC, hBX, hCX, he⟩
    refine BwdNP.mem_of_bcP Z (IotaBP.isLattice_NgX hΛ F F') fun p' => ?_
    by_cases hp : p' = p
    · rw [hp, bcP_osmul]
      have e : (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y =
          baseChange₂ D p y + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • baseChange₂ D p y) := by
        rw [smul_smul, ← hao, sub_smul, one_smul]; abel
      rw [e]
      refine add_mem ?_ (IotaBP.smul_gS_mem Z p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))
      rw [he]
      refine add_mem (add_mem (smulLat_le Z p g hs Λ F F' hA) ?_) ?_
      · exact IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (mem_latP_XLam Z p hΛ.fg F hB hBX)
      · exact IotaBP.localLattice_mono Z p le_sup_right (mem_latP_XLam Z p hΛ.fg F' hC hCX)
    · obtain ⟨o', ho', hao'⟩ := hoth p' hp
      have e : baseChange₂ D p' (a • y) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • (o' • baseChange₂ D p' y) := by
        rw [bcP_osmul, smul_smul, ← hao']
      rw [e]
      exact IotaBP.smul_gS_mem Z p' F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p' ho' (BwdNP.baseChange_mem_localLattice Z hy p'))

end GlobalTheory.IotaLocGlob
