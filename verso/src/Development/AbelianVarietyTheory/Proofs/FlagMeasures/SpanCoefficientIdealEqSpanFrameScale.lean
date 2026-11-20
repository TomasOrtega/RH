import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFlagScaledFrameEqBaseChangeFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledLocalDualCoeffEqGlobalCoeffStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStepLocallyStandardDualCoeffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagStepLocallyStandardDualCoeffOneStatement

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero`. Establish `h0 : H.h 0 e = 0` using `by simpa using H.h_smul_left 0 0 e`.

Rewrite using `[h0, mul_zero]`. Conclude with `N.zero_mem`. Consider the case `add x y _ _ hx hy`. Rewrite using `[H.h_add_left, mul_add]`. Conclude with `N.add_mem hx hy`.

Consider the case `smul r x _ hx`. Establish `hmem` using `N.smul_mem r hx`. Rewrite `hmem` using `[Subring.smul_def, smul_eq_mul]`. Rewrite using `[Subring.smul_def, H.h_smul_left, mul_left_comm]`. Conclude with `hmem`.
-/
theorem span_coef_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] (H : Loc.HermSp M V) (c : E) (e : V) (S : Set V) (N : Submodule M.L.O E)
    (hS : ∀ w ∈ S, c * H.h w e ∈ N) : ∀ w ∈ Submodule.span M.L.O S, c * H.h w e ∈ N := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h0 : H.h 0 e = 0 := by simpa using H.h_smul_left 0 0 e
    rw [h0, mul_zero]
    exact N.zero_mem
  | add x y _ _ hx hy =>
    rw [H.h_add_left, mul_add]
    exact N.add_mem hx hy
  | smul r x _ hx =>
    have hmem := N.smul_mem r hx
    rw [Subring.smul_def, smul_eq_mul] at hmem
    rw [Subring.smul_def, H.h_smul_left, mul_left_comm]
    exact hmem

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T G Z A hA Λ hL hloc p a`. Take `⟨n, hn, L, -, hΛ⟩` from `hloc p`. Establish `hFj : (A p).Fj (a.val + 1) = Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa (a.val + 1) : Set (VS D).V))` using `(GlobalTheory.T.local_flag_scaled_frame_eq_baseChange_flag D T G Z A hA p (a.val + 1)).symm`. Establish `hXle : G.fl.Xa (a.val + 1) ≤ G.fl.X` using `Submodule.span_mono (Set.image_subset_range _ _)`. Establish `hint : ∀ y : D.host.E, IsIntegral ℤ y → (D.s.atP p).ιE y ∈ (Z.M p).L.O`.

Introduce `y hy`. Rewrite using `[Formalism.L2.SG.Pf.LocFacts.lf_hO Z p, (D.s.atP p).O_def]`. Conclude with `(hy.map (D.s.atP p).ιE.toIntAlgHom).tower_top`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨x, hxΛ, hxX, rfl⟩` from `ht`. Establish `hv1 : baseChange₂ D p x ∈ (A p).Fj (a.val + 1)`.

Rewrite using `[hFj]`. Conclude with `Submodule.subset_span ⟨x, hxX, rfl⟩`. Establish `hv2 : baseChange₂ D p x ∈ LocNG.img n ((A p).LamStd L)`. Rewrite using `[← hΛ]`. Conclude with `Submodule.subset_span ⟨x, hxΛ, rfl⟩`.

Establish `hO` using `GlobalTheory.T.flagStep_locallyStandard_dualCoeff_integral (A p) n hn L a (baseChange₂ D p x) hv1 hv2`. Rewrite using `[← GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff D T G Z A hA p a x (hXle hxX)]`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`. Conclude with `⟨⟨_, hO⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩`. Consider the case `zero`.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul r x _ hx`. Establish `hrO : (D.s.atP p).ιE (algebraMap (𝓞 D.host.E) D.host.E r) ∈ (Z.M p).L.O` using `hint _ (NumberField.RingOfIntegers.isIntegral r).algebraMap`. Establish `hmem` using `Submodule.smul_mem _ (⟨_, hrO⟩ : (Z.M p).L.O) hx`. Rewrite `hmem` using `[Subring.smul_def, smul_eq_mul]`. Rewrite using `[Algebra.smul_def, map_mul]`.

Conclude with `hmem`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Take `⟨v, hvΛ, hvF, hv1⟩` from `GlobalTheory.T.exists_flagStep_locallyStandard_dualCoeff_one (A p) n hn L a`. Rewrite `hvΛ` using `[← hΛ]`. Rewrite `hvF` using `[hFj]`.

Use `set Xr : Submodule D.host.E (VS D).V := G.fl.Xa (a.val + 1) with hXr`. Use `set W : Submodule D.host.E (Fin (nV D) → D.host.E) := Xr.map ((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)) with hW`. Establish `hsat : v ∈ lattice₂ D Z.M p (Λ ⊓ Xr.restrictScalars (𝓞 D.host.E))`. Establish `hFG : (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)).FG` using `hL.fg.map _`. Establish `key : (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D) ⊓ W.restrictScalars (𝓞 D.host.E)) : Set (Vp D p)) = (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) ∩ Submodule.span (D.s.atP p).Ep (PI.LocLatEq.bc (D.s.atP p) …` using `inf_eq_inter_span _ _ _ _ (D.s.atP p) _ _ _ hFG`.

Establish `himg : baseChange₂ D p '' (Xr : Set (VS D).V) = PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E))`. Rewrite using `[hW, Submodule.map_coe, Set.image_image]`. Apply `Set.image_congr` to reduce the goal to its premises. Introduce `x _`. Rewrite using `[Formalism.L2.SG.Pf.LocFacts.localBaseChange_eq]`.

Both sides reduce to the same expression. Establish `hvΛ' : v ∈ (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p))`. Rewrite using `[← Formalism.L2.SG.Pf.LocFacts.localLattice_coe Z p Λ]`. Conclude with `hvΛ`. Establish `hvF' : v ∈ Submodule.span (D.s.atP p).Ep (PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E)))`.

Rewrite using `[← himg]`. Conclude with `hvF`. Establish `hmap : (Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)).map (Formalism.L2.SG.Pf.LocFacts.phi D) = Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D) ⊓ W.restrictScalars (𝓞 D.host.E)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, ⟨hxΛ, hxX⟩, rfl⟩`. Conclude with `⟨⟨x, hxΛ, rfl⟩, ⟨x, hxX, rfl⟩⟩`. Introduce and unpack `⟨⟨x, hxΛ, rfl⟩, ⟨x', hx'X, hx'⟩⟩`. Establish `hxx : x' = x` using `(VS D).frame.equivFun.injective hx'`. Substitute `hxx` using the available equality.

Conclude with `⟨x', ⟨hxΛ, hx'X⟩, rfl⟩`. Establish `h3 : v ∈ (PI.LocLatEq.latL (D.s.atP p) ((Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)).map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p))`. Rewrite using `[hmap, key]`. Conclude with `⟨hvΛ', hvF'⟩`. Rewrite `h3` using `[← Formalism.L2.SG.Pf.LocFacts.localLattice_coe Z p]`.

Conclude with `h3`. Establish `key` using `span_coef_mem (locH Z p) (frFac Z.δ p a.castSucc) ((A p).es a) (baseChange₂ D p '' ((Λ ⊓ Xr.restrictScalars (𝓞 D.host.E) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V)) (Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (GlobalTheory.RowLatXS.Ia Λ G.fl a : Set D.host.E))) ?_ v hs …`. Rewrite `key` using `[hv1, mul_one]`. Conclude with `key`. Introduce and unpack `_ ⟨x, ⟨hxΛ, hxX⟩, rfl⟩`.

Rewrite using `[GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff D T G Z A hA p a x (hXle hxX)]`. Conclude with `Submodule.subset_span ⟨_, Submodule.subset_span ⟨x, hxΛ, hxX, rfl⟩, rfl⟩`.
-/
theorem span_coefIdeal_eq_span_frFac : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ (p : PlF D) (a : Fin D.R.rS), Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (GlobalTheory.RowLatXS.Ia Λ G.fl a : Set D.host.E)) = Submodule.span (Z.M p).L.O {frFac Z.δ p a.castSucc} := by
  intro D T G Z A hA Λ hL hloc p a
  obtain ⟨n, hn, L, -, hΛ⟩ := hloc p

  have hFj : (A p).Fj (a.val + 1) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa (a.val + 1) : Set (VS D).V)) :=
    (GlobalTheory.T.local_flag_scaled_frame_eq_baseChange_flag D T G Z A hA p (a.val + 1)).symm
  have hXle : G.fl.Xa (a.val + 1) ≤ G.fl.X := Submodule.span_mono (Set.image_subset_range _ _)

  have hint : ∀ y : D.host.E, IsIntegral ℤ y → (D.s.atP p).ιE y ∈ (Z.M p).L.O := by
    intro y hy
    rw [Formalism.L2.SG.Pf.LocFacts.lf_hO Z p, (D.s.atP p).O_def]
    exact (hy.map (D.s.atP p).ιE.toIntAlgHom).tower_top
  apply le_antisymm
  ·
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hxΛ, hxX, rfl⟩ := ht
      have hv1 : baseChange₂ D p x ∈ (A p).Fj (a.val + 1) := by
        rw [hFj]; exact Submodule.subset_span ⟨x, hxX, rfl⟩
      have hv2 : baseChange₂ D p x ∈ LocNG.img n ((A p).LamStd L) := by
        rw [← hΛ]; exact Submodule.subset_span ⟨x, hxΛ, rfl⟩
      have hO := GlobalTheory.T.flagStep_locallyStandard_dualCoeff_integral (A p) n hn L a (baseChange₂ D p x) hv1 hv2
      rw [← GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff D T G Z A hA p a x (hXle hxX)]
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨⟨_, hO⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
    | zero =>
      rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hrO : (D.s.atP p).ιE (algebraMap (𝓞 D.host.E) D.host.E r) ∈ (Z.M p).L.O :=
        hint _ (NumberField.RingOfIntegers.isIntegral r).algebraMap
      have hmem := Submodule.smul_mem _ (⟨_, hrO⟩ : (Z.M p).L.O) hx
      rw [Subring.smul_def, smul_eq_mul] at hmem
      rw [Algebra.smul_def, map_mul]
      exact hmem
  ·
    rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨v, hvΛ, hvF, hv1⟩ := GlobalTheory.T.exists_flagStep_locallyStandard_dualCoeff_one (A p) n hn L a
    rw [← hΛ] at hvΛ
    rw [hFj] at hvF
    set Xr : Submodule D.host.E (VS D).V := G.fl.Xa (a.val + 1) with hXr
    set W : Submodule D.host.E (Fin (nV D) → D.host.E) :=
      Xr.map ((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)) with hW

    have hsat : v ∈ lattice₂ D Z.M p (Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)) := by
      have hFG : (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)).FG := hL.fg.map _
      have key : (PI.LocLatEq.latL (D.s.atP p)
            (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D) ⊓ W.restrictScalars (𝓞 D.host.E)) : Set (Vp D p)) =
          (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) ∩
            Submodule.span (D.s.atP p).Ep (PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E))) :=
        inf_eq_inter_span _ _ _ _ (D.s.atP p) _ _ _ hFG
      have himg : baseChange₂ D p '' (Xr : Set (VS D).V) =
          PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E)) := by
        rw [hW, Submodule.map_coe, Set.image_image]
        apply Set.image_congr
        intro x _
        rw [Formalism.L2.SG.Pf.LocFacts.localBaseChange_eq]
        rfl
      have hvΛ' : v ∈ (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) := by
        rw [← Formalism.L2.SG.Pf.LocFacts.localLattice_coe Z p Λ]; exact hvΛ
      have hvF' : v ∈ Submodule.span (D.s.atP p).Ep
          (PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E))) := by
        rw [← himg]; exact hvF
      have hmap : (Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)).map (Formalism.L2.SG.Pf.LocFacts.phi D) =
          Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D) ⊓ W.restrictScalars (𝓞 D.host.E) := by
        ext y
        constructor
        · rintro ⟨x, ⟨hxΛ, hxX⟩, rfl⟩
          exact ⟨⟨x, hxΛ, rfl⟩, ⟨x, hxX, rfl⟩⟩
        · rintro ⟨⟨x, hxΛ, rfl⟩, ⟨x', hx'X, hx'⟩⟩
          have hxx : x' = x := (VS D).frame.equivFun.injective hx'
          subst hxx
          exact ⟨x', ⟨hxΛ, hx'X⟩, rfl⟩
      have h3 : v ∈ (PI.LocLatEq.latL (D.s.atP p)
          ((Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)).map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) := by
        rw [hmap, key]; exact ⟨hvΛ', hvF'⟩
      rw [← Formalism.L2.SG.Pf.LocFacts.localLattice_coe Z p] at h3
      exact h3
    have key := span_coef_mem (locH Z p) (frFac Z.δ p a.castSucc) ((A p).es a)
      (baseChange₂ D p '' ((Λ ⊓ Xr.restrictScalars (𝓞 D.host.E) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V))
      (Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (GlobalTheory.RowLatXS.Ia Λ G.fl a : Set D.host.E))) ?_ v hsat
    · rw [hv1, mul_one] at key
      exact key
    · rintro _ ⟨x, ⟨hxΛ, hxX⟩, rfl⟩
      rw [GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff D T G Z A hA p a x (hXle hxX)]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨x, hxΛ, hxX, rfl⟩, rfl⟩

end GlobalTheory.RowLatXS
