import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.IsotropicLift

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def kerR (H : HermSp M V) (w : V) : Submodule E V where
  carrier := {v | H.h v w = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_add_left, ha, hb, add_zero]
  zero_mem' := H.h_zero_left w
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_smul_left, hv, mul_zero]

/- English proof (translation)
Rewrite using `[H.h_herm, h]`. Simplify using the standard rewrite rules.
-/
theorem h_swap_zero (H : HermSp M V) {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h]; simp

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Introduce `x hx`. Establish `hk : H.X Fr.f ≤ kerR H (Fr.f b.castSucc)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Fr.h_iso a.castSucc b.castSucc (Or.inl (Fin.castSucc_ne_last a))`. Conclude with `h_swap_zero H (hk hx)`.
-/
theorem X_le_perp (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  intro x hx
  have hk : H.X Fr.f ≤ kerR H (Fr.f b.castSucc) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Fr.h_iso a.castSucc b.castSucc (Or.inl (Fin.castSucc_ne_last a))
  exact h_swap_zero H (hk hx)

/- English proof (translation)
Establish `hXP` using `X_le_perp H Fr`. It suffices to establish `key : ∀ g ∈ Fr.N, ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f ∧ g.symm v - v ∈ H.X Fr.f from (key n hn v hv).1`. Introduce `g hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg`.

Take `⟨hu, -, hperp⟩` from `hg`. Introduce `v hv`. Use `⟨hperp v hv, ?_⟩` and prove the remaining obligations. Establish `hw : g.symm v ∈ H.perp (H.X Fr.f)`. Introduce `x hx`.

Establish `hgx : g x ∈ H.X Fr.f`. Use `hperp x (hXP hx)` as an intermediate fact. Establish `e : g x = (g x - x) + x` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ this hx`.

Rewrite using `[← hu (g.symm v) x, LinearEquiv.apply_symm_apply]`. Conclude with `hv _ hgx`. Establish `h1` using `hperp _ hw`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Establish `e : g.symm v - v = -(v - g.symm v)` using `by abel`.

Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ h1`. Consider the case `one`. Introduce `v _`. Conclude with `⟨by simp, by show v - v ∈ _; simp⟩`.

Consider the case `mul g₁ g₂ _ _ ih₁ ih₂`. Introduce `v hv`. Establish `hm : ∀ x, (g₁ * g₂) x = g₁ (g₂ x)` using `fun _ => rfl`. Establish `hms : ∀ x, (g₁ * g₂).symm x = g₂.symm (g₁.symm x)` using `fun _ => rfl`. Take `⟨a2, b2⟩` from `ih₂ v hv`.

Take `⟨a1, b1⟩` from `ih₁ v hv`. Establish `hv2 : g₂ v ∈ H.perp (H.X Fr.f)`. Establish `e : g₂ v = (g₂ v - v) + v` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hXP a2) hv`.

Establish `hv1 : g₁.symm v ∈ H.perp (H.X Fr.f)`. Establish `e : g₁.symm v = (g₁.symm v - v) + v` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hXP b1) hv`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hm]`. Establish `e : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v)` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (ih₁ _ hv2).1 a2`. Rewrite using `[hms]`.

Establish `e : g₂.symm (g₁.symm v) - v = (g₂.symm (g₁.symm v) - g₁.symm v) + (g₁.symm v - v)` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (ih₂ _ hv1).2 b1`. Consider the case `inv g _ ih`. Introduce `v hv`.

Conclude with `⟨(ih v hv).2, (ih v hv).1⟩`.
-/
theorem sub_mem_X_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : n v - v ∈ H.X Fr.f := by
  have hXP := X_le_perp H Fr
  suffices key : ∀ g ∈ Fr.N, ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f ∧ g.symm v - v ∈ H.X Fr.f from
    (key n hn v hv).1
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hu, -, hperp⟩ := hg
    intro v hv
    refine ⟨hperp v hv, ?_⟩
    have hw : g.symm v ∈ H.perp (H.X Fr.f) := by
      intro x hx
      have hgx : g x ∈ H.X Fr.f := by
        have := hperp x (hXP hx)
        have e : g x = (g x - x) + x := by abel
        rw [e]; exact Submodule.add_mem _ this hx
      rw [← hu (g.symm v) x, LinearEquiv.apply_symm_apply]
      exact hv _ hgx
    have h1 := hperp _ hw
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : g.symm v - v = -(v - g.symm v) := by abel
    rw [e]; exact Submodule.neg_mem _ h1
  | one =>
    intro v _
    exact ⟨by simp, by show v - v ∈ _; simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    intro v hv
    have hm : ∀ x, (g₁ * g₂) x = g₁ (g₂ x) := fun _ => rfl
    have hms : ∀ x, (g₁ * g₂).symm x = g₂.symm (g₁.symm x) := fun _ => rfl
    obtain ⟨a2, b2⟩ := ih₂ v hv
    obtain ⟨a1, b1⟩ := ih₁ v hv
    have hv2 : g₂ v ∈ H.perp (H.X Fr.f) := by
      have e : g₂ v = (g₂ v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP a2) hv
    have hv1 : g₁.symm v ∈ H.perp (H.X Fr.f) := by
      have e : g₁.symm v = (g₁.symm v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP b1) hv
    refine ⟨?_, ?_⟩
    · rw [hm]
      have e : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₁ _ hv2).1 a2
    · rw [hms]
      have e : g₂.symm (g₁.symm v) - v = (g₂.symm (g₁.symm v) - g₁.symm v) + (g₁.symm v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₂ _ hv1).2 b1
  | inv g _ ih =>
    intro v hv
    exact ⟨(ih v hv).2, (ih v hv).1⟩

/- English proof (translation)
Take `⟨-, -, xz, hxz, hxzL, -⟩` from `hL`. Establish `hs : ∀ a, H.h Fr.z (Fr.es a) = 0` using `fun a => h_swap_zero H (Fr.h_sz a)`. Establish `he : ∀ a, H.h Fr.z (Fr.e a) = 0` using `fun a => Fr.h_iso (Fin.last r) a.castSucc (Or.inr (Fin.castSucc_ne_last a))`. Use `Submodule.subset_span ⟨fun a => ?_, fun a => ?_, xz, ?_, hxzL⟩` and prove the remaining obligations. Rewrite using `[hs a]`.

Conclude with `zero_mem _`. Rewrite using `[he a]`. Conclude with `zero_mem _`. Rewrite using `[hxz]`. Simplify using `[FrameD.prF, hs, he]`.
-/
theorem z_mem_LamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)}
    (hL : Fr.IsInner L) : Fr.z ∈ Fr.LamStd L := by
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  have hs : ∀ a, H.h Fr.z (Fr.es a) = 0 := fun a => h_swap_zero H (Fr.h_sz a)
  have he : ∀ a, H.h Fr.z (Fr.e a) = 0 := fun a =>
    Fr.h_iso (Fin.last r) a.castSucc (Or.inr (Fin.castSucc_ne_last a))
  refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, xz, ?_, hxzL⟩
  · rw [hs a]; exact zero_mem _
  · rw [he a]; exact zero_mem _
  · rw [hxz]
    simp [FrameD.prF, hs, he]

end Gen

variable {D : D7}

/- English proof (translation)
Introduce `D T G Z A hA Λ hΛ hloc`. Choose the witnesses or unpack the hypotheses as in `⟨π, hπX, hπmem⟩ : ∃ π : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ G.fl.X, π x = x) ∧ ∀ x, π x ∈ G.fl.X := by`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective G.fl.X.subtype (Submodule.ker_subtype _)`. Use `⟨G.fl.X.subtype ∘ₗ g, fun x hx => ?_, fun x => (g x).2⟩` and prove the remaining obligations. Use `congrArg (fun f => ((f ⟨x, hx⟩ : G.fl.X) : (VS D).V)) hg` as an intermediate fact.

Conclude with `this`. Take `⟨Λ₁, hΛ₁⟩ : ∃ N : LV D, N = Λ ⊔ Submodule.span (𝓞 D.host.E) {G.fl.z}` from `⟨_, rfl⟩`. Take `⟨Λ₂, hΛ₂⟩ : ∃ N : LV D, N = Λ ⊔ Λ₁.map (π.restrictScalars (𝓞 D.host.E))` from `⟨_, rfl⟩`. Establish `hfg : Λ₂.FG`. Rewrite using `[hΛ₂, hΛ₁]`.

Conclude with `hΛ.fg.sup ((hΛ.fg.sup (Submodule.fg_span_singleton _)).map _)`. Establish `hz : G.fl.z ∈ Λ₂`. Use `GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z hfg fun p => ?_` and prove the remaining obligations. Take `⟨n, hn, L, hL, hlat⟩` from `hloc p`. Establish `hzp : (A p).z = baseChange₂ D p G.fl.z` using `by show (A p).f (Fin.last _) = _`.

Rewrite using `[hA p]`. Simplify using `[frFac, frame, FlagG.fvec]`. Establish `hperp : (A p).z ∈ (locH Z p).perp ((locH Z p).X (A p).f)`. Take `⟨-, -, xz, hxz, -, -⟩` from `hL`. Rewrite using `[← hxz]`.

Conclude with `xz.2`. Establish `hnz : n (A p).z ∈ lattice₂ D Z.M p Λ`. Rewrite using `[hlat]`. Conclude with `Submodule.mem_map_of_mem (z_mem_LamStd _ (A p) hL)`. Establish `hxX` using `sub_mem_X_of_mem_N _ (A p) hn hperp`.

Establish `hfix : (locH Z p).X (A p).f ≤ LinearMap.eqLocus (GlobalTheory.LocExt.locEnd p π) LinearMap.id`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Use `show (GlobalTheory.LocExt.locEnd p π) ((A p).f a.castSucc) = (A p).f a.castSucc`. Rewrite using `[hA p]`.

Rewrite using `[map_smul, GlobalTheory.LocExt.locEnd_bcP, GlobalTheory.LocExt.frame_castSucc, hπX _ (Submodule.subset_span ⟨a, rfl⟩)]`. Use `show _ = frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)`. Rewrite using `[GlobalTheory.LocExt.frame_castSucc]`. Establish `hx1 : n (A p).z - (A p).z ∈ lattice₂ D Z.M p Λ₁`. Rewrite using `[hΛ₁]`.

Use `Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) ?_` and prove the remaining obligations. Rewrite using `[hzp]`. Conclude with `Submodule.subset_span ⟨G.fl.z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩`. Establish `hx2 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) ∈ lattice₂ D Z.M p (Λ₁.map (π.restrictScalars (𝓞 D.host.E)))`. Rewrite using `[GlobalTheory.FrameProj.localLattice_map Z p π (GlobalTheory.LocExt.locEnd p π) (fun x => (GlobalTheory.LocExt.locEnd_bcP p π x).symm) Λ₁]`.

Conclude with `Submodule.mem_map_of_mem hx1`. Establish `hx3 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) = n (A p).z - (A p).z` using `hfix hxX`. Rewrite `hx2` using `[hx3]`. Establish `e : baseChange₂ D p G.fl.z = n (A p).z - (n (A p).z - (A p).z)` using `by rw [hzp]; abel`. Rewrite using `[e, hΛ₂]`.

Conclude with `Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hx2)`. Rewrite `hz` using `[hΛ₂]`. Take `⟨l, hl, y, hy, hly⟩` from `Submodule.mem_sup.1 hz`. Take `⟨w, -, rfl⟩` from `hy`. Use `⟨-(π w), Submodule.neg_mem _ (hπmem w), ?_⟩` and prove the remaining obligations.

Establish `e : G.fl.z + -(π w) = l`. Rewrite using `[← hly]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `hl`.
-/
theorem exists_add_mem : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D)
    (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS),
    (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D,
    Submodule.IsLattice D.host.E Λ →
    (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) →
    ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  intro D T G Z A hA Λ hΛ hloc
  obtain ⟨π, hπX, hπmem⟩ : ∃ π : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ G.fl.X, π x = x) ∧ ∀ x, π x ∈ G.fl.X := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective G.fl.X.subtype (Submodule.ker_subtype _)
    refine ⟨G.fl.X.subtype ∘ₗ g, fun x hx => ?_, fun x => (g x).2⟩
    have := congrArg (fun f => ((f ⟨x, hx⟩ : G.fl.X) : (VS D).V)) hg
    exact this
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ N : LV D, N = Λ ⊔ Submodule.span (𝓞 D.host.E) {G.fl.z} := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ N : LV D, N = Λ ⊔ Λ₁.map (π.restrictScalars (𝓞 D.host.E)) := ⟨_, rfl⟩
  have hfg : Λ₂.FG := by
    rw [hΛ₂, hΛ₁]; exact hΛ.fg.sup ((hΛ.fg.sup (Submodule.fg_span_singleton _)).map _)
  have hz : G.fl.z ∈ Λ₂ := by
    refine GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z hfg fun p => ?_
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hzp : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last _) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hperp : (A p).z ∈ (locH Z p).perp ((locH Z p).X (A p).f) := by
      obtain ⟨-, -, xz, hxz, -, -⟩ := hL
      rw [← hxz]; exact xz.2
    have hnz : n (A p).z ∈ lattice₂ D Z.M p Λ := by
      rw [hlat]
      exact Submodule.mem_map_of_mem (z_mem_LamStd _ (A p) hL)
    have hxX := sub_mem_X_of_mem_N _ (A p) hn hperp
    have hfix : (locH Z p).X (A p).f ≤ LinearMap.eqLocus (GlobalTheory.LocExt.locEnd p π) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show (GlobalTheory.LocExt.locEnd p π) ((A p).f a.castSucc) = (A p).f a.castSucc
      rw [hA p]
      rw [map_smul, GlobalTheory.LocExt.locEnd_bcP, GlobalTheory.LocExt.frame_castSucc,
        hπX _ (Submodule.subset_span ⟨a, rfl⟩)]
      show _ = frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)
      rw [GlobalTheory.LocExt.frame_castSucc]
    have hx1 : n (A p).z - (A p).z ∈ lattice₂ D Z.M p Λ₁ := by
      rw [hΛ₁]
      refine Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) ?_
      rw [hzp]
      exact Submodule.subset_span ⟨G.fl.z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩
    have hx2 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) ∈ lattice₂ D Z.M p (Λ₁.map (π.restrictScalars (𝓞 D.host.E))) := by
      rw [GlobalTheory.FrameProj.localLattice_map Z p π (GlobalTheory.LocExt.locEnd p π) (fun x => (GlobalTheory.LocExt.locEnd_bcP p π x).symm) Λ₁]
      exact Submodule.mem_map_of_mem hx1
    have hx3 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) = n (A p).z - (A p).z := hfix hxX
    rw [hx3] at hx2
    have e : baseChange₂ D p G.fl.z = n (A p).z - (n (A p).z - (A p).z) := by rw [hzp]; abel
    rw [e, hΛ₂]
    exact Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz)
      (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hx2)
  rw [hΛ₂] at hz
  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.1 hz
  obtain ⟨w, -, rfl⟩ := hy
  refine ⟨-(π w), Submodule.neg_mem _ (hπmem w), ?_⟩
  have e : G.fl.z + -(π w) = l := by
    rw [← hly]; simp
  rw [e]; exact hl

end GlobalTheory.IsotropicLift
