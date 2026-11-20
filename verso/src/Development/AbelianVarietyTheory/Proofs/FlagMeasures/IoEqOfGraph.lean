import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalInnerLatticeEqOfInnerPreimageEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ApproxGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.IotaLocA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

/- English proof (translation)
The claim follows from `(Zd.agree p).2.2.2.1`.
-/
theorem hO : (Zd.M p).L.O = (D.s.atP p).O := (Zd.agree p).2.2.2.1

/- English proof (translation)
The claim follows from `(lattice₂ D Zd.M p Λ).smul_mem (⟨a, by rw [hO Zd p]; exact ha⟩ : (Zd.M p).L.O) hv`.
-/
theorem smul_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O)
    {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) : a • v ∈ lattice₂ D Zd.M p Λ :=
  (lattice₂ D Zd.M p Λ).smul_mem (⟨a, by rw [hO Zd p]; exact ha⟩ : (Zd.M p).L.O) hv

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨y, hy, rfl⟩`.
-/
theorem baseChange_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {y : (VS D).V} (hy : y ∈ Λ) (p : PlF D) :
    baseChange₂ D p y ∈ lattice₂ D Zd.M p Λ := Submodule.subset_span ⟨y, hy, rfl⟩

/- English proof (translation)
Establish `hagree` using `(Zd.agree p).2.2.2.2.2`. Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases. Rewrite `hagree` using `[hg, hs]`. Conclude with `hagree.elim`. Rewrite `hagree` using `[hg, hs]`.

Conclude with `⟨sg, rfl, hagree.2, hagree.1⟩`.
-/
theorem typed_data (g : Loc.SplitG (Zd.M p).L) (hg : (Zd.M p).split = some g) :
    ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q ∧ g.e = sg.e := by
  have hagree := (Zd.agree p).2.2.2.2.2
  rcases hs : (D.s.atP p).split with _ | sg
  · rw [hg, hs] at hagree; exact hagree.elim
  · rw [hg, hs] at hagree; exact ⟨sg, rfl, hagree.2, hagree.1⟩

/- English proof (translation)
Take `⟨sg, hsg, hq, -⟩` from `typed_data Zd p g hs`. Use `⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E), Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_natCast]`. Conclude with `natCast_mem _ _`. Rewrite using `[hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]`.

Simplify using `only [Nat.cast_mul, map_mul, map_natCast]`. Rewrite using `[← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]`. Establish `h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0`. Conclude with `Formalism.MainNotions.BridgeLemma.oth_ne_zero p` after adjusting the coercions. Use `push_cast`.

Rewrite using `[mul_inv_cancel₀ h0, map_one]`.
-/
theorem gS_typed (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O, ∃ w' ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w ∧
        w * w' = 1 := by
  obtain ⟨sg, hsg, hq, -⟩ := typed_data Zd p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E),
    Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem localLattice_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B :=
  Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨y, hy, rfl⟩` from `hv`. Rewrite using `[← Formalism.L2.SG.TermLoc.baseChange_smul₂]`. Use `Submodule.subset_span ⟨_, ?_, rfl⟩` and prove the remaining obligations.

Establish `h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y`. Rewrite using `[← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]`. Rewrite using `[SetLike.mem_coe, h1]`. Use `Submodule.mem_sup_left (Submodule.mem_sup_left ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul o v _ hv`.

Establish `e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v)` using `by show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _`. Rewrite using `[smul_smul, smul_smul, mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hv`.
-/
theorem smul_gS_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [← Formalism.L2.SG.TermLoc.baseChange_smul₂]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y := by
      rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]
    rw [SetLike.mem_coe, h1]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
      show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hv

/- English proof (translation)
Take `⟨w, -, w', hw', he, hww⟩` from `gS_typed Zd p g hs`. Establish `e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v)`. Rewrite using `[he, smul_smul, mul_assoc, hww, mul_one]`. Rewrite using `[e]`. Conclude with `smul_gS_mem Zd p F F' (smul_mem_localLattice Zd p hw' hv)`.
-/
theorem typed_q_mem (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨w, -, w', hw', he, hww⟩ := gS_typed Zd p g hs
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v) := by
    rw [he, smul_smul, mul_assoc, hww, mul_one]
  rw [e]
  exact smul_gS_mem Zd p F F' (smul_mem_localLattice Zd p hw' hv)

/- English proof (translation)
The claim follows from `(Submodule.mem_inf.1 hx).1`.
-/
theorem xi_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {x : (VS D).V}
    (hx : x ∈ XLam Λ F) : x ∈ Λ := (Submodule.mem_inf.1 hx).1

/- English proof (translation)
Establish `hle : NgX Λ (gS D) F F' ≤ Λ`. Use `sup_le (sup_le ?_ inf_le_left) inf_le_left` and prove the remaining obligations. Conclude with `Submodule.smul_le_right`. Use `⟨hΛ.fg.of_le hle, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hΛ.span_eq_top, Submodule.span_le]`.

Introduce `v hv`. Establish `h0 : ((gS D : ℕ) : D.host.E) ≠ 0` using `Formalism.L2.SG.Pf.StabIntSh.gS_ne`. Establish `hm : ((gS D : ℕ) : 𝓞 D.host.E) • v ∈ NgX Λ (gS D) F F'` using `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv))`. Establish `e : v = (((gS D : ℕ) : D.host.E))⁻¹ • (((gS D : ℕ) : 𝓞 D.host.E) • v)`. Rewrite using `[← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ h0, one_smul]`.

Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hm)`.
-/
theorem isLattice_NgX {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : Submodule.IsLattice D.host.E (NgX Λ (gS D) F F') := by
  have hle : NgX Λ (gS D) F F' ≤ Λ := by
    refine sup_le (sup_le ?_ inf_le_left) inf_le_left
    exact Submodule.smul_le_right
  refine ⟨hΛ.fg.of_le hle, ?_⟩
  rw [eq_top_iff, ← hΛ.span_eq_top, Submodule.span_le]
  intro v hv
  have h0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hm : ((gS D : ℕ) : 𝓞 D.host.E) • v ∈ NgX Λ (gS D) F F' :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv))
  have e : v = (((gS D : ℕ) : D.host.E))⁻¹ • (((gS D : ℕ) : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

/- English proof (translation)
Take `⟨a, ha, ξ', hξ', rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨b, hb, ξ, hξ, rfl⟩` from `Submodule.mem_sup.1 ha`. Rewrite `hb` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨l, hl, rfl⟩` from `hb`. Use `⟨l, hl, ξ, hξ, ξ', hξ', ?_⟩` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) l, map_natCast]`.
-/
theorem NgX_dec {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {F' : LFlag (VS D) D.R.rS T'} {x : (VS D).V} (hx : x ∈ NgX Λ (gS D) F F') :
    ∃ l ∈ Λ, ∃ ξ ∈ XLam Λ F, ∃ ξ' ∈ XLam Λ F', x = ((gS D : ℕ) : D.host.E) • l + ξ + ξ' := by
  obtain ⟨a, ha, ξ', hξ', rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, hb, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hb
  obtain ⟨l, hl, rfl⟩ := hb
  refine ⟨l, hl, ξ, hξ, ξ', hξ', ?_⟩
  rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) l, map_natCast]

/- English proof (translation)
Use `Submodule.span_induction (p := fun u _ => baseChange₂ D p u ∈ (locH Zd p).X f) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Take `⟨c, hc⟩` from `(Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Zd p a.castSucc).exists_left_inv`. Establish `: baseChange₂ D p (G.fl.e a) = c • f a.castSucc`. Rewrite using `[hf]`.

Simplify using `only`. Rewrite using `[smul_smul, hc, one_smul]`. Simplify using `[frame, FlagG.fvec]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.

Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.

Introduce `c a _ ha`. Rewrite using `[Formalism.L2.SG.TermLoc.baseChange_smul₂]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem bcP_X {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (f : Fin (D.R.rS + 1) → Vp D p)
    (hf : f = fun a => frFac Zd.δ p a • baseChange₂ D p (frame G a)) {u : (VS D).V} (hu : u ∈ Xsp G) :
    baseChange₂ D p u ∈ (locH Zd p).X f := by
  refine Submodule.span_induction (p := fun u _ => baseChange₂ D p u ∈ (locH Zd p).X f) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Zd p a.castSucc).exists_left_inv
    have : baseChange₂ D p (G.fl.e a) = c • f a.castSucc := by
      rw [hf]; simp only; rw [smul_smul, hc, one_smul]; simp [frame, FlagG.fvec]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
  · intro c a _ ha; rw [Formalism.L2.SG.TermLoc.baseChange_smul₂]; exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Establish `h1 : l ∈ Lsub Λ₁ G` using `⟨Submodule.mem_sup_left hl, hl.2⟩`. Rewrite `h1` using `[h]`. Take `⟨m, hm, x, hx, rfl⟩` from `Submodule.mem_sup.1 h1.1`. Conclude with `⟨m, hm, by simpa using hx⟩`.
-/
theorem rep_of_lsub {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {Λ₁ Λ₂ : LV D} (h : Lsub Λ₁ G = Lsub Λ₂ G)
    {l : (VS D).V} (hl : l ∈ Lrep Λ₁ G) : ∃ m ∈ Lrep Λ₂ G, l - m ∈ Xsp G := by
  have h1 : l ∈ Lsub Λ₁ G := ⟨Submodule.mem_sup_left hl, hl.2⟩
  rw [h] at h1
  obtain ⟨m, hm, x, hx, rfl⟩ := Submodule.mem_sup.1 h1.1
  exact ⟨m, hm, by simpa using hx⟩

/- English proof (translation)
Take `⟨w, hw, w', -, he, -⟩` from `gS_typed Zd p g hs`. Rewrite using `[Formalism.L2.SG.TermLoc.baseChange_smul₂, he, mul_smul]`. Conclude with `Submodule.subset_span ⟨w • baseChange₂ D p l, smul_mem_localLattice Zd p hw (baseChange_mem_localLattice Zd hl p), rfl⟩`.
-/
theorem q_of_g (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : LV D} {l : (VS D).V} (hl : l ∈ Λ) :
    baseChange₂ D p (((gS D : ℕ) : D.host.E) • l) ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Zd.M p Λ) := by
  obtain ⟨w, hw, w', -, he, -⟩ := gS_typed Zd p g hs
  rw [Formalism.L2.SG.TermLoc.baseChange_smul₂, he, mul_smul]
  exact Submodule.subset_span ⟨w • baseChange₂ D p l, smul_mem_localLattice Zd p hw (baseChange_mem_localLattice Zd hl p), rfl⟩

/- English proof (translation)
Use `(Submodule.span_le.2 ?_) hv` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `typed_q_mem Zd p g hs F F' hv`.
-/
theorem q_le_NgX (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : LV D} {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {v : Vp D p}
    (hv : v ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Zd.M p Λ)) :
    v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  refine (Submodule.span_le.2 ?_) hv
  rintro _ ⟨v, hv, rfl⟩
  exact typed_q_mem Zd p g hs F F' hv

/- English proof (translation)
Introduce and unpack `_ ⟨x', x, a, b, c, rfl⟩`. Take `⟨y, hy, y', hy', d1, d2, d3⟩` from `h x x' x.2 x'.2 b a c`. Establish `p1 : y ∈ H.perp (H.X f)`. Use `sub_mem x.2 (hX d1)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Establish `p2 : y' ∈ H.perp (H.X f')`. Use `sub_mem x'.2 (hX' d2)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Use `⟨⟨y', p2⟩, ⟨y, p1⟩, hy', hy, d3, Prod.ext ?_ ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.eq _).2 (by simpa using d2)`.

Conclude with `(Submodule.Quotient.eq _).2 (by simpa using d1)`.
-/
theorem io_sub {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (g : Loc.SplitG M.L) {r : ℕ} (L₁ L₂ : Submodule M.L.O V) (f f' : Fin (r + 1) → V) (T T' : F)
    (hX : H.X f ≤ H.perp (H.X f)) (hX' : H.X f' ≤ H.perp (H.X f'))
    (h : ∀ x x' : V, x ∈ H.perp (H.X f) → x' ∈ H.perp (H.X f') → x ∈ L₁ → x' ∈ L₁ →
      x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) L₁ →
      ∃ y ∈ L₂, ∃ y' ∈ L₂, x - y ∈ H.X f ∧ x' - y' ∈ H.X f' ∧ y - y' ∈ H.smulLat (algebraMap F E (g.q : F)) L₂) :
    H.iotaGraph g ⟨L₁, f, f', T, T'⟩ ⊆ H.iotaGraph g ⟨L₂, f, f', T, T'⟩ := by
  rintro _ ⟨x', x, a, b, c, rfl⟩
  obtain ⟨y, hy, y', hy', d1, d2, d3⟩ := h x x' x.2 x'.2 b a c
  have p1 : y ∈ H.perp (H.X f) := by
    have := sub_mem x.2 (hX d1)
    rwa [sub_sub_cancel] at this
  have p2 : y' ∈ H.perp (H.X f') := by
    have := sub_mem x'.2 (hX' d2)
    rwa [sub_sub_cancel] at this
  refine ⟨⟨y', p2⟩, ⟨y, p1⟩, hy', hy, d3, Prod.ext ?_ ?_⟩
  · exact (Submodule.Quotient.eq _).2 (by simpa using d2)
  · exact (Submodule.Quotient.eq _).2 (by simpa using d1)

/- English proof (translation)
Take `⟨w, hw, w', -, he, -⟩` from `gS_typed Zd p g hs`. Rewrite using `[he, mul_smul]`. Conclude with `Submodule.subset_span ⟨w • v, smul_mem_localLattice Zd p hw hv, rfl⟩`.
-/
theorem gsmul_q (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : LV D} {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Zd.M p Λ) := by
  obtain ⟨w, hw, w', -, he, -⟩ := gS_typed Zd p g hs
  rw [he, mul_smul]
  exact Submodule.subset_span ⟨w • v, smul_mem_localLattice Zd p hw hv, rfl⟩

/- English proof (translation)
Rewrite using `[map_natCast]`. Conclude with `natCast_mem _ _`.
-/
theorem g_mem_O : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) ∈ (D.s.atP p).O := by
  rw [map_natCast]; exact natCast_mem _ _

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨l, hl, rfl⟩` from `hw`. Take `⟨m, hm, hlm⟩` from `rep_of_lsub G h hl`. Conclude with `⟨baseChange₂ D p m, baseChange_mem_localLattice Zd (Submodule.mem_inf.1 hm).1 p, by rw [← map_sub]; exact bcP_X Zd p G f hf hlm⟩`.

Consider the case `zero => exact ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨u, hu, e1⟩` from `ha`. Take `⟨v, hv, e2⟩` from `hb`. Conclude with `⟨u + v, add_mem hu hv, by rw [add_sub_add_comm]; exact add_mem e1 e2⟩`.

Consider the case `smul o a _ ha`. Take `⟨u, hu, e1⟩` from `ha`. Use `⟨o • u, Submodule.smul_mem _ _ hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Conclude with `Submodule.smul_mem ((locH Zd p).X f) (o : (D.s.atP p).Ep) e1`.
-/
theorem rep_loc {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (f : Fin (D.R.rS + 1) → Vp D p)
    (hf : f = fun a => frFac Zd.δ p a • baseChange₂ D p (frame G a)) {Λ₁ Λ₂ : LV D} (h : Lsub Λ₁ G = Lsub Λ₂ G)
    {w : Vp D p} (hw : w ∈ lattice₂ D Zd.M p (Lrep Λ₁ G)) : ∃ v ∈ lattice₂ D Zd.M p Λ₂, w - v ∈ (locH Zd p).X f := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    obtain ⟨m, hm, hlm⟩ := rep_of_lsub G h hl
    exact ⟨baseChange₂ D p m, baseChange_mem_localLattice Zd (Submodule.mem_inf.1 hm).1 p, by rw [← map_sub]; exact bcP_X Zd p G f hf hlm⟩
  | zero => exact ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, e1⟩ := ha
    obtain ⟨v, hv, e2⟩ := hb
    exact ⟨u + v, add_mem hu hv, by rw [add_sub_add_comm]; exact add_mem e1 e2⟩
  | smul o a _ ha =>
    obtain ⟨u, hu, e1⟩ := ha
    refine ⟨o • u, Submodule.smul_mem _ _ hu, ?_⟩
    rw [← smul_sub]
    exact Submodule.smul_mem ((locH Zd p).X f) (o : (D.s.atP p).Ep) e1

/- English proof (translation)
Establish `hp : baseChange₂ D p (l - l') ∈ lattice₂ D Zd.M p (NgX Λ₁ (gS D) F F')`. Establish `e3 : baseChange₂ D p (l - l') = (x - x') + (baseChange₂ D p l - x) - (baseChange₂ D p l' - x')` using `by rw [map_sub]; abel`. Establish `k1` using `smul_gS_mem Zd p F F' hw`. Establish `k2` using `smul_gS_mem Zd p F F' hw'`. Rewrite `k1` using `[← e]`.

Rewrite `k2` using `[← e']`. Rewrite using `[e3]`. Conclude with `sub_mem (add_mem hd k1) k2`. Use `GlobalTheory.Unfold.LsubG.mem_of_local Zd _ (isLattice_NgX h₁ F F') _ fun q => ?_` and prove the remaining obligations. Distinguish the cases in `hq : q = p`.

Rewrite using `[hq]`. Conclude with `hp`. Rewrite using `[map_sub]`. Conclude with `sub_mem (ho q hq) (ho' q hq)`.
-/
theorem ngx_step (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {Λ₁ : LV D} (h₁ : Submodule.IsLattice D.host.E Λ₁)
    {x x' w w' : Vp D p} {l l' : (VS D).V} (hw : w ∈ lattice₂ D Zd.M p Λ₁) (hw' : w' ∈ lattice₂ D Zd.M p Λ₁)
    (e : baseChange₂ D p l - x = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w)
    (e' : baseChange₂ D p l' - x' = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w')
    (ho : ∀ q : PlF D, q ≠ p → baseChange₂ D q l ∈ lattice₂ D Zd.M q (NgX Λ₁ (gS D) F F'))
    (ho' : ∀ q : PlF D, q ≠ p → baseChange₂ D q l' ∈ lattice₂ D Zd.M q (NgX Λ₁ (gS D) F F'))
    (hd : x - x' ∈ lattice₂ D Zd.M p (NgX Λ₁ (gS D) F F')) : l - l' ∈ NgX Λ₁ (gS D) F F' := by
  have hp : baseChange₂ D p (l - l') ∈ lattice₂ D Zd.M p (NgX Λ₁ (gS D) F F') := by
    have e3 : baseChange₂ D p (l - l') = (x - x') + (baseChange₂ D p l - x) - (baseChange₂ D p l' - x') := by rw [map_sub]; abel
    have k1 := smul_gS_mem Zd p F F' hw
    have k2 := smul_gS_mem Zd p F F' hw'
    rw [← e] at k1
    rw [← e'] at k2
    rw [e3]
    exact sub_mem (add_mem hd k1) k2
  refine GlobalTheory.Unfold.LsubG.mem_of_local Zd _ (isLattice_NgX h₁ F F') _ fun q => ?_
  by_cases hq : q = p
  · rw [hq]; exact hp
  · rw [map_sub]; exact sub_mem (ho q hq) (ho' q hq)

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Conclude with `smul_gS_mem Zd p F F' (localLattice_mono Zd p hN hu)`.
-/
theorem off_step {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {Λ₁ N : LV D} (hN : N ≤ Λ₁)
    {v : Vp D p} (h : ∃ w ∈ lattice₂ D Zd.M p N, v = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) :
    v ∈ lattice₂ D Zd.M p (NgX Λ₁ (gS D) F F') := by
  obtain ⟨u, hu, rfl⟩ := h
  exact smul_gS_mem Zd p F F' (localLattice_mono Zd p hN hu)

/- English proof (translation)
Establish `: x = a - c • w` using `by rw [← e]; abel`. Substitute `this` using the available equality. Apply the tactic sequence `constructor <;> (rw [smul_sub]; abel)`.
-/
theorem alg1 {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (c : R) (x a b s w v : V) (e : a - x = c • w) :
    x - (b - s - c • v) = (a - b + s) - c • (w - v) ∧ x - (b + s - c • v) = (a - b - s) - c • (w - v) := by
  have : x = a - c • w := by rw [← e]; abel
  subst this
  constructor <;> (rw [smul_sub]; abel)

set_option maxHeartbeats 800000 in
/- English proof (translation)
Take `⟨l, hl, ⟨w, hw, e⟩, ho⟩` from `GlobalTheory.GlobalApprox.approx D Zd p _ x hx`. Take `⟨l', hl', ⟨w', hw', e'⟩, ho'⟩` from `GlobalTheory.GlobalApprox.approx D Zd p _ x' hx'`. Establish `le1 : Lrep Λ₁ F ≤ Λ₁` using `inf_le_left`. Establish `le2 : Lrep Λ₁ F' ≤ Λ₁` using `inf_le_left`. Establish `hN : l - l' ∈ NgX Λ₁ (gS D) F F'` using `ngx_step Zd p g hs F F' h₁ (localLattice_mono Zd p le1 hw) (localLattice_mono Zd p le2 hw') e e' (fun q hq => off_step Zd q F F' le1 (ho q hq)) (fun q hq => off_step Zd q F F' le2 (ho' q hq)) (q_le_NgX Zd p g hs F F' hd)`.

Take `⟨m', hm', m, hm, d', d, hN₂⟩` from `hG l' hl' l hl hN`. Take `⟨lam, hlam, ξ, hξ, ξ', hξ', heq⟩` from `NgX_dec hN₂`. Establish `hξX : ξ ∈ Xsp F` using `(Submodule.mem_inf.1 hξ).2`. Establish `hξX' : ξ' ∈ Xsp F'` using `(Submodule.mem_inf.1 hξ').2`. Take `⟨v, hv, c⟩` from `rep_loc Zd p F f hA hL hw`.

Take `⟨v', hv', c'⟩` from `rep_loc Zd p F' f' hB hL' hw'`. Establish `hvv : m - ξ - (m' + ξ') = ((gS D : ℕ) : D.host.E) • lam`. Rewrite using `[show m - ξ - (m' + ξ') = (m - m') - ξ - ξ' by abel, heq]; abel`. Use `⟨baseChange₂ D p (m - ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v, sub_mem (baseChange_mem_localLattice Zd (sub_mem (Submodule.mem_inf.1 hm).1 (xi_mem hξ)) p) (smul_mem_localLattice Zd p (g_mem_O p) hv), baseChange₂ D p (m' + ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v', …` and prove the remaining obligations. Establish `e4 : x - (baseChange₂ D p (m - ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) = baseChange₂ D p ((l - m) + ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w - v)`.

Rewrite using `[map_sub, map_add, map_sub]`. Conclude with `(alg1 _ _ _ _ _ _ _ e).1`. Rewrite using `[e4]`. Conclude with `sub_mem (bcP_X Zd p F f hA (add_mem d hξX)) (Submodule.smul_mem _ _ c)`. Establish `e4 : x' - (baseChange₂ D p (m' + ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v') = baseChange₂ D p ((l' - m') - ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' - v')`.

Rewrite using `[map_add, map_sub, map_sub]`. Conclude with `(alg1 _ _ _ _ _ _ _ e').2`. Rewrite using `[e4]`. Conclude with `sub_mem (bcP_X Zd p F' f' hB (sub_mem d' hξX')) (Submodule.smul_mem _ _ c')`. Establish `e4 : (baseChange₂ D p (m - ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) - (baseChange₂ D p (m' + ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v') = baseChange₂ D p (m - ξ - (m' + ξ')) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v'`.

Rewrite using `[map_sub (baseChange₂ D p) (m - ξ) (m' + ξ')]`. Normalize the expressions using the abelian group laws. Rewrite using `[e4, hvv]`. Conclude with `add_mem (sub_mem (q_of_g Zd p g hs hlam) (gsmul_q Zd p g hs hv)) (gsmul_q Zd p g hs hv')`.
-/
theorem place_A (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (f f' : Fin (D.R.rS + 1) → Vp D p)
    (hA : f = fun a => frFac Zd.δ p a • baseChange₂ D p (frame F a)) (hB : f' = fun a => frFac Zd.δ p a • baseChange₂ D p (frame F' a))
    {Λ₁ Λ₂ : LV D} (h₁ : Submodule.IsLattice D.host.E Λ₁) (hL : Lsub Λ₁ F = Lsub Λ₂ F) (hL' : Lsub Λ₁ F' = Lsub Λ₂ F')
    (hG : ∀ l' ∈ Lrep Λ₁ F', ∀ l ∈ Lrep Λ₁ F, l - l' ∈ NgX Λ₁ (gS D) F F' →
      ∃ m' ∈ Lrep Λ₂ F', ∃ m ∈ Lrep Λ₂ F, l' - m' ∈ Xsp F' ∧ l - m ∈ Xsp F ∧ m - m' ∈ NgX Λ₂ (gS D) F F')
    {x x' : Vp D p} (hx : x ∈ lattice₂ D Zd.M p (Lrep Λ₁ F)) (hx' : x' ∈ lattice₂ D Zd.M p (Lrep Λ₁ F'))
    (hd : x - x' ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Zd.M p Λ₁)) :
    ∃ y ∈ lattice₂ D Zd.M p Λ₂, ∃ y' ∈ lattice₂ D Zd.M p Λ₂, x - y ∈ (locH Zd p).X f ∧ x' - y' ∈ (locH Zd p).X f' ∧
      y - y' ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Zd.M p Λ₂) := by
  obtain ⟨l, hl, ⟨w, hw, e⟩, ho⟩ := GlobalTheory.GlobalApprox.approx D Zd p _ x hx
  obtain ⟨l', hl', ⟨w', hw', e'⟩, ho'⟩ := GlobalTheory.GlobalApprox.approx D Zd p _ x' hx'
  have le1 : Lrep Λ₁ F ≤ Λ₁ := inf_le_left
  have le2 : Lrep Λ₁ F' ≤ Λ₁ := inf_le_left
  have hN : l - l' ∈ NgX Λ₁ (gS D) F F' :=
    ngx_step Zd p g hs F F' h₁ (localLattice_mono Zd p le1 hw) (localLattice_mono Zd p le2 hw') e e'
      (fun q hq => off_step Zd q F F' le1 (ho q hq)) (fun q hq => off_step Zd q F F' le2 (ho' q hq))
      (q_le_NgX Zd p g hs F F' hd)
  obtain ⟨m', hm', m, hm, d', d, hN₂⟩ := hG l' hl' l hl hN
  obtain ⟨lam, hlam, ξ, hξ, ξ', hξ', heq⟩ := NgX_dec hN₂
  have hξX : ξ ∈ Xsp F := (Submodule.mem_inf.1 hξ).2
  have hξX' : ξ' ∈ Xsp F' := (Submodule.mem_inf.1 hξ').2
  obtain ⟨v, hv, c⟩ := rep_loc Zd p F f hA hL hw
  obtain ⟨v', hv', c'⟩ := rep_loc Zd p F' f' hB hL' hw'
  have hvv : m - ξ - (m' + ξ') = ((gS D : ℕ) : D.host.E) • lam := by
    rw [show m - ξ - (m' + ξ') = (m - m') - ξ - ξ' by abel, heq]; abel
  refine ⟨baseChange₂ D p (m - ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v,
    sub_mem (baseChange_mem_localLattice Zd (sub_mem (Submodule.mem_inf.1 hm).1 (xi_mem hξ)) p) (smul_mem_localLattice Zd p (g_mem_O p) hv),
    baseChange₂ D p (m' + ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v',
    sub_mem (baseChange_mem_localLattice Zd (add_mem (Submodule.mem_inf.1 hm').1 (xi_mem hξ')) p) (smul_mem_localLattice Zd p (g_mem_O p) hv'), ?_, ?_, ?_⟩
  · have e4 : x - (baseChange₂ D p (m - ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) =
        baseChange₂ D p ((l - m) + ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w - v) := by
      rw [map_sub, map_add, map_sub]; exact (alg1 _ _ _ _ _ _ _ e).1
    rw [e4]
    exact sub_mem (bcP_X Zd p F f hA (add_mem d hξX)) (Submodule.smul_mem _ _ c)
  · have e4 : x' - (baseChange₂ D p (m' + ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v') =
        baseChange₂ D p ((l' - m') - ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' - v') := by
      rw [map_add, map_sub, map_sub]; exact (alg1 _ _ _ _ _ _ _ e').2
    rw [e4]
    exact sub_mem (bcP_X Zd p F' f' hB (sub_mem d' hξX')) (Submodule.smul_mem _ _ c')
  · have e4 : (baseChange₂ D p (m - ξ) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) - (baseChange₂ D p (m' + ξ') - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v') =
        baseChange₂ D p (m - ξ - (m' + ξ')) - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v' := by
      rw [map_sub (baseChange₂ D p) (m - ξ) (m' + ξ')]; abel
    rw [e4, hvv]
    exact add_mem (sub_mem (q_of_g Zd p g hs hlam) (gsmul_q Zd p g hs hv)) (gsmul_q Zd p g hs hv')

/- English proof (translation)
Introduce `l' hl' l hl hN`. Establish `k : (l', l) ∈ (gdat F F' Λ₁).2.2` using `⟨l', hl', l, hl, by rw [sub_self]; exact zero_mem _, by rw [sub_self]; exact zero_mem _, hN⟩`. Rewrite `k` using `[h]`. Conclude with `k`.
-/
theorem graph_reps {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {Λ₁ Λ₂ : LV D}
    (h : (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2) :
    ∀ l' ∈ Lrep Λ₁ F', ∀ l ∈ Lrep Λ₁ F, l - l' ∈ NgX Λ₁ (gS D) F F' →
      ∃ m' ∈ Lrep Λ₂ F', ∃ m ∈ Lrep Λ₂ F, l' - m' ∈ Xsp F' ∧ l - m ∈ Xsp F ∧ m - m' ∈ NgX Λ₂ (gS D) F F' := by
  intro l' hl' l hl hN
  have k : (l', l) ∈ (gdat F F' Λ₁).2.2 :=
    ⟨l', hl', l, hl, by rw [sub_self]; exact zero_mem _, by rw [sub_self]; exact zero_mem _, hN⟩
  rw [h] at k
  exact k

/- English proof (translation)
The claim follows from `io_sub (locH Z p) g _ _ _ _ _ _ (GlobalTheory.Unfold.InnerLoc.X_le_perp Z p (FP p).A) (GlobalTheory.Unfold.InnerLoc.X_le_perp Z p (FP p).B) fun x x' a b c d e => place_A Z p g hs F F' (FP p).A.f (FP p).B.f (hB p).1 (hB p).2.1 h₁ hL hL' (graph_reps F F' h) (GlobalTheory.Unfold.Inn …`.
-/
theorem io_le (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)) (hB : Based Z FP Tn T'n F F') (Λ₁ Λ₂ : LV D) (h₁ : Submodule.IsLattice D.host.E Λ₁) (hL : Lsub Λ₁ F = Lsub Λ₂ F) (hL' : Lsub Λ₁ F' = Lsub Λ₂ F') (h : (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g) :
    (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ ⊆ (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ :=
  io_sub (locH Z p) g _ _ _ _ _ _ (GlobalTheory.Unfold.InnerLoc.X_le_perp Z p (FP p).A) (GlobalTheory.Unfold.InnerLoc.X_le_perp Z p (FP p).B)
    fun x x' a b c d e => place_A Z p g hs F F' (FP p).A.f (FP p).B.f (hB p).1 (hB p).2.1 h₁ hL hL' (graph_reps F F' h)
      (GlobalTheory.Unfold.InnerLoc.mem_localLattice_lrep Z p F Λ₁ h₁ (FP p).A (hB p).1 x c a)
      (GlobalTheory.Unfold.InnerLoc.mem_localLattice_lrep Z p F' Λ₁ h₁ (FP p).B (hB p).2.1 x' d b) e

/- English proof (translation)
Introduce `D Z FP Tn T'n F F' hB Λ₁ Λ₂ h₁ h₂ hL hL' h p g hs`. Conclude with `Set.Subset.antisymm (io_le Z FP Tn T'n F F' hB Λ₁ Λ₂ h₁ hL hL' h p g hs) (io_le Z FP Tn T'n F F' hB Λ₂ Λ₁ h₂ hL.symm hL'.symm h.symm p g hs)`.
-/
theorem io_eq_of_graph : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
  intro D Z FP Tn T'n F F' hB Λ₁ Λ₂ h₁ h₂ hL hL' h p g hs
  exact Set.Subset.antisymm (io_le Z FP Tn T'n F F' hB Λ₁ Λ₂ h₁ hL hL' h p g hs)
    (io_le Z FP Tn T'n F F' hB Λ₂ Λ₁ h₂ hL.symm hL'.symm h.symm p g hs)

end GlobalTheory.IotaLocA
