import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiamondElementsStepLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Dil

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Take `⟨g, hg, k, hk, e⟩` from `(DoubleCoset.eq _ _ y' (y * δ)).1 h`. Take `⟨γ, hγ, eγ⟩` from `Subgroup.mem_subgroupOf.1 hg`. Use `⟨⟨γ, hγ⟩, ⟨k.1, Subgroup.mem_subgroupOf.1 hk⟩⁻¹, ?_⟩` and prove the remaining obligations. Establish `e' : y.1 * δ.1 = g.1 * y'.1 * k.1` using `congrArg Subtype.val e`. Use `show bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * (k.1)⁻¹`.

Rewrite using `[e', eγ, mul_inv_cancel_right]`.
-/
theorem exists_of_cls_eq (S : StepLevel F E σ J T f bad) (y y' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (h : (Quotient.mk'' y' : Cls S) = Quotient.mk'' (y * δ)) :
    ∃ γ : UJ (σ : E →+* E) J, ∃ κ : S.U,
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 * y'.1 = y.1 * δ.1 * κ.1 := by
  obtain ⟨g, hg, k, hk, e⟩ := (DoubleCoset.eq _ _ y' (y * δ)).1 h
  obtain ⟨γ, hγ, eγ⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨⟨γ, hγ⟩, ⟨k.1, Subgroup.mem_subgroupOf.1 hk⟩⁻¹, ?_⟩
  have e' : y.1 * δ.1 = g.1 * y'.1 * k.1 := congrArg Subtype.val e
  show bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * (k.1)⁻¹
  rw [e', eγ, mul_inv_cancel_right]

/- English proof (translation)
Use `haveI := S.Lb_fin`. Use `(GlobalTheory.LatticeStabLocal.mem_stabGL_adele_iff S.Lb _).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `mul_mem ?_ (Subgroup.mem_inf.1 (S.Uloc_lev w (((S.U_eq _).1 κ.2).2 w))).2` and prove the remaining obligations. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Conclude with `(Subgroup.mem_inf.1 hδ.2.1).2`. Rewrite using `[hδ.1 w hw]`. Conclude with `one_mem _`.
-/
theorem dia_mul_stab (S : StepLevel F E σ J T f bad) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (hδ : IsDia S v hv k δ) (κ : S.U) :
    δ.1 * κ.1 ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb) := by
  haveI := S.Lb_fin
  refine (GlobalTheory.LatticeStabLocal.mem_stabGL_adele_iff S.Lb _).2 fun w => ?_
  rw [map_mul]
  refine mul_mem ?_ (Subgroup.mem_inf.1 (S.Uloc_lev w (((S.U_eq _).1 κ.2).2 w))).2
  by_cases hw : w = v
  · subst hw
    exact (Subgroup.mem_inf.1 hδ.2.1).2
  · rw [hδ.1 w hw]
    exact one_mem _

/- English proof (translation)
Establish `e1 : L = Formalism.UG.CS.globLat y.1 S.Lb` using `Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat ⟨Module.Finite.iff_fg.2 hL.fg, hL.span_eq_top⟩ _ hy`. Establish `e2 : L' = Formalism.UG.CS.globLat y'.1 S.Lb` using `Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat ⟨Module.Finite.iff_fg.2 hL'.fg, hL'.span_eq_top⟩ _ hy'`. Establish `e3` using `Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) S.Lb γ y'.1 (δ.1 * κ.1)⁻¹ (inv_mem (dia_mul_stab S δ v hv k hδ κ))`. Rewrite `e3` using `[he, mul_assoc y.1, mul_inv_cancel_right, ← e1, ← e2]`. Rewrite using `[e3]`.

Both sides reduce to the same expression.
-/
theorem lat_eq_of_move (S : StepLevel F E σ J T f bad) (L L' : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L')
    (y y' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      ((y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (hy' : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔
      ((y'.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (hδ : IsDia S v hv k δ)
    (γ : GL (Fin n) E) (κ : S.U)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * κ.1) :
    Formalism.L2.Forms.mulLat γ.1 L' = L := by
  have e1 : L = Formalism.UG.CS.globLat y.1 S.Lb :=
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat ⟨Module.Finite.iff_fg.2 hL.fg, hL.span_eq_top⟩ _ hy
  have e2 : L' = Formalism.UG.CS.globLat y'.1 S.Lb :=
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat ⟨Module.Finite.iff_fg.2 hL'.fg, hL'.span_eq_top⟩ _ hy'
  have e3 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) S.Lb γ y'.1 (δ.1 * κ.1)⁻¹
    (inv_mem (dia_mul_stab S δ v hv k hδ κ))
  rw [he, mul_assoc y.1, mul_inv_cancel_right, ← e1, ← e2] at e3
  rw [e3]
  rfl

/- English proof (translation)
Use `(GlobalTheory.DualCompletion.dual_move F E σ n J v L S.Lb (bc (prV (E := E) v) y.1) hJ hL ⟨Module.Finite.iff_fg.1 S.Lb_fin, S.Lb_span⟩ (Formalism.UG.P.afsplit_bc_mem _ _ _ _ y.2) (fun x => ?_) _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hy x`.
-/
theorem dual_mem_loc (hJ : IsUnit J.det) (S : StepLevel F E σ J T f bad) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      ((y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → E)
    (hz : z ∈ Formalism.L2.Forms.dualL (σ : E →+* E) J L) :
    ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
  refine (GlobalTheory.DualCompletion.dual_move F E σ n J v L S.Lb (bc (prV (E := E) v) y.1) hJ hL
    ⟨Module.Finite.iff_fg.1 S.Lb_fin, S.Lb_span⟩ (Formalism.UG.P.afsplit_bc_mem _ _ _ _ y.2) (fun x => ?_) _).1
    (Submodule.subset_span ⟨z, hz, rfl⟩)
  rw [← map_inv]
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hy x

/- English proof (translation)
Take `⟨hg, hf⟩` from `hδ.2.2`. Establish `hk` using `((S.U_eq _).1 κ.2).2 v`. Rewrite `hk` using `[S.UlocAlt v hv]`. Take `⟨hg', hf'⟩` from `(Subgroup.mem_inf.1 hk).2`. Rewrite using `[map_mul]`.

Use `⟨mul_mem hg hg', fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf' x, ← hf ⟨_, (hg' x.1).1 x.2⟩]`. Use `congr 2`. Conclude with `Subtype.ext (by simp only [Units.val_mul, Matrix.mulVec_mulVec])`.
-/
theorem mulsF_dia_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (k : ℤ) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hδ : IsDia S v hv k δ) (κ : S.U) :
    GlobalTheory.LevelHecke.MulsF S v hv k (bc (prV (E := E) v) (δ.1 * κ.1)) := by
  obtain ⟨hg, hf⟩ := hδ.2.2
  have hk := ((S.U_eq _).1 κ.2).2 v
  rw [S.UlocAlt v hv] at hk
  obtain ⟨hg', hf'⟩ := (Subgroup.mem_inf.1 hk).2
  rw [map_mul]
  refine ⟨mul_mem hg hg', fun x => ?_⟩
  rw [← hf' x, ← hf ⟨_, (hg' x.1).1 x.2⟩]
  congr 2
  exact Subtype.ext (by simp only [Units.val_mul, Matrix.mulVec_mulVec])

/- English proof (translation)
Establish `e : y.1⁻¹ * bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = δ.1 * κ.1 := by`. Rewrite using `[mul_assoc, he, mul_assoc, inv_mul_cancel_left]`. Establish `hm` using `GlobalTheory.LevelHecke.MovePair.mov_mulVec v y.1 y'.1 γ z`. Rewrite `hm` using `[e]`. Conclude with `(GlobalTheory.LevelHecke.MovePair.mulsF_apply S v hv k _ (mulsF_dia_mul S v hv k δ hδ κ) φ _ _ hm).2 hz' hz`.
-/
theorem fT_move (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (k : ℤ) (y y' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hδ : IsDia S v hv k δ)
    (γ : GL (Fin n) E) (κ : S.U)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * κ.1) (z : Fin n → E)
    {R : Type} [Ring R] (φ : S.fM v hv ≃+ R)
    (hz' : ((bc (prV (E := E) v) y'.1)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hz : ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    φ (S.fT v hv ⟨_, hz'⟩) = (k : R) * φ (S.fT v hv ⟨_, hz⟩) := by
  have e : y.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = δ.1 * κ.1 := by
    rw [mul_assoc, he, mul_assoc, inv_mul_cancel_left]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec v y.1 y'.1 γ z
  rw [e] at hm
  exact (GlobalTheory.LevelHecke.MovePair.mulsF_apply S v hv k _ (mulsF_dia_mul S v hv k δ hδ κ) φ _ _ hm).2 hz' hz

end Gen

section Steps

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨γ, κ, he⟩` from `exists_of_cls_eq (T.cls i hi h).lev _ _ δ ((T.val i hi h).dil v a k hk c δ hδ)`. Use `⟨γ, ⟨fun _ => ⟨κ.1, κ.2, δ.1, δ.2, hδ.1, he⟩, fun h1 h2 => by omega⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `lat_eq_of_move (T.cls i hi h).lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi c) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ _ δ ((T.cls i hi h).y_lat c) ((T.cls i hi h).y_lat _) _ _ k hδ γ.1 κ he`. Introduce and unpack `z ⟨w, hw⟩ e`. Take `rfl : w = γ.1.1 *ᵥ z.1` from `e`.

Establish `m1` using `dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (T.cls i hi h).lev _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ ((T.cls i hi h).y_lat ((D.fm u).dil i v a c)) (T.atT.eV v).1 z.1 z.2`. Establish `m2` using `dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (T.cls i hi h).lev _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ ((T.cls i hi h).y_lat c) (T.atT.eV v).1 _ hw`. Establish `e1` using `T.fv i hi h v _ z m1`. Establish `e2` using `T.fv i hi h v c ⟨_, hw⟩ m2`. Establish `e3` using `fT_move (T.cls i hi h).lev _ _ k _ _ δ hδ γ.1 κ he z.1 (T.fMe i hi h v) m1 m2`.

Rewrite using `[← hk]`. Conclude with `e1.trans (e3.trans (congrArg (fun t => (k : (D.mem u).A.Fv v) * t) e2.symm))`.
-/
theorem move_end (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a)
    (δ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia (T.cls i hi h).lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      AdC T i hi c ((D.fm u).dil i v a c) γ.1 (T.atT.eV v).1 ∧
      Formalism.L2.Forms.mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).dil i v a c)) = clsCrd D u i hi c ∧
      ∀ (z : Formalism.L2.Forms.Ld D u i hi ((D.fm u).dil i v a c)) (z' : Formalism.L2.Forms.Ld D u i hi c), z'.1 = γ.1.1 *ᵥ z.1 →
        (D.fm u).fv i v _ ((T.lv i hi).pr v _ z) =
          (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((T.lv i hi).pr v c z') := by
  obtain ⟨γ, κ, he⟩ := exists_of_cls_eq (T.cls i hi h).lev _ _ δ ((T.val i hi h).dil v a k hk c δ hδ)
  refine ⟨γ, ⟨fun _ => ⟨κ.1, κ.2, δ.1, δ.2, hδ.1, he⟩, fun h1 h2 => by omega⟩, ?_, ?_⟩
  · exact lat_eq_of_move (T.cls i hi h).lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi c)
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ _ δ ((T.cls i hi h).y_lat c) ((T.cls i hi h).y_lat _)
      _ _ k hδ γ.1 κ he
  · rintro z ⟨w, hw⟩ e
    obtain rfl : w = γ.1.1 *ᵥ z.1 := e
    have m1 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (T.cls i hi h).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ ((T.cls i hi h).y_lat ((D.fm u).dil i v a c)) (T.atT.eV v).1 z.1 z.2
    have m2 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (T.cls i hi h).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ ((T.cls i hi h).y_lat c) (T.atT.eV v).1 _ hw
    have e1 := T.fv i hi h v _ z m1
    have e2 := T.fv i hi h v c ⟨_, hw⟩ m2
    have e3 := fT_move (T.cls i hi h).lev _ _ k _ _ δ hδ γ.1 κ he z.1 (T.fMe i hi h v) m1 m2
    rw [← hk]
    exact e1.trans (e3.trans (congrArg (fun t => (k : (D.mem u).A.Fv v) * t) e2.symm))

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Establish `hβ : chOf i ((D.fm u).dil i v a c) = chOf i c` using `(T.dilC i h1 h2).ch v a c`. Take `⟨γ, κ, he⟩` from `exists_of_cls_eq (T.ch i h1 h2 (chOf i c)).lev ((T.ch i h1 h2 (chOf i c)).y ⟨c, rfl⟩) ((T.ch i h1 h2 (chOf i c)).y ⟨_, hβ⟩) δ ((T.dilC i h1 h2).dil v a k hk (chOf i c) ⟨c, rfl⟩ δ hδ)`. Use `⟨γ, ⟨fun h => by omega, fun _ _ => ⟨hβ, κ.1, κ.2, δ.1, δ.2, hδ.1, he⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `lat_eq_of_move (T.ch i h1 h2 (chOf i c)).lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ c) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ _ δ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩) ((T.ch i h1 h2 (chOf i c)).y …`. Introduce and unpack `z ⟨w, hw⟩ e`.

Take `rfl : w = γ.1.1 *ᵥ z.1` from `e`. Establish `m1` using `dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i _) (T.ch i h1 h2 (chOf i c)).lev _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨_, hβ⟩) (T.atT.eV v).1 z.1 z.2`. Establish `m2` using `dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i _) (T.ch i h1 h2 (chOf i c)).lev _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩) (T.atT.eV v).1 _ hw`. Establish `e1` using `T.fvC i h1 h2 v (chOf i c) ⟨_, hβ⟩ z m1`. Establish `e2` using `T.fvC i h1 h2 v (chOf i c) ⟨c, rfl⟩ ⟨_, hw⟩ m2`.

Establish `e3` using `fT_move (T.ch i h1 h2 (chOf i c)).lev _ _ k _ _ δ hδ γ.1 κ he z.1 (T.fMeC i h1 h2 (chOf i c) v) m1 m2`. Rewrite using `[← hk]`. Conclude with `e1.trans (e3.trans (congrArg (fun t => (k : (D.mem u).A.Fv v) * t) e2.symm))`.
-/
theorem move_mid (T : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a)
    (δ : UPts (sigD D) (gramN D i (le_of_succ_m h2)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia (T.ch i h1 h2 (chOf i c)).lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (le_of_succ_m h2)),
      AdC T i (le_of_succ_m h2) c ((D.fm u).dil i v a c) γ.1 (T.atT.eV v).1 ∧
      Formalism.L2.Forms.mulLat γ.1.1 (clsCrd D u i (le_of_succ_m h2) ((D.fm u).dil i v a c)) =
        clsCrd D u i (le_of_succ_m h2) c ∧
      ∀ (z : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) ((D.fm u).dil i v a c))
        (z' : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) c), z'.1 = γ.1.1 *ᵥ z.1 →
        (D.fm u).fv i v _ ((T.lvC i h1 h2).pr v _ z) =
          (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((T.lvC i h1 h2).pr v c z') := by
  have hβ : chOf i ((D.fm u).dil i v a c) = chOf i c := (T.dilC i h1 h2).ch v a c
  obtain ⟨γ, κ, he⟩ := exists_of_cls_eq (T.ch i h1 h2 (chOf i c)).lev ((T.ch i h1 h2 (chOf i c)).y ⟨c, rfl⟩)
    ((T.ch i h1 h2 (chOf i c)).y ⟨_, hβ⟩) δ ((T.dilC i h1 h2).dil v a k hk (chOf i c) ⟨c, rfl⟩ δ hδ)
  refine ⟨γ, ⟨fun h => by omega, fun _ _ => ⟨hβ, κ.1, κ.2, δ.1, δ.2, hδ.1, he⟩⟩, ?_, ?_⟩
  · exact lat_eq_of_move (T.ch i h1 h2 (chOf i c)).lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ c)
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ _ δ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩)
      ((T.ch i h1 h2 (chOf i c)).y_lat ⟨_, hβ⟩) _ _ k hδ γ.1 κ he
  · rintro z ⟨w, hw⟩ e
    obtain rfl : w = γ.1.1 *ᵥ z.1 := e
    have m1 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i _) (T.ch i h1 h2 (chOf i c)).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨_, hβ⟩) (T.atT.eV v).1 z.1 z.2
    have m2 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i _) (T.ch i h1 h2 (chOf i c)).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩) (T.atT.eV v).1 _ hw
    have e1 := T.fvC i h1 h2 v (chOf i c) ⟨_, hβ⟩ z m1
    have e2 := T.fvC i h1 h2 v (chOf i c) ⟨c, rfl⟩ ⟨_, hw⟩ m2
    have e3 := fT_move (T.ch i h1 h2 (chOf i c)).lev _ _ k _ _ δ hδ γ.1 κ he z.1 (T.fMeC i h1 h2 (chOf i c) v) m1 m2
    rw [← hk]
    exact e1.trans (e3.trans (congrArg (fun t => (k : (D.mem u).A.Fv v) * t) e2.symm))

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Use `⟨?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩` and prove the remaining obligations. Use `Submodule.map_injective_of_injective (f := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) (crdN D i hi).injective ?_` and prove the remaining obligations. Conclude with `(lc_gmap i hi γ _).trans hl`. Rewrite using `[prH_eq A P hi, prH_eq A P hi]`. Conclude with `hv _ _ (crdN_gx i hi γ z.1)`.

Rewrite using `[prH_eq A P hi, prH_eq A P hi]`. Conclude with `ho v' hv' _ _ (crdN_gx i hi γ z.1)`.
-/
theorem dilCl_of_crd (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi) (i : ℕ) (hi : i ≤ D.R.m)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.L2.Forms.mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).dil i v a c)) = clsCrd D u i hi c)
    (hv : ∀ (z : Formalism.L2.Forms.Ld D u i hi ((D.fm u).dil i v a c)) (z' : Formalism.L2.Forms.Ld D u i hi c), z'.1 = γ.1.1 *ᵥ z.1 →
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((P i hi).pr v c z'))
    (ho : ∀ v', v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld D u i hi c) (z' : Formalism.L2.Forms.Ld D u i hi ((D.fm u).dil i v a c)),
        z.1 = γ.1.1 *ᵥ z'.1 → (D.fm u).fv i v' _ ((P i hi).pr v' _ z') = (D.fm u).fv i v' c ((P i hi).pr v' c z)) :
    DilCl A P i v a c (gx i hi γ) := by
  refine ⟨?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · refine Submodule.map_injective_of_injective
      (f := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)))
      (crdN D i hi).injective ?_
    exact (lc_gmap i hi γ _).trans hl
  · rw [prH_eq A P hi, prH_eq A P hi]
    exact hv _ _ (crdN_gx i hi γ z.1)
  · rw [prH_eq A P hi, prH_eq A P hi]
    exact ho v' hv' _ _ (crdN_gx i hi γ z.1)

end Steps

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `B X I hOk hP l Z H F hF hC u i v a c`. Distinguish the cases in `hi : i ≤ (I.rec7 l Z).R.m`. Use `swap`. Conclude with `⟨1, fun h => absurd h hi⟩`. Take `⟨k, hk, hE, hM⟩` from `GlobalTheory.T.exists_diamond_elements_step_levels I hOk hP l Z H F hF hC u i hi v a`.

Establish `core : ∃ γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi), AdC (F u) i hi c (((I.rec7 l Z).fm u).dil i v a c) γ.1 ((F u).atT.eV v).1 ∧ Formalism.L2.Forms.mulLat γ.1.1 (clsCrd (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dil i v a c)) …`. Distinguish the cases in `h : i = 0 ∨ i = (I.rec7 l Z).R.m`. Take `⟨δ, hδ⟩` from `hE h`. Conclude with `move_end (F u) i hi h v a c k hk δ hδ`. Establish `h1 : 1 ≤ i` using `by omega`.

Establish `h2 : i + 1 ≤ (I.rec7 l Z).R.m` using `by omega`. Take `⟨δ, hδ⟩` from `hM h1 h2 (H.chOf u i c)`. Take `⟨γ, g1, g2, g3⟩` from `move_mid (F u) i h1 h2 v a c k hk δ hδ`. Use `⟨γ, g1, g2, fun z z' e => ?_⟩` and prove the remaining obligations. Establish `e1` using `(GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hF hC u i h1 h2 v _).1 z z rfl`.

Establish `e2` using `(GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hF hC u i h1 h2 v c).1 z' z' rfl`. Establish `e3` using `g3 z z' e`. Rewrite `e3` using `[e1, e2]`. Conclude with `e3`. Take `⟨γ, g1, g2, g3⟩` from `core`.

Conclude with `⟨gx i hi γ, fun _ => ⟨dilCl_of_crd (F u).atT (F u).lv i hi v a c γ g2 g3 (fun v' hv' z z' e => GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hP l Z H F hF hC u i hi v v' c _ γ.1 g1 hv' z z' e), GlobalTheory.T.adelic_relation_classes_coordinates I hOk hP l Z …`.
-/
theorem diamond_on_hermitian_side : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ) (c : ((I.rec7 l Z).mem u).C.cls i), ∃ γ, i ≤ (I.rec7 l Z).R.m → DilCl (F u).atT (F u).lv i v a c γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dil i v a c) γ v := by
  intro B X I hOk hP l Z H F hF hC u i v a c
  by_cases hi : i ≤ (I.rec7 l Z).R.m
  swap
  · exact ⟨1, fun h => absurd h hi⟩
  obtain ⟨k, hk, hE, hM⟩ := GlobalTheory.T.exists_diamond_elements_step_levels I hOk hP l Z H F hF hC u i hi v a
  have core : ∃ γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi),
      AdC (F u) i hi c (((I.rec7 l Z).fm u).dil i v a c) γ.1 ((F u).atT.eV v).1 ∧
      Formalism.L2.Forms.mulLat γ.1.1 (clsCrd (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dil i v a c)) =
        clsCrd (I.rec7 l Z) u i hi c ∧
      ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dil i v a c))
        (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c), z'.1 = γ.1.1 *ᵥ z.1 →
        ((I.rec7 l Z).fm u).fv i v _ (((F u).lv i hi).pr v _ z) =
          (a : ((I.rec7 l Z).mem u).A.Fv v) * ((I.rec7 l Z).fm u).fv i v c (((F u).lv i hi).pr v c z') := by
    by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
    · obtain ⟨δ, hδ⟩ := hE h
      exact move_end (F u) i hi h v a c k hk δ hδ
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
      obtain ⟨δ, hδ⟩ := hM h1 h2 (H.chOf u i c)
      obtain ⟨γ, g1, g2, g3⟩ := move_mid (F u) i h1 h2 v a c k hk δ hδ
      refine ⟨γ, g1, g2, fun z z' e => ?_⟩
      have e1 := (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hF hC u i h1 h2 v _).1 z z rfl
      have e2 := (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hF hC u i h1 h2 v c).1 z' z' rfl
      have e3 := g3 z z' e
      rw [e1, e2] at e3
      exact e3
  obtain ⟨γ, g1, g2, g3⟩ := core
  exact ⟨gx i hi γ, fun _ => ⟨dilCl_of_crd (F u).atT (F u).lv i hi v a c γ g2 g3
    (fun v' hv' z z' e => GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hP l Z H F hF hC u i hi v v' c _ γ.1 g1 hv' z z' e),
    GlobalTheory.T.adelic_relation_classes_coordinates I hOk hP l Z H F hF hC u i hi v c _ γ g1⟩⟩

end GlobalTheory.Mem.Col2.HAt.Dil
