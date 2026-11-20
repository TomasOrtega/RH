import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

noncomputable section
namespace GlobalTheory.RatMoveLat
open Matrix

/- English proof (translation)
Establish `hv : (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) = (a : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i)`. Use function extensionality and compare the values at `i`. Rewrite using `[ha]`. Conclude with `RingHom.map_mulVec _ _ _ _`. Establish `hw : (((a * g)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) = ((g⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) …`.

Rewrite using `[hv, Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Unfold `Formalism.UG.CS.globLat`. Simplify using `only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`. Establish `he : Formalism.UG.inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) = Formalism.IndefR.Datum.eToEAf D := rfl`. Rewrite using `[he, hw]`.
-/
theorem mem_globLat_rat {D : D7} {n : ℕ} (a g : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (M : Matrix (Fin n) (Fin n) D.host.E)
    (ha : a.1 = M.map (Formalism.IndefR.Datum.eToEAf D)) (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → D.host.E) :
    M *ᵥ y ∈ Formalism.UG.CS.globLat (a * g) C ↔ y ∈ Formalism.UG.CS.globLat g C := by
  have hv : (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) =
      (a : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i) := by
    funext i
    rw [ha]
    exact RingHom.map_mulVec _ _ _ _
  have hw : (((a * g)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ
        (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) =
      ((g⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ
        fun i => Formalism.IndefR.Datum.eToEAf D (y i) := by
    rw [hv, Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  unfold Formalism.UG.CS.globLat
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  have he : Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) = Formalism.IndefR.Datum.eToEAf D := rfl
  rw [he, hw]

/- English proof (translation)
Take `⟨γ, -, hfin, hmt⟩` from `h`. Establish `key : ∀ e : D.host.E, Formalism.IndefR.Lev.swapAE D ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (incA D e)) = Formalism.IndefR.Datum.eToEAf D e`. Introduce `e`. Simplify using `[Formalism.IndefR.Lev.swapAE, Formalism.IndefR.Datum.eToEAf, Formalism.L2.Theta.incA, inclR]`. Unfold `GlobalTheory.FunObj.finG Formalism.IndefR.Lev.finE`.

Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype]`. Rewrite using `[← hfin]`. Establish `hm : ((Formalism.L2.Theta.matHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D)` using `hmt`. Unfold `Formalism.L2.Theta.finHom`. Simplify using `only [Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, hm, Matrix.map_map]`.

Use extensionality with `i j`. Conclude with `key _`.
-/
theorem finG_rat {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) (h : GlobalTheory.RatMoveJets.RatCoord V fr g U) :
    (GlobalTheory.FunObj.finG V g).1 = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (Formalism.IndefR.Datum.eToEAf D) := by
  obtain ⟨γ, -, hfin, hmt⟩ := h
  have key : ∀ e : D.host.E, Formalism.IndefR.Lev.swapAE D
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (incA D e)) =
      Formalism.IndefR.Datum.eToEAf D e := by
    intro e
    simp [Formalism.IndefR.Lev.swapAE, Formalism.IndefR.Datum.eToEAf, Formalism.L2.Theta.incA, inclR]
  unfold GlobalTheory.FunObj.finG Formalism.IndefR.Lev.finE
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← hfin]
  have hm : ((Formalism.L2.Theta.matHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) =
      (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D) := hmt
  unfold Formalism.L2.Theta.finHom
  simp only [Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, hm,
    Matrix.map_map]
  ext i j
  exact key _

/- English proof (translation)
Introduce `D T L sc G W S X r U hr x`. Establish `hfr` using `finG_rat _ _ _ _ hr`. Establish `hU : U.1 * star U.1 = 1` using `Matrix.mem_unitaryGroup_iff.mp U.2`. Establish `hmv : ∀ v : Fin (G.V X).rank → D.host.E, ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1) *ᵥ ((S.N.fr X).1 *ᵥ v) = (S.N.fr X).1 *ᵥ (U.1 *ᵥ v)`. Introduce `v`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Establish `hzz : ∀ z : Fin (G.V X).rank → D.host.E, U.1 *ᵥ (star U.1 *ᵥ z) = z`. Introduce `z`. Rewrite using `[Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]`. Use extensionality with `z`.

Simplify using `only [GlobalTheory.SumSize.latAt, SDLat.smulLat, Submodule.mem_map, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.toLin'_apply, map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `⟨star U.1 *ᵥ z, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_globLat_rat _ _ _ hfr, hmv, hzz]`.

Conclude with `hz`. Conclude with `hzz z`. Introduce and unpack `⟨w, hw, rfl⟩`. Rewrite using `[← hmv, mem_globLat_rat _ _ _ hfr]`. Conclude with `hw`.
-/
theorem latAt_rat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U → ∀ x : FinPt G X,
      GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  intro D T L sc G W S X r U hr x
  have hfr := finG_rat _ _ _ _ hr
  have hU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hmv : ∀ v : Fin (G.V X).rank → D.host.E,
      ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1) *ᵥ ((S.N.fr X).1 *ᵥ v) =
        (S.N.fr X).1 *ᵥ (U.1 *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hzz : ∀ z : Fin (G.V X).rank → D.host.E, U.1 *ᵥ (star U.1 *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  ext z
  simp only [GlobalTheory.SumSize.latAt, SDLat.smulLat, Submodule.mem_map, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.toLin'_apply, map_mul]
  constructor
  · intro hz
    refine ⟨star U.1 *ᵥ z, ?_, ?_⟩
    · rw [← mem_globLat_rat _ _ _ hfr, hmv, hzz]
      exact hz
    · exact hzz z
  · rintro ⟨w, hw, rfl⟩
    rw [← hmv, mem_globLat_rat _ _ _ hfr]
    exact hw

end GlobalTheory.RatMoveLat
