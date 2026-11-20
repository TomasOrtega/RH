import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.AInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨a, ha⟩` from `Frames.exists_isLatticeFrame (F := F) L`. Use `set b := Formalism.UG.bc (compFin F E v) a with hb`. Use `set N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (b⁻¹).1 * X * b.1 with hN`. Establish `hent : ∀ i j, N i j ∈ intLoc F E v`. Introduce `i j`.

Establish `h1 : b.1 *ᵥ (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v` using `(ha v (Pi.single j 1)).1 fun l => by`. Distinguish the cases in `e : l = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e]`.

Establish `h2` using `hX _ h1`. Establish `hbN : b.1 * N = X * b.1`. Rewrite using `[hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `h3 : b.1 *ᵥ (N *ᵥ Pi.single j 1) ∈ latLoc F L v`. Rewrite using `[Matrix.mulVec_mulVec, hbN, ← Matrix.mulVec_mulVec]` and apply the resulting hypothesis.

Establish `h4` using `(ha v _).2 h3 i`. Simplify using `using h4`. Establish `hdet : N.det = X.det`. Rewrite using `[hN, Matrix.det_mul, Matrix.det_mul, mul_comm ((b⁻¹).1.det * X.det), ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]`. Set `N' : Matrix (Fin n) (Fin n) (intLoc F E v)` to `fun i j => ⟨N i j, hent i j⟩`.

Establish `hmap : N'.map (intLoc F E v).subtype = N` using `by ext i j; rfl`. Establish `hd` using `RingHom.map_det (intLoc F E v).subtype N'`. Rewrite using `[← hdet, ← hmap, ← RingHom.mapMatrix_apply, ← hd]`. Conclude with `(N'.det).2`.
-/
theorem det_mem_intLoc_of_mapsTo {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hX : ∀ x ∈ latLoc F L v, X *ᵥ x ∈ latLoc F L v) : X.det ∈ intLoc F E v := by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  set b := Formalism.UG.bc (compFin F E v) a with hb
  set N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (b⁻¹).1 * X * b.1 with hN
  have hent : ∀ i j, N i j ∈ intLoc F E v := by
    intro i j
    have h1 : b.1 *ᵥ (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v :=
      (ha v (Pi.single j 1)).1 fun l => by
        by_cases e : l = j
        · subst e; simp
        · simp [e]
    have h2 := hX _ h1
    have hbN : b.1 * N = X * b.1 := by
      rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h3 : b.1 *ᵥ (N *ᵥ Pi.single j 1) ∈ latLoc F L v := by
      rwa [Matrix.mulVec_mulVec, hbN, ← Matrix.mulVec_mulVec]
    have h4 := (ha v _).2 h3 i
    simpa using h4
  have hdet : N.det = X.det := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, mul_comm ((b⁻¹).1.det * X.det), ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  let N' : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i j => ⟨N i j, hent i j⟩
  have hmap : N'.map (intLoc F E v).subtype = N := by ext i j; rfl
  have hd := RingHom.map_det (intLoc F E v).subtype N'
  rw [← hdet, ← hmap, ← RingHom.mapMatrix_apply, ← hd]
  exact (N'.det).2

/- English proof (translation)
Establish `hk : KeepsDiag finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1` using `(mem_siegelOf (e := finSumFinEquiv) (mat := GlobalTheory.AdelicU.matHom (Fv F v) σ Q)).1 p.2`. Use `det_mem_intLoc_of_mapsTo L v (leviMat finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1) fun x hx => ?_` and prove the remaining obligations. Establish `h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v`. Rewrite using `[latLoc_sumLat]`. Conclude with `(pairVec_mem_sumLat _).2 ⟨hx, hx⟩`.

Establish `h2` using `(mem_stabLoc.1 hp _).1 h1`. Rewrite `h2` using `[hk.mulVec_diag, latLoc_sumLat, pairVec_mem_sumLat]`. Conclude with `h2.1`.
-/
theorem aH_mem_intLoc_of_lattice (σ : E →ₐ[F] E) {n : ℕ} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (p : siegelH (Fv F v) σ Q) (hp : (p : GLoc σ Q v) ∈ GlobalTheory.Doubling.KFin σ Q L v) :
    ((aH _ σ Q p : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  have hk : KeepsDiag finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := GlobalTheory.AdelicU.matHom (Fv F v) σ Q)).1 p.2
  refine det_mem_intLoc_of_mapsTo L v (leviMat finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1) fun x hx => ?_
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hp _).1 h1
  rw [hk.mulVec_diag, latLoc_sumLat, pairVec_mem_sumLat] at h2
  exact h2.1

/- English proof (translation)
Introduce `D A L hL v p hp`. Use `haveI := hL.1`. Conclude with `aH_mem_intLoc_of_lattice D.sp.cm.sig (n := A.rank) (dblSp A).gram L v p hp`.
-/
theorem aH_mem_intLoc : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  intro D A L hL v p hp
  haveI := hL.1
  exact aH_mem_intLoc_of_lattice D.sp.cm.sig (n := A.rank) (dblSp A).gram L v p hp

end GlobalTheory.Core.Rk.AInt
