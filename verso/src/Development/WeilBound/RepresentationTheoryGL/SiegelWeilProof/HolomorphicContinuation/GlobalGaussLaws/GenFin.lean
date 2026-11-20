import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinH

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (blkDm M).map f = blkDm (M.map f) := by
  ext i j; rfl

/- English proof (translation)
Unfold `blkDm`. Rewrite using `[Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]`.
-/
theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  unfold blkDm
  rw [Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

end PositivityTheory.Rg.Sw.Glob.GenFinH

namespace PositivityTheory.Rg.Sw.Glob

open GenFinH

/- English proof (translation)
Introduce `D n k hk hreal`. Use `choose a I hgood using fun v => hL D n k hk v`. Take `⟨m, hm, hmv, hmr⟩` from `hGL D n a (fun v => (hgood v).1) (fun v => (hgood v).2.1)`. Take `⟨w, hw, hwv, hwr⟩` from `hGW D n I`. Establish `hmat : ∀ {S : Type} [CommRing S] (f : AE D →+* S), (mat (k * m * w)).map f = (mat k).map f * (mat m).map f * (mat w).map f`.

Introduce `S _ f`. Use `show (mat k * mat m * mat w).map f = _`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Establish `hd : IsUnit (blkDm (mat (k * m * w))).det`. Apply `hUA D` to reduce the goal to its premises.

Introduce `τ`. Rewrite using `[det_map, blkDm_map, hmat, hreal τ, hmr τ, hwr τ, Matrix.mul_one, Matrix.mul_one, blkDm_one, Matrix.det_one]`. Conclude with `one_ne_zero`. Introduce `v`. Rewrite using `[det_map, blkDm_map, hmat, hmv v, hwv v]`.

Conclude with `(hgood v).2.2`. Establish `h1 : k * m * w ∈ Subgroup.closure (genSet D n)` using `hU D n _ hd`. Establish `hm' : m ∈ Subgroup.closure (genSet D n)` using `Subgroup.subset_closure hm`. Establish `e : k = k * m * w * w⁻¹ * m⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hm')`.
-/
theorem kInFin_of (hU : UnitD) (hL : LocFin) (hGL : GlueLevi) (hGW : GlueW) (hUA : UnitAE) : KInFin := by
  intro D n k hk hreal
  choose a I hgood using fun v => hL D n k hk v
  obtain ⟨m, hm, hmv, hmr⟩ := hGL D n a (fun v => (hgood v).1) (fun v => (hgood v).2.1)
  obtain ⟨w, hw, hwv, hwr⟩ := hGW D n I
  have hmat : ∀ {S : Type} [CommRing S] (f : AE D →+* S), (mat (k * m * w)).map f = (mat k).map f * (mat m).map f * (mat w).map f := by
    intro S _ f
    show (mat k * mat m * mat w).map f = _
    rw [Matrix.map_mul, Matrix.map_mul]
  have hd : IsUnit (blkDm (mat (k * m * w))).det := by
    apply hUA D
    · intro τ
      rw [det_map, blkDm_map, hmat, hreal τ, hmr τ, hwr τ, Matrix.mul_one, Matrix.mul_one, blkDm_one, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [det_map, blkDm_map, hmat, hmv v, hwv v]
      exact (hgood v).2.2
  have h1 : k * m * w ∈ Subgroup.closure (genSet D n) := hU D n _ hd
  have hm' : m ∈ Subgroup.closure (genSet D n) := Subgroup.subset_closure hm
  have e : k = k * m * w * w⁻¹ * m⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hm')

end PositivityTheory.Rg.Sw.Glob
