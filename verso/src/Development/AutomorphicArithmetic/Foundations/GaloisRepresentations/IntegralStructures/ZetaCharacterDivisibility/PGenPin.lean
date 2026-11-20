import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharAnn

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Simplify using `only [aeval_def, eval₂_map]`. Establish `h` using `hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M`. Rewrite `h` using `[RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]`. Rewrite using `[h]`. Use `congr 1`.

Use extensionality with `a : 1`. Simplify using `[Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]`.
-/
private theorem aeval_matrix_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval (M.map f) (Q.map f) = (aeval M Q).map f := by
  simp only [aeval_def, eval₂_map]
  have h := hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext a : 1
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]

/- English proof (translation)
Introduce `l _ ι a M s hcard hgen hann hdet`. Use `set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef`. Establish `hround : map ι.toRingHom (map ι.symm.toRingHom P) = P`. Rewrite using `[Polynomial.map_map]`. Use `Polynomial.map_id` and compare the differences between its conclusion and the goal.

Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0` using `by show aeval (M.map ι.toRingHom) P = 0`. Rewrite using `[← hround, aeval_matrix_map, hann]`. Simplify using the standard rewrite rules.

Establish `hdet2 : (M.map ι.toRingHom).det = s.prod`. Establish `hd` using `RingHom.map_det ι.toRingHom M`. Rewrite `hd` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← hd]`. Conclude with `hdet`.

Rewrite using `[← Matrix.charpoly_map]`. Conclude with `UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2`.
-/
theorem UpperTheory.Gal.Int.Div.genPin_of :
    GenPin := by
  intro l _ ι a M s hcard hgen hann hdet
  set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef
  have hround : map ι.toRingHom (map ι.symm.toRingHom P) = P := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext z
    simp
  have hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0 := by
    show aeval (M.map ι.toRingHom) P = 0
    rw [← hround, aeval_matrix_map, hann]
    simp
  have hdet2 : (M.map ι.toRingHom).det = s.prod := by
    have hd := RingHom.map_det ι.toRingHom M
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hd]
    exact hdet
  rw [← Matrix.charpoly_map]
  exact UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2
