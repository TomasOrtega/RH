import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

/- English proof (translation)
Simplify using `only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem block_matrix_mul_comm_ring {R : Type} [Ring R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
theorem block_matrix_diagonal_one_eq_one {R : Type} [Ring R] {n : ℕ} : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 1 0 0 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Unfold `blk4`. Rewrite using `[← Matrix.fromBlocks_map]`. Both sides reduce to the same expression.
-/
theorem block_matrix_map {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(f.mapMatrix) (-1) = -1`. Rewrite using `[map_neg, map_one]`.
-/
theorem map_neg_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
  change (f.mapMatrix) (-1) = -1
  rw [map_neg, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(f.mapMatrix) 1 = 1`. Rewrite using `[map_one]`.
-/
theorem map_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (1 : Matrix (Fin n) (Fin n) R).map f = 1 := by
  change (f.mapMatrix) 1 = 1
  rw [map_one]

/- English proof (translation)
Simplify using `only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]`.
-/
theorem blockMatrixTwoByTwoFin_transpose {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

open LocCellA in

/- English proof (translation)
Introduce `D n`. Set `M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)` to `blk4 0 1 (-1) 0`. Set `Mi : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)` to `blk4 0 (-1) 1 0`. Establish `h1 : M * Mi = 1` using `by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]`. Establish `h2 : Mi * M = 1` using `by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]`.

Set `u : GL (Fin (n + n)) (AE D)` to `⟨M, Mi, h1, h2⟩`. Establish `hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n)` using `by show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)`. Establish `hJ : JR (AF D.host.F) (Jst D n) = M`. Simplify using `[JR, Jst, M, block_matrix_map, map_neg_one', map_one']`. Rewrite using `[hJ]`.

Simplify using `[Formalism.UG.cT, M, block_matrix_map, blockMatrixTwoByTwoFin_transpose, block_matrix_mul_comm_ring, map_neg_one', map_one']`. Conclude with `⟨⟨u, hu⟩, rfl⟩`.
-/
theorem wEx : WEx := by
  intro D n
  let M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 1 (-1) 0
  let Mi : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 (-1) 1 0
  have h1 : M * Mi = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  have h2 : Mi * M = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  let u : GL (Fin (n + n)) (AE D) := ⟨M, Mi, h1, h2⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    have hJ : JR (AF D.host.F) (Jst D n) = M := by
      simp [JR, Jst, M, block_matrix_map, map_neg_one', map_one']
    rw [hJ]
    simp [Formalism.UG.cT, M, block_matrix_map, blockMatrixTwoByTwoFin_transpose, block_matrix_mul_comm_ring, map_neg_one', map_one']
  exact ⟨⟨u, hu⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
