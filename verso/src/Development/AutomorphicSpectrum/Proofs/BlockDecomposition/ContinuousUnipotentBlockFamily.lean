import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

/- English proof (translation)
Unfold `blk4`. Conclude with `(continuous_const.matrix_fromBlocks hf continuous_const continuous_const).matrix_submatrix _ _`.
-/
theorem continuous_unipotent_block_family {X R : Type} [TopologicalSpace X] [TopologicalSpace R] [Zero R] [One R] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) :
    Continuous fun x => blk4 (1 : Matrix (Fin n) (Fin n) R) (f x) 0 1 := by
  unfold blk4
  exact (continuous_const.matrix_fromBlocks hf continuous_const continuous_const).matrix_submatrix _ _

/- English proof (translation)
Unfold `blk4`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Simplify using `[add_comm]`.
-/
theorem unipotent_block_mul_add {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) :
    blk4 (1 : Matrix (Fin n) (Fin n) R) b 0 1 * blk4 1 c 0 1 = blk4 1 (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

/- English proof (translation)
Establish `emb` using `isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)`. Rewrite using `[emb.continuous_iff, Units.continuous_iff]`. Establish `hv : Continuous fun b : hermA D p => (b.1 : Mx D p p)` using `continuous_subtype_val`. Establish `hm : ∀ b, (AdelicU.matHom _ D.sp.cm.sig (Jst D p) (nb b)).1 = blk4 1 b.1 0 1` using `hnb`. Prove the components needed by the constructor for the conclusion.

Use `(continuous_unipotent_block_family hv).congr fun b => ?_` and prove the remaining obligations. Conclude with `(hm b).symm`. Use `(continuous_unipotent_block_family hv.neg).congr fun b => ?_` and prove the remaining obligations. Use `symm`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations.

Simplify using `only [Function.comp]`. Rewrite using `[hm b, unipotent_block_mul_add]`. Simplify using `[blk4]`.
-/
theorem continuous_nb {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) : Continuous nb := by
  have emb := isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)
  rw [emb.continuous_iff, Units.continuous_iff]
  have hv : Continuous fun b : hermA D p => (b.1 : Mx D p p) := continuous_subtype_val
  have hm : ∀ b, (AdelicU.matHom _ D.sp.cm.sig (Jst D p) (nb b)).1 = blk4 1 b.1 0 1 := hnb
  constructor
  · refine (continuous_unipotent_block_family hv).congr fun b => ?_
    exact (hm b).symm
  · refine (continuous_unipotent_block_family hv.neg).congr fun b => ?_
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp only [Function.comp]
    rw [hm b, unipotent_block_mul_add]
    simp [blk4]

end GlobalTheory.CompanionTheory.MuC
