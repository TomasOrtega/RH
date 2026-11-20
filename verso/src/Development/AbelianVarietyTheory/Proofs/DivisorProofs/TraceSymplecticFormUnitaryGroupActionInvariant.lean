import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen.SympAct

/- English proof (translation)
Unfold `hTens`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq_mat {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Establish `hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB` using `g.2`. Establish `key : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ`. Unfold `actB`. Rewrite using `[show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E).map c)ᵀ by`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply, map_sum, map_mul]]`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_transpose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hg]`.

Unfold `symp`. Rewrite using `[hTens_eq_mat, hTens_eq_mat, key]`.
-/
theorem symp_actB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E) : symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  have key : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB
    rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E).map c)ᵀ by
      ext i j; simp [Matrix.mul_apply, map_sum, map_mul]]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc x * ((g : GL β E) : Matrix β β E)ᵀ * JB * (((g : GL β E) : Matrix β β E).map c * (y.map c)ᵀ)
        = x * (((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c) * (y.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_mat, hTens_eq_mat, key]

end GlobalTheory.DblVacEigen.SympAct
