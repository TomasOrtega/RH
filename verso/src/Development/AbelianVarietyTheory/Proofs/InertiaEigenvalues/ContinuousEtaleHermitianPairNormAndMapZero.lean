import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `h2 : Module.finrank F E = 2` using `Unram.finrank_eq`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`. Establish `hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap` using `A.push.symm.out`. Set `b0` to `Module.finBasisOfFinrankEq F E h2`. Set `b : Module.Basis (Fin 2) A.K A.L` to `hb.basis b0`.

Establish `hN : ∀ y, A.NL y = (Algebra.leftMulMatrix b y).det` using `fun y => Algebra.norm_eq_matrix_det b y`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: A.NL = fun y => (Algebra.leftMulMatrix b y).det` using `funext hN`. Rewrite using `[this]`. Use `Continuous.matrix_det ?_` and prove the remaining obligations.

Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Set `f : A.L →ₗ[F] A.K` to `((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F`. Establish `hf : Continuous f` using `IsModuleTopology.continuous_of_linearMap f`. Use `hf.congr fun y => ?_` and prove the remaining obligations. Simplify using `[f, Algebra.leftMulMatrix_eq_repr_mul]`.

Rewrite using `[hN, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem etale_norm_continuous_and_zero (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := by
  classical
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  let b0 := Module.finBasisOfFinrankEq F E h2
  let b : Module.Basis (Fin 2) A.K A.L := hb.basis b0
  have hN : ∀ y, A.NL y = (Algebra.leftMulMatrix b y).det := fun y => Algebra.norm_eq_matrix_det b y
  refine ⟨?_, ?_⟩
  · have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := funext hN
    rw [this]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    let f : A.L →ₗ[F] A.K := ((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine hf.congr fun y => ?_
    simp [f, Algebra.leftMulMatrix_eq_repr_mul]
  · rw [hN, map_zero]
    simp

end GlobalTheory
