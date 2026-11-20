import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmTypeStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn

/- English proof (translation)
Introduce `D θ hθ m n z x₀`. Establish `hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w)` using `fun τ w => Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)`. Set `C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ` to `fun τ => (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix`. Establish `hC : ∀ τ w, compAt θ τ w = C τ w` using `fun τ w => rfl`. Set `P : Mx D m n →+ Matrix (Fin m) (Fin n) _` to `((finPart D).toAddMonoidHom).mapMatrix`.

Establish `hP : ∀ w : Mx D m n, w.map (finPart D) = P w` using `fun w => rfl`. Establish `key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y`. Introduce `x y h1 h2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `(GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_` and prove the remaining obligations. Use `congrFun (congrFun (h1 τ) i) j` as an intermediate fact. Simplify using `only [compAt, Matrix.map_apply] at this`. Rewrite using `[(infPart D).map_sub, (θ τ).map_sub, this, sub_self]`. Use `congrFun (congrFun h2 i) j` as an intermediate fact.

Simplify using `only [Matrix.map_apply] at this`. Rewrite using `[(finPart D).map_sub, this, sub_self]`. Use `⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hC, map_add, map_sum, ← hC]`. Repeatedly rewrite using `[← hC, (hL _ _).2.2 1 τ]`.

Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hP, hP, map_add, map_sum]`. Repeatedly rewrite using `[← hP, (hL _ _).2.1 1]`. Simplify using the standard rewrite rules.

Introduce and unpack `y ⟨hy1, hy2⟩`. Apply `key` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[hy1, hC, map_add, map_sum, ← hC]`. Repeatedly rewrite using `[← hC, (hL _ _).2.2 1 τ]`.

Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hy2, hP, hP, map_add, map_sum]`. Repeatedly rewrite using `[← hP, (hL _ _).2.1 1]`. Simplify using the standard rewrite rules.
-/
theorem exists_unique_of_comp_finPart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  intro D θ hθ m n z x₀
  have hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w) := fun τ w =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)
  let C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ := fun τ =>
    (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix
  have hC : ∀ τ w, compAt θ τ w = C τ w := fun τ w => rfl
  let P : Mx D m n →+ Matrix (Fin m) (Fin n) _ := ((finPart D).toAddMonoidHom).mapMatrix
  have hP : ∀ w : Mx D m n, w.map (finPart D) = P w := fun w => rfl
  have key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y := by
    intro x y h1 h2
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    refine (GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_
    · have := congrFun (congrFun (h1 τ) i) j
      simp only [compAt, Matrix.map_apply] at this
      rw [(infPart D).map_sub, (θ τ).map_sub, this, sub_self]
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at this
      rw [(finPart D).map_sub, this, sub_self]
  refine ⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩
  · rw [hC, map_add, map_sum, ← hC]
    simp_rw [← hC, (hL _ _).2.2 1 τ]
    rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
    abel
  · rw [hP, hP, map_add, map_sum]
    simp_rw [← hP, (hL _ _).2.1 1]
    simp
  · rintro y ⟨hy1, hy2⟩
    apply key
    · intro τ
      rw [hy1, hC, map_add, map_sum, ← hC]
      simp_rw [← hC, (hL _ _).2.2 1 τ]
      rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
      abel
    · rw [hy2, hP, hP, map_add, map_sum]
      simp_rw [← hP, (hL _ _).2.1 1]
      simp

end GlobalTheory.StdUnn
