import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RealParamSize

variable {D : D7} {m n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [compAt, Matrix.map_apply, Matrix.add_apply]`. Rewrite using `[(infPart D).map_add, (θ τ).map_add]`.
-/
theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [(infPart D).map_add, (θ τ).map_add]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [compAt, Matrix.map_apply, Matrix.neg_apply]`. Rewrite using `[(infPart D).map_neg, (θ τ).map_neg]`.
-/
theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) :
    compAt θ τ (-x) = -compAt θ τ x := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.neg_apply]
  rw [(infPart D).map_neg, (θ τ).map_neg]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) :
    (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

/- English proof (translation)
Unfold `GlobalTheory.Unf.realSize`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun τ => (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun i => (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j`.
-/
theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

/- English proof (translation)
Use `set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv`. Unfold `GlobalTheory.Unf.realSize`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

/- English proof (translation)
Unfold `GlobalTheory.Unf.realSize`. Simplify using `only [compAt_add, Matrix.add_apply, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _`.
-/
theorem realSize_add_le (θ : InfFam D) (x y : Mx D m n) :
    GlobalTheory.Unf.realSize θ (x + y) ≤ GlobalTheory.Unf.realSize θ x + GlobalTheory.Unf.realSize θ y := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_add, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _

/- English proof (translation)
Unfold `GlobalTheory.Unf.realSize`. Simplify using `only [compAt_neg, Matrix.neg_apply, norm_neg]`.
-/
theorem realSize_neg (θ : InfFam D) (x : Mx D m n) : GlobalTheory.Unf.realSize θ (-x) = GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_neg, Matrix.neg_apply, norm_neg]

/- English proof (translation)
The claim follows from `continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp ((continuous_apply i).comp hL))`.
-/
theorem continuous_realVec {θ : InfFam D} (hθ : IsInfFam θ) {k : ℕ} {L : (Fin k → ℝ) →+ Mx D m n}
    (hL : Continuous L) : Continuous (realVec θ L) :=
  continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp ((continuous_apply i).comp hL))

end GlobalTheory.RealParamSize

open GlobalTheory.RealParamSize in

/- English proof (translation)
Introduce `D θ hθ m n k L hL`. Establish `hc` using `continuous_realVec hθ hL.1`. Use `set A := (realVec θ L).toRealLinearMap hc with hA`. Establish `hAt : ∀ t, A t = realVec θ L t` using `fun t => rfl`. Establish `hvec : ∀ t, realVec θ L t = (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ)` using `fun t => rfl`.

Use `⟨⟨(Fintype.card D.what₂.Tau * (m * n) : ℝ) * ‖A‖, fun t => ?_⟩, fun hinj => ?_⟩` and prove the remaining obligations. Use `(realSize_le θ (L t)).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc _ ‖A‖, ← hvec, ← hAt]`. Conclude with `mul_le_mul_of_nonneg_left (A.le_opNorm t) (by positivity)`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`.

Establish `hker : (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `t ht`. Establish `h0 : realVec θ L t = 0` using `by rw [← hAt]; exact ht`. Establish `hLt : L t = 0`.

Use extensionality with `i j`. Use `hσ.ext _ ?_ fun τ => ?_` and prove the remaining obligations. Establish `h` using `congrFun (congrFun (hL.2 t) i) j`. Simplify `h` using `only [Matrix.map_apply, Matrix.zero_apply]`. Establish `h` using `congrFun (congrFun (congrFun h0 τ) i) j`.

Conclude with `h`. Conclude with `hinj (hLt.trans L.map_zero.symm)`. Take `⟨K, -, hK⟩` from `(A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker`. Use `⟨K, fun x t => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖t‖ ≤ K * ‖A t‖`.

Use `hK.le_mul_dist t 0` as an intermediate fact. Simplify `this` using `[dist_eq_norm]`. Establish `h2 : ‖A t‖ ≤ GlobalTheory.Unf.realSize θ (L t)` using `by rw [hAt, hvec]; exact norm_vec_le θ (L t)`. Establish `h3 : GlobalTheory.Unf.realSize θ (L t) ≤ GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x`. Use `realSize_add_le θ (x + L t) (-x)` as an intermediate fact.

Rewrite `this` using `[realSize_neg, add_neg_cancel_comm]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.Unf.realParam_size_bounds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L → (∃ C : ℝ, ∀ t, GlobalTheory.Unf.realSize θ (L t) ≤ C * ‖t‖) ∧ (Function.Injective L → ∃ C : ℝ, ∀ (x : Mx D m n) t, ‖t‖ ≤ C * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x)) := by
  intro D θ hθ m n k L hL
  have hc := continuous_realVec hθ hL.1
  set A := (realVec θ L).toRealLinearMap hc with hA
  have hAt : ∀ t, A t = realVec θ L t := fun t => rfl
  have hvec : ∀ t, realVec θ L t = (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    fun t => rfl
  refine ⟨⟨(Fintype.card D.what₂.Tau * (m * n) : ℝ) * ‖A‖, fun t => ?_⟩, fun hinj => ?_⟩
  · refine (realSize_le θ (L t)).trans ?_
    rw [mul_assoc _ ‖A‖, ← hvec, ← hAt]
    exact mul_le_mul_of_nonneg_left (A.le_opNorm t) (by positivity)
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    have hker : (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAt]; exact ht
      have hLt : L t = 0 := by
        ext i j
        refine hσ.ext _ ?_ fun τ => ?_
        · have h := congrFun (congrFun (hL.2 t) i) j
          simpa only [Matrix.map_apply, Matrix.zero_apply] using h
        · have h := congrFun (congrFun (congrFun h0 τ) i) j
          exact h
      exact hinj (hLt.trans L.map_zero.symm)
    obtain ⟨K, -, hK⟩ := (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    refine ⟨K, fun x t => ?_⟩
    have h1 : ‖t‖ ≤ K * ‖A t‖ := by
      have := hK.le_mul_dist t 0
      simpa [dist_eq_norm] using this
    have h2 : ‖A t‖ ≤ GlobalTheory.Unf.realSize θ (L t) := by rw [hAt, hvec]; exact norm_vec_le θ (L t)
    have h3 : GlobalTheory.Unf.realSize θ (L t) ≤ GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x := by
      have := realSize_add_le θ (x + L t) (-x)
      rwa [realSize_neg, add_neg_cancel_comm] at this
    calc ‖t‖ ≤ K * ‖A t‖ := h1
      _ ≤ K * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) K.coe_nonneg

end
