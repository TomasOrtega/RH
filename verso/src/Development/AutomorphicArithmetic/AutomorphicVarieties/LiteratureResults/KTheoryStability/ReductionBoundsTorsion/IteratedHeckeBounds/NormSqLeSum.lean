import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.JoinReconstruction

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sx (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

def pt {q : ℕ} (y : Fin (q + 1) → V) (t : Fin q → ℝ) : V := y 0 + ∑ j, t j • (y j.succ - y 0)

/- English proof (translation)
Set `L : (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ((ι → κ) → ℝ)` to `{ toFun := fun A v => A fun i => b (v i) map_add' := fun A B => by`. Use extensionality with `v`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun c A => by`. Use extensionality with `v`.

Simplify using `}`. Establish `hL : LinearMap.ker L = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `A hA`. Establish `hm : A.toMultilinearMap = (0 : V [⋀^ι]→L[ℝ] ℝ).toMultilinearMap`.

Use `Module.Basis.ext_multilinear (fun _ => b) fun v => ?_` and prove the remaining obligations. Use `congrFun hA v` as an intermediate fact. Simplify `this` using `[L]`. Use extensionality with `x`. Simplify using `using congrFun (congrArg DFunLike.coe hm) x`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective L hL`. Use `⟨LinearMap.toContinuousLinearMap g, fun A => ?_⟩` and prove the remaining obligations. Use `congrArg (fun f => f A) hg` as an intermediate fact. Simplify `this` using `[L]`.
-/
theorem recon [FiniteDimensional ℝ V] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Module.Basis κ ℝ V) :
    ∃ Ψ : ((ι → κ) → ℝ) →L[ℝ] (V [⋀^ι]→L[ℝ] ℝ), ∀ A : V [⋀^ι]→L[ℝ] ℝ, Ψ (fun v => A fun i => b (v i)) = A := by
  let L : (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ((ι → κ) → ℝ) :=
    { toFun := fun A v => A fun i => b (v i)
      map_add' := fun A B => by
        ext v
        simp
      map_smul' := fun c A => by
        ext v
        simp }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have hm : A.toMultilinearMap = (0 : V [⋀^ι]→L[ℝ] ℝ).toMultilinearMap := by
      refine Module.Basis.ext_multilinear (fun _ => b) fun v => ?_
      have := congrFun hA v
      simpa [L] using this
    ext x
    simpa using congrFun (congrArg DFunLike.coe hm) x
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨LinearMap.toContinuousLinearMap g, fun A => ?_⟩
  have := congrArg (fun f => f A) hg
  simpa [L] using this

/- English proof (translation)
Establish `hs : 0 ≤ ∑ v, u v ^ 2` using `Finset.sum_nonneg fun v _ => sq_nonneg _`. Establish `h : ‖u‖ ≤ Real.sqrt (∑ v, u v ^ 2)`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]`. Conclude with `Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => u w ^ 2) (fun w _ => sq_nonneg (u w)) (Finset.mem_univ v))`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sq_le_sum {κ : Type} [Fintype κ] (u : κ → ℝ) : ‖u‖ ^ 2 ≤ ∑ v, u v ^ 2 := by
  have hs : 0 ≤ ∑ v, u v ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have h : ‖u‖ ≤ Real.sqrt (∑ v, u v ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => u w ^ 2) (fun w _ => sq_nonneg (u w)) (Finset.mem_univ v))
  calc ‖u‖ ^ 2 ≤ Real.sqrt (∑ v, u v ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ v, u v ^ 2 := Real.sq_sqrt hs

end PositivityTheory.KB.JoinReconstruction

end
