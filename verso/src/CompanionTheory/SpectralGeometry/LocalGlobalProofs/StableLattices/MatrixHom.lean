import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckMatHom

/- English proof (translation)
Simplify using `[mAct, LinearMap.sum_apply]`.
-/
theorem mAct_coord {ι ι' V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct, LinearMap.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [mAct_coord, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem mAct_mAct {ι ι' ι'' V : Type} [Fintype ι] [Fintype ι'] [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) (x : ι → V) :
    mAct A (mAct B x) = mAct (A * B) x := by
  funext c
  simp only [mAct_coord, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `h : ∀ (κ : Type) (y : κ → V) (e : κ), dOp κ T y e = T (y e)` using `fun _ _ _ => rfl`. Simplify using `only [h, mAct_coord, map_sum, map_smul]`.
-/
theorem dOp_mAct {ι ι' V V' : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (A : Matrix ι' ι ℂ) (T : V →ₗ[ℂ] V') (x : ι → V) :
    dOp ι' T (mAct A x) = mAct A (dOp ι T x) := by
  funext c
  have h : ∀ (κ : Type) (y : κ → V) (e : κ), dOp κ T y e = T (y e) := fun _ _ _ => rfl
  simp only [h, mAct_coord, map_sum, map_smul]

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | X :: W, hW, v => by have ih := dsigW_eq_prod U W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) v rw [List.map_cons, List.prod_cons, Module.End.mul_apply, URep.dsig_coe U (hW X List.mem_cons_self), ← ih] rfl`.
-/
theorem dsigW_eq_prod {k r : ℕ} (U : URep k r) :
    ∀ (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)), LieWd k r W → ∀ v : U.R.smSub,
      PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W (v : U.R.H) = ((W.map U.dsig).prod v : U.R.H)
  | [], _, _ => rfl
  | X :: W, hW, v => by
    have ih := dsigW_eq_prod U W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) v
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      URep.dsig_coe U (hW X List.mem_cons_self), ← ih]
    rfl

/- English proof (translation)
Introduce `k r F F' U A hA`. Use `⟨fun W hW => ⟨∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖, [W], ?_, fun x => ?_⟩, fun g hg => ?_⟩` and prove the remaining obligations. Introduce `W' hW'`. Rewrite using `[List.mem_singleton.1 hW']`. Conclude with `hW`.

Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]`. Express the relevant statement in the definitionally equal form `∑ c : F'.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((mAct A x c : U.R.smSub) : U.R.H)‖ ≤ (∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖) * ∑ e : F.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((x e : U.R.smSub) : U.R.H)‖`. Simplify using `only [dsigW_eq_prod U W hW]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[mAct_coord, map_sum, Submodule.coe_sum, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Submodule.coe_smul, norm_smul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun e => ‖(((W.map U.dsig).prod (x e) : U.R.smSub) : U.R.H)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ d)`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mAct A (mAct (F.ρ g) (dOp F.ι (U.sig g) x)) = mAct (F'.ρ g) (dOp F'.ι (U.sig g) (mAct A x))`. Rewrite using `[dOp_mAct, mAct_mAct, mAct_mAct, hA g hg]`.
-/
theorem matHom : MatHom := by
  intro k r F F' U A hA
  refine ⟨fun W hW => ⟨∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖, [W], ?_, fun x => ?_⟩, fun g hg => ?_⟩
  · intro W' hW'
    rw [List.mem_singleton.1 hW']
    exact hW
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change ∑ c : F'.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((mAct A x c : U.R.smSub) : U.R.H)‖ ≤
      (∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖) *
        ∑ e : F.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((x e : U.R.smSub) : U.R.H)‖
    simp only [dsigW_eq_prod U W hW]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [mAct_coord, map_sum, Submodule.coe_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [map_smul, Submodule.coe_smul, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Finset.single_le_sum
      (f := fun e => ‖(((W.map U.dsig).prod (x e) : U.R.smSub) : U.R.H)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
  · refine LinearMap.ext fun x => ?_
    change mAct A (mAct (F.ρ g) (dOp F.ι (U.sig g) x)) = mAct (F'.ρ g) (dOp F'.ι (U.sig g) (mAct A x))
    rw [dOp_mAct, mAct_mAct, mAct_mAct, hA g hg]

end GlobalTheory.CompanionTheory.ZuckMatHom

end
