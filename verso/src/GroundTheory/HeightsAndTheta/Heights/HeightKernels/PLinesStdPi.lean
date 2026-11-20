import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesStdPi

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, Pi.single_apply, Algebra.smul_def, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem eq_sum_smul_single {K : Type*} [Field K] {k : ℕ} (y : Fin k → 𝓞 K) :
    (fun i => algebraMap (𝓞 K) K (y i)) = ∑ j, y j • (Pi.single j 1 : Fin k → K) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, Algebra.smul_def, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end KLinesStdPi

/- English proof (translation)
Introduce `K _ k`. Use extensionality with `v`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Introduce `i`. Simplify using `only`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => intro i`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => intro i`. Conclude with `Submodule.add_mem _ (hx i) (hy i)`. Consider the case `smul a x _ hx => intro i`. Conclude with `Submodule.smul_mem _ a (hx i)`.

Introduce `hv choose y hy using fun i => Submodule.mem_one.mp (hv i)`. Establish `hv' : v = fun i => algebraMap (𝓞 K) K (y i)` using `funext fun i => (hy i).symm`. Rewrite using `[hv', KLinesStdPi.eq_sum_smul_single]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem LinesStdPi.proof : LinesStdPi.Statement := by
  intro K _ k
  ext v
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      dsimp only
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro i; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro i; exact Submodule.add_mem _ (hx i) (hy i)
    | smul a x _ hx => intro i; exact Submodule.smul_mem _ a (hx i)
  · intro hv
    choose y hy using fun i => Submodule.mem_one.mp (hv i)
    have hv' : v = fun i => algebraMap (𝓞 K) K (y i) := funext fun i => (hy i).symm
    rw [hv', KLinesStdPi.eq_sum_smul_single]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GroundTheory.Heights₂.Heights
