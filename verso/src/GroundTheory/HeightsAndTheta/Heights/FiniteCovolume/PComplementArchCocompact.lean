import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementArchCocompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsZsmulMem

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace ComplementArchCocompact

section Lattice

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem hL x`.
-/
theorem exists_zsmul_mem {La : AddSubgroup W} (hL : IsLattice E La) (x : W) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem hL x

end Lattice

end ComplementArchCocompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ComplementArchCocompact

def formAt (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) (u : ι → ℂ) :
    (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := star u ⬝ᵥ (gramAt h v w *ᵥ z)
  map_add' x y := by simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [Matrix.mulVec_smul, dotProduct_smul]

def projAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] (InfinitePlace E → ι → ℂ) :=
  LinearMap.pi fun w => (LinearMap.id - (formAt h v w (vecAt v w₀ w)).smulRight (vecAt v x₀ w) -
    (formAt h v w (vecAt v x₀ w)).smulRight (vecAt v w₀ w)) ∘ₗ LinearMap.proj w

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projAt_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (Y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    projAt h v x₀ w₀ Y w = Y w - (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v x₀ w -
      (star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v w₀ w := rfl

omit [NumberField E] [IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecAt]`.
-/
theorem vecAt_smul_apply (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Rewrite using `[projAt_apply, ← HermAtPlace.proof h v w w₀, ← HermAtPlace.proof h v w x₀, ComplementExtension.proj_apply]`. Simplify using `only [← vecAtHom_apply, map_sub, Pi.sub_apply]`. Simplify using `only [vecAtHom_apply, vecAt_smul_apply]`.
-/
theorem projAt_vecAt (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (e : W) :
    projAt h v x₀ w₀ (vecAt v e) = vecAt v (ComplementExtension.proj hp e : W) := by
  funext w
  rw [projAt_apply, ← HermAtPlace.proof h v w w₀, ← HermAtPlace.proof h v w x₀,
    ComplementExtension.proj_apply]
  simp only [← vecAtHom_apply, map_sub, Pi.sub_apply]
  simp only [vecAtHom_apply, vecAt_smul_apply]

end ComplementArchCocompact

open ComplementArchCocompact in

/- English proof (translation)
Introduce `La x₀ w₀ m hLa hp hm`. Take `⟨hli, hdim⟩` from `CoordEmbedBasis.proof E ι`. Set `b₀` to `Pi.basis fun _ : ι => integralBasis E`. Set `Bs` to `basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hdim, finrank_eq_card_basis b₀])`. Set `e : _ → W` to `fun k => v.equivFun.symm (b₀ k)`.

Establish `hBe : ∀ k, Bs k = vecAt v (e k)`. Introduce `k`. Rewrite using `[coe_basisOfLinearIndependentOfCardEqFinrank']`. Use function extensionality and compare the values at `w i`. Rewrite using `[vecAt, coordEmbed_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.

Set `p : _ → W` to `fun k => (ComplementExtension.proj hp (e k) : W)`. Use `choose d hd hdL using fun k => exists_zsmul_mem hLa (p k)`. Set `f : _ → W` to `fun k => m • d k • p k`. Set `D : _ → ℝ` to `fun k => (m : ℝ) * d k`. Establish `hD : ∀ k, D k ≠ 0` using `fun k => mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hd k)`.

Establish `hf : ∀ k, vecAt v (f k) = D k • vecAt v (p k)`. Introduce `k`. Simplify using `only [f, D, ← vecAtHom_apply, map_nsmul, map_zsmul]`. Rewrite using `[mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]`. Use `⟨(fun t : _ → ℝ => ∑ k, t k • vecAt v (f k)) '' Set.Icc 0 1, isCompact_Icc.image (continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const), fun Y hY => ?_⟩` and prove the remaining obligations.

Establish `hPY : projAt h v x₀ w₀ Y = Y`. Use function extensionality and compare the values at `w`. Rewrite using `[projAt_apply, (hY w).1, (hY w).2, zero_smul, zero_smul, sub_zero, sub_zero]`. Use `set s : _ → ℝ := fun k => Bs.repr Y k * (D k)⁻¹ with hs`. Establish `hYs : Y = ∑ k, s k • vecAt v (f k)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Bs.sum_repr]`. Conclude with `hPY.symm`. Use `_ = ∑ k, Bs.repr Y k • vecAt v (p k) := by`. Simplify using `only [map_sum, map_smul, LinearMap.restrictScalars_apply, hBe]`.

Conclude with `Finset.sum_congr rfl fun k _ => by rw [projAt_vecAt]`. Use `_ = _ := Finset.sum_congr rfl fun k _ => by`. Rewrite using `[hf, smul_smul, hs, mul_assoc, inv_mul_cancel₀ (hD k), mul_one]`. Use `⟨∑ k, ⌊s k⌋ • f k, ?_, ⟨∑ k, ⌊s k⌋ • d k • p k, ?_, ?_⟩, ⟨fun k => Int.fract (s k), ⟨fun k => Int.fract_nonneg _, fun k => (Int.fract_lt_one _).le⟩, ?_⟩⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun k _ => zsmul_mem (nsmul_mem (zsmul_mem (ComplementExtension.proj hp (e k)).2 _) _) _`.

Conclude with `La.sum_mem fun k _ => La.zsmul_mem (hdL k) _`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => smul_comm _ _ _`. Use `show ∑ k, Int.fract (s k) • vecAt v (f k) = Y - vecAt v (∑ k, ⌊s k⌋ • f k) conv_rhs => rw [hYs]`. Rewrite using `[← vecAtHom_apply, map_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, vecAtHom_apply, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, Int.self_sub_floor]`.
-/
theorem ComplementArchCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ComplementArchCocompact.Statement h v := by
  classical
  intro La x₀ w₀ m hLa hp hm
  obtain ⟨hli, hdim⟩ := CoordEmbedBasis.proof E ι
  let b₀ := Pi.basis fun _ : ι => integralBasis E
  let Bs := basisOfLinearIndependentOfCardEqFinrank' _ hli
    (by rw [hdim, finrank_eq_card_basis b₀])
  let e : _ → W := fun k => v.equivFun.symm (b₀ k)
  have hBe : ∀ k, Bs k = vecAt v (e k) := by
    intro k
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    funext w i
    rw [vecAt, coordEmbed_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let p : _ → W := fun k => (ComplementExtension.proj hp (e k) : W)
  choose d hd hdL using fun k => exists_zsmul_mem hLa (p k)
  let f : _ → W := fun k => m • d k • p k
  let D : _ → ℝ := fun k => (m : ℝ) * d k
  have hD : ∀ k, D k ≠ 0 := fun k =>
    mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hd k)
  have hf : ∀ k, vecAt v (f k) = D k • vecAt v (p k) := by
    intro k
    simp only [f, D, ← vecAtHom_apply, map_nsmul, map_zsmul]
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
  refine ⟨(fun t : _ → ℝ => ∑ k, t k • vecAt v (f k)) '' Set.Icc 0 1,
    isCompact_Icc.image (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).smul continuous_const), fun Y hY => ?_⟩
  have hPY : projAt h v x₀ w₀ Y = Y := by
    funext w
    rw [projAt_apply, (hY w).1, (hY w).2, zero_smul, zero_smul, sub_zero, sub_zero]
  set s : _ → ℝ := fun k => Bs.repr Y k * (D k)⁻¹ with hs
  have hYs : Y = ∑ k, s k • vecAt v (f k) := by
    calc Y = (projAt h v x₀ w₀).restrictScalars ℝ (∑ k, Bs.repr Y k • Bs k) := by
          rw [Bs.sum_repr]; exact hPY.symm
      _ = ∑ k, Bs.repr Y k • vecAt v (p k) := by
          simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, hBe]
          exact Finset.sum_congr rfl fun k _ => by rw [projAt_vecAt]
      _ = _ := Finset.sum_congr rfl fun k _ => by
          rw [hf, smul_smul, hs, mul_assoc, inv_mul_cancel₀ (hD k), mul_one]
  refine ⟨∑ k, ⌊s k⌋ • f k, ?_, ⟨∑ k, ⌊s k⌋ • d k • p k, ?_, ?_⟩,
    ⟨fun k => Int.fract (s k), ⟨fun k => Int.fract_nonneg _, fun k => (Int.fract_lt_one _).le⟩, ?_⟩⟩
  · exact Submodule.sum_mem _ fun k _ =>
      zsmul_mem (nsmul_mem (zsmul_mem (ComplementExtension.proj hp (e k)).2 _) _) _
  · exact La.sum_mem fun k _ => La.zsmul_mem (hdL k) _
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · show ∑ k, Int.fract (s k) • vecAt v (f k) = Y - vecAt v (∑ k, ⌊s k⌋ • f k)
    conv_rhs => rw [hYs]
    rw [← vecAtHom_apply, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, vecAtHom_apply, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, Int.self_sub_floor]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
