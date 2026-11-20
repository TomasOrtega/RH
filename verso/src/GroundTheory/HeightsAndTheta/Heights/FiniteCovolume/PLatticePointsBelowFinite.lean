import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Imports
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoerciveOfPositiveDefinite

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef hP`.
-/
theorem exists_coercive_of_posDef {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ (P *ᵥ z)).re :=
  _root_.UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef hP

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

/- English proof (translation)
Use `choose c hc hcoer using fun w => exists_coercive_of_posDef (M.posDef w)`. Use `set G : InfinitePlace E → Matrix ι ι ℂ := fun w => (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) with hG`. Use `⟨∑ w, ∑ i, ∑ j, ‖G w i j‖ / Real.sqrt (c w), by positivity, fun y w i => ?_⟩` and prove the remaining obligations. Use `set z := invApply g y with hz`. Establish `hre : ∀ w', 0 ≤ (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re` using `fun w' => (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (z w'))).1`.

Establish `hinv : G w * (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1`. Simplify using `[hG]`. Establish `hy : y w = G w *ᵥ z w`. Rewrite using `[hz, invApply, mulVec_mulVec, hinv, one_mulVec]`. Establish `hzj : ∀ j, ‖z w j‖ ≤ M.len z / Real.sqrt (c w)`.

Introduce `j`. Establish `hsq : 0 < Real.sqrt (c w)` using `Real.sqrt_pos.2 (hc w)`. Rewrite using `[le_div_iff₀ hsq]`. Establish `h1 : c w * ‖z w j‖ ^ 2 ≤ ∑ w', (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re` using `(hcoer w (z w) j).trans (Finset.single_le_sum (fun w' _ => hre w') (Finset.mem_univ w))`. Establish `h2` using `Real.sqrt_le_sqrt h1`.

Rewrite `h2` using `[Real.sqrt_mul (hc w).le, Real.sqrt_sq (norm_nonneg _)]`. Unfold `Majorant.len`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlen : 0 ≤ M.len z` using `Real.sqrt_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hzj j) (norm_nonneg _)`. Use `_ = (∑ j, ‖G w i j‖ / Real.sqrt (c w)) * M.len z := by rw [Finset.sum_mul]`. Use `_ ≤ (∑ w', ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) * M.len z := by`.

Use `mul_le_mul_of_nonneg_right ?_ hlen` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun w' => ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) (fun _ _ => by positivity) (Finset.mem_univ w))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i' => ∑ j, ‖G w i' j‖ / Real.sqrt (c w)) (fun _ _ => by positivity) (Finset.mem_univ i)`.
-/
theorem exists_coord_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (g : archUnitary h v) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : InfinitePlace E → ι → ℂ) w i,
      ‖y w i‖ ≤ K * M.len (invApply g y) := by
  choose c hc hcoer using fun w => exists_coercive_of_posDef (M.posDef w)
  set G : InfinitePlace E → Matrix ι ι ℂ := fun w =>
    (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) with hG
  refine ⟨∑ w, ∑ i, ∑ j, ‖G w i j‖ / Real.sqrt (c w), by positivity, fun y w i => ?_⟩
  set z := invApply g y with hz
  have hre : ∀ w', 0 ≤ (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re := fun w' =>
    (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (z w'))).1
  have hinv : G w * (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
    simp [hG]
  have hy : y w = G w *ᵥ z w := by
    rw [hz, invApply, mulVec_mulVec, hinv, one_mulVec]
  have hzj : ∀ j, ‖z w j‖ ≤ M.len z / Real.sqrt (c w) := by
    intro j
    have hsq : 0 < Real.sqrt (c w) := Real.sqrt_pos.2 (hc w)
    rw [le_div_iff₀ hsq]
    have h1 : c w * ‖z w j‖ ^ 2 ≤ ∑ w', (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re :=
      (hcoer w (z w) j).trans (Finset.single_le_sum (fun w' _ => hre w') (Finset.mem_univ w))
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (hc w).le, Real.sqrt_sq (norm_nonneg _)] at h2
    unfold Majorant.len
    linarith
  have hlen : 0 ≤ M.len z := Real.sqrt_nonneg _
  calc ‖y w i‖ = ‖∑ j, G w i j * z w j‖ := by rw [hy]; rfl
    _ ≤ ∑ j, ‖G w i j‖ * ‖z w j‖ := (norm_sum_le _ _).trans (by simp)
    _ ≤ ∑ j, ‖G w i j‖ / Real.sqrt (c w) * M.len z := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hzj j) (norm_nonneg _)
    _ = (∑ j, ‖G w i j‖ / Real.sqrt (c w)) * M.len z := by rw [Finset.sum_mul]
    _ ≤ (∑ w', ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) * M.len z := by
        refine mul_le_mul_of_nonneg_right ?_ hlen
        refine le_trans ?_ (Finset.single_le_sum (f := fun w' => ∑ i', ∑ j,
          ‖G w' i' j‖ / Real.sqrt (c w')) (fun _ _ => by positivity) (Finset.mem_univ w))
        exact Finset.single_le_sum (f := fun i' => ∑ j, ‖G w i' j‖ / Real.sqrt (c w))
          (fun _ _ => by positivity) (Finset.mem_univ i)

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

/- English proof (translation)
Introduce `M La g t hLa`. Take `⟨S, hS⟩` from `hLa.fg`. Take `⟨d, hd0, hd⟩` from `exists_integral_multiples ℤ ℚ (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)`. Set `T : AddSubgroup W` to `{ carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)} add_mem' := fun {a b} ha hb i => by`. Simplify `(ha i).add (hb i)` using `only [map_add, Finsupp.add_apply, smul_add]`.

Use the proof step `zero_mem' := fun i => by`. Simplify `isIntegral_zero` using `only [map_zero, Finsupp.zero_apply, smul_zero]`. Use the proof step `neg_mem' := fun {a} ha i => by`. Simplify `(ha i).neg }` using `only [map_neg, Finsupp.neg_apply, smul_neg]`. Establish `hLaT : La ≤ T`.

Rewrite using `[← hS, AddSubgroup.closure_le]`. Introduce `s hs i`. Conclude with `hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)`. Establish `hdE : (d : E) ≠ 0` using `Int.cast_ne_zero.2 hd0`. Take `⟨K, hK0, hK⟩` from `exists_coord_le_len M g`.

Use `set B : ℝ := |(d : ℝ)| * (K * t) with hB`. Use `set A : Set E := {a | IsIntegral ℤ a ∧ ∀ φ : E →+* ℂ, ‖φ a‖ ≤ B} with hA`. Establish `hAfin : A.Finite` using `NumberField.Embeddings.finite_of_norm_le E ℂ B`. Use `set φ : W → ι → E := fun x i => d • v.repr x i with hφ`. Establish `hinj : Function.Injective φ`.

Introduce `x y hxy`. Use `v.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations. Use `congrFun hxy i` as an intermediate fact. Simplify using `only [hφ, zsmul_eq_mul] at this`. Conclude with `mul_left_cancel₀ hdE this`.

Use `((Set.Finite.pi (t := fun _ : ι => A) fun _ => hAfin).preimage hinj.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxt⟩ i -`. Use `⟨hLaT hx i, fun ψ => ?_⟩` and prove the remaining obligations. Establish `hw : ‖ψ (v.repr x i)‖ = ‖(InfinitePlace.mk ψ).embedding (v.repr x i)‖`. Rewrite using `[InfinitePlace.norm_embedding_eq, InfinitePlace.apply]`.

Establish `hb` using `hK (vecAt v x) (InfinitePlace.mk ψ) i`. Express the relevant statement in the definitionally equal form `‖ψ (d • v.repr x i)‖ ≤ B`. Rewrite using `[zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast, hw, hB]`. Use `mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)` and prove the remaining obligations. Conclude with `hb.trans (mul_le_mul_of_nonneg_left hxt.le hK0)`.
-/
theorem LatticePointsBelowFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LatticePointsBelowFinite.Statement h v := by
  classical
  intro M La g t hLa
  obtain ⟨S, hS⟩ := hLa.fg

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add, Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    rw [← hS, AddSubgroup.closure_le]
    intro s hs i
    exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  obtain ⟨K, hK0, hK⟩ := exists_coord_le_len M g
  set B : ℝ := |(d : ℝ)| * (K * t) with hB
  set A : Set E := {a | IsIntegral ℤ a ∧ ∀ φ : E →+* ℂ, ‖φ a‖ ≤ B} with hA
  have hAfin : A.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  set φ : W → ι → E := fun x i => d • v.repr x i with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have := congrFun hxy i
    simp only [hφ, zsmul_eq_mul] at this
    exact mul_left_cancel₀ hdE this
  refine ((Set.Finite.pi (t := fun _ : ι => A) fun _ => hAfin).preimage hinj.injOn).subset ?_
  rintro x ⟨hx, hxt⟩ i -
  refine ⟨hLaT hx i, fun ψ => ?_⟩
  have hw : ‖ψ (v.repr x i)‖ = ‖(InfinitePlace.mk ψ).embedding (v.repr x i)‖ := by
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  have hb := hK (vecAt v x) (InfinitePlace.mk ψ) i
  change ‖ψ (d • v.repr x i)‖ ≤ B
  rw [zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast, hw, hB]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hxt.le hK0)

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
