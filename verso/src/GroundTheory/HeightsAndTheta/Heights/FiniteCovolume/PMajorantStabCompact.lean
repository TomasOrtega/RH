import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace MajorantStabCompact

/- English proof (translation)
Establish `hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ`. Use extensionality with `i j`. Simplify using `[conjTranspose_apply]`. Rewrite `hA` using `[hc]`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]`.
-/
theorem form_mulVec {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by
  have hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hc] at hA
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

end MajorantStabCompact

open MajorantStabCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

/- English proof (translation)
Introduce `M`. Use `set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm`. Establish `he : Submodule.span E (Set.range e) = ⊤`. Rewrite using `[Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]`. Use `set C : ℝ := ∑ a, M.len (vecAt v (e a))`.

Establish `hcpt` using `BoundedInverseCompact.proof h v M _ e he C`. Establish `hclosed : IsClosed (M.stab : Set (archUnitary h v))`. Establish `: (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v | ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w * (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w}`. Use extensionality with `g`. Simplify using `[Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]`.

Rewrite using `[this]`. Use `isClosed_iInter fun w => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Establish `hg : Continuous fun g : archUnitary h v => (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))` using `Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)`. Conclude with `((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul continuous_const).matrix_mul hg`. Use `hcpt.of_isClosed_subset hclosed ?_` and prove the remaining obligations.

Introduce `g hg a`. Establish `hgi : (g⁻¹ : archUnitary h v) ∈ M.stab` using `inv_mem hg`. Establish `hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w`. Introduce `w`. Use `(Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)` as an intermediate fact.

Conclude with `mem_unitaryGroupMatrix.mp this`. Establish `heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a))`. Simplify using `only [Majorant.len, invApply]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]`.

Rewrite using `[heq]`. Conclude with `Finset.single_le_sum (f := fun a => M.len (vecAt v (e a))) (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)`.
-/
theorem MajorantStabCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by
  intro M
  set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm
  have he : Submodule.span E (Set.range e) = ⊤ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]
  set C : ℝ := ∑ a, M.len (vecAt v (e a))
  have hcpt := BoundedInverseCompact.proof h v M _ e he C

  have hclosed : IsClosed (M.stab : Set (archUnitary h v)) := by
    have : (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
        ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w *
          (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w} := by
      ext g
      simp [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]
    rw [this]
    refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
    have hg : Continuous fun g : archUnitary h v =>
        (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) :=
      Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
    exact ((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hg
  refine hcpt.of_isClosed_subset hclosed ?_
  intro g hg a

  have hgi : (g⁻¹ : archUnitary h v) ∈ M.stab := inv_mem hg
  have hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map
      (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ)) = M.P w := by
    intro w
    have := (Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)
    exact mem_unitaryGroupMatrix.mp this
  have heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a)) := by
    simp only [Majorant.len, invApply]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]
  rw [heq]
  exact Finset.single_le_sum (f := fun a => M.len (vecAt v (e a)))
    (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
