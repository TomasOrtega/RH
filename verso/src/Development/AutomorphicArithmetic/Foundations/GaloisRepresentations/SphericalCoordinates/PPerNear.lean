import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinearStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.PerCoordU GlobalTheory.PeriodCoord

namespace UpperTheory.Gal.W2

/- English proof (translation)
Introduce `O _ bar g ρ D P₀ M₀ hP hM d co hco`. Take `⟨hHerm, hPos, hIm⟩` from `hM`. Establish `hdet : M₀.det ≠ 0` using `det_ne_zero_of_pos hPos`. Take `⟨t, ht, htO, ht0⟩` from `eventually_nhds_iff.mp (T.eventually_posDef_hermForm_near_zero_matrix M₀ hPos)`. Establish `hcont : Continuous co` using `LinearMap.continuous_of_finiteDimensional co`.

Use `⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Take `⟨h1, h2, h3⟩` from `ht (co b) hb`. Establish `hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ` using `hco b`. Take `⟨hH, hF⟩` from `T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1`.

Establish `hcomm` using `comm_of_mem_Tsp hP hIm hdet hT`. Use `T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP (realMap_one_injective h2) ?_ hH h3 ?_` and prove the remaining obligations. Introduce `a x`. Simplify using `only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map, Matrix.mulVec_mulVec, hcomm a]`. Rewrite using `[Matrix.one_mul]`.

Introduce `x y`. Simplify using `only [realMap_apply, Matrix.one_mulVec]`. Rewrite using `[hF, hIm]`. Introduce `x set v := star (P₀ x)`. Set `f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `{ toFun := fun b => co b *ᵥ v map_add' := by intro a b; simp [Matrix.add_mulVec] map_smul' := by intro c b; simp [Matrix.smul_mulVec] }`.

Establish `hf : Differentiable ℂ (fun b => co b *ᵥ v)` using `(LinearMap.toContinuousLinearMap f).differentiable`. Establish `: (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v`. Use function extensionality and compare the values at `b`. Simplify using `[perC_apply, v]`. Rewrite using `[this]`.

Conclude with `((differentiable_const _).add hf).differentiableOn`.
-/
theorem perNear_of : PerNear := by
  intro O _ bar g ρ D P₀ M₀ hP hM d co hco
  obtain ⟨hHerm, hPos, hIm⟩ := hM
  have hdet : M₀.det ≠ 0 := det_ne_zero_of_pos hPos
  obtain ⟨t, ht, htO, ht0⟩ := eventually_nhds_iff.mp (T.eventually_posDef_hermForm_near_zero_matrix M₀ hPos)
  have hcont : Continuous co := LinearMap.continuous_of_finiteDimensional co
  refine ⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := ht (co b) hb
    have hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ := hco b
    obtain ⟨hH, hF⟩ := T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1
    have hcomm := comm_of_mem_Tsp hP hIm hdet hT
    refine T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP
      (realMap_one_injective h2) ?_ hH h3 ?_
    · intro a x
      simp only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map,
        Matrix.mulVec_mulVec, hcomm a]
      rw [Matrix.one_mul]
    · intro x y
      simp only [realMap_apply, Matrix.one_mulVec]
      rw [hF, hIm]
  · intro x
    set v := star (P₀ x)
    let f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => co b *ᵥ v
        map_add' := by intro a b; simp [Matrix.add_mulVec]
        map_smul' := by intro c b; simp [Matrix.smul_mulVec] }
    have hf : Differentiable ℂ (fun b => co b *ᵥ v) :=
      (LinearMap.toContinuousLinearMap f).differentiable
    have : (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v := by
      funext b; simp [perC_apply, v]
    rw [this]
    exact ((differentiable_const _).add hf).differentiableOn

end UpperTheory.Gal.W2
