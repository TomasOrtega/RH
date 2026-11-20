import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CoefFam

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Take `⟨W, hW, hmem⟩` from `A.fin x`. Take `⟨C, hC⟩` from `A.bdd`. Set `b` to `Module.finBasis ℂ W`. Set `embW : W →ₗ[ℂ] A.N` to `A.emb ∘ₗ W.subtype`. Establish `hinj : Function.Injective embW` using `A.inj.comp Subtype.val_injective`.

Set `e : W ≃ₗ[ℂ] LinearMap.range embW` to `LinearEquiv.ofInjective embW hinj`. Establish `: FiniteDimensional ℂ (LinearMap.range embW)` using `LinearMap.finiteDimensional_range embW`. Set `ψ : Fin (Module.finrank ℂ W) → (LinearMap.range embW →L[ℂ] ℂ)` to `fun l => LinearMap.toContinuousLinearMap ((b.coord l) ∘ₗ e.symm.toLinearMap)`. Use `⟨Module.finrank ℂ W, fun l => (b l : X.V), fun l k => b.repr ⟨A.ρ k x, hmem k⟩ l, ∑ l, ‖ψ l‖ * (|C| * ‖A.emb x‖), fun l k => ?_, fun k => ?_⟩` and prove the remaining obligations. Establish `h1 : b.repr ⟨A.ρ k x, hmem k⟩ l = ψ l (e ⟨A.ρ k x, hmem k⟩)`.

Simplify using `[ψ]`. Use `show ‖b.repr ⟨A.ρ k x, hmem k⟩ l‖ ≤ _`. Rewrite using `[h1]`. Establish `h2 : ‖e ⟨A.ρ k x, hmem k⟩‖ = ‖A.emb (A.ρ k x)‖` using `rfl`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `(hC k x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))`. Use `_ ≤ _ := Finset.single_le_sum (f := fun l => ‖ψ l‖ * (|C| * ‖A.emb x‖)) (fun l _ => by positivity) (Finset.mem_univ l)`. Establish `h3` using `congrArg Subtype.val (b.sum_repr ⟨A.ρ k x, hmem k⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h3`. Conclude with `h3.symm`.
-/
theorem rightExp {ε : Fin n → Bool} {X : GMod n} (A : KAct ε X) (x : X.V) :
    ∃ (r : ℕ) (w : Fin r → X.V) (a : Fin r → S7.KG ε → ℂ) (B : ℝ), (∀ l k, ‖a l k‖ ≤ B) ∧
      ∀ k, A.ρ k x = ∑ l, a l k • w l := by
  obtain ⟨W, hW, hmem⟩ := A.fin x
  obtain ⟨C, hC⟩ := A.bdd
  let b := Module.finBasis ℂ W
  let embW : W →ₗ[ℂ] A.N := A.emb ∘ₗ W.subtype
  have hinj : Function.Injective embW := A.inj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range embW := LinearEquiv.ofInjective embW hinj
  have : FiniteDimensional ℂ (LinearMap.range embW) := LinearMap.finiteDimensional_range embW
  let ψ : Fin (Module.finrank ℂ W) → (LinearMap.range embW →L[ℂ] ℂ) :=
    fun l => LinearMap.toContinuousLinearMap ((b.coord l) ∘ₗ e.symm.toLinearMap)
  refine ⟨Module.finrank ℂ W, fun l => (b l : X.V), fun l k => b.repr ⟨A.ρ k x, hmem k⟩ l,
    ∑ l, ‖ψ l‖ * (|C| * ‖A.emb x‖), fun l k => ?_, fun k => ?_⟩
  · have h1 : b.repr ⟨A.ρ k x, hmem k⟩ l = ψ l (e ⟨A.ρ k x, hmem k⟩) := by
      simp [ψ]
    show ‖b.repr ⟨A.ρ k x, hmem k⟩ l‖ ≤ _
    rw [h1]
    have h2 : ‖e ⟨A.ρ k x, hmem k⟩‖ = ‖A.emb (A.ρ k x)‖ := rfl
    calc ‖ψ l (e ⟨A.ρ k x, hmem k⟩)‖ ≤ ‖ψ l‖ * ‖e ⟨A.ρ k x, hmem k⟩‖ := (ψ l).le_opNorm _
      _ ≤ ‖ψ l‖ * (|C| * ‖A.emb x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [h2]
          exact (hC k x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
      _ ≤ _ := Finset.single_le_sum (f := fun l => ‖ψ l‖ * (|C| * ‖A.emb x‖))
          (fun l _ => by positivity) (Finset.mem_univ l)
  · have h3 := congrArg Subtype.val (b.sum_repr ⟨A.ρ k x, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
    exact h3.symm

end CompanionTheory.RgExh.Dec.L.WyKR
