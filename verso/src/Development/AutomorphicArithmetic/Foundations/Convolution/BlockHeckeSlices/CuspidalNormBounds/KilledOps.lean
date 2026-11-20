import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift

open NumberField

namespace UpperTheory.ConvolutionTheory.BW

/- English proof (translation)
Set `A : (K →₀ ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ` to `Finsupp.linearCombination ℂ ρ`. Set `B : (K →₀ ℂ) →ₗ[ℂ] (X → ℂ)` to `Finsupp.linearCombination ℂ ψ`. Establish `hAB : LinearMap.ker A ≤ LinearMap.ker B`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`.

Use function extensionality and compare the values at `g`. Use `h x (by simpa [A, Finsupp.linearCombination_apply] using hx) g` as an intermediate fact. Simplify `this` using `[B, Finsupp.linearCombination_apply, Finsupp.sum_apply']`. Use `haveI : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker A) := Module.Finite.equiv A.quotKerEquivRange.symm`. Establish `hr : LinearMap.range ((LinearMap.ker A).liftQ B hAB) = Submodule.span ℂ (Set.range ψ)`.

Rewrite using `[Submodule.range_liftQ]`. Conclude with `Finsupp.range_linearCombination ℂ`. Rewrite using `[← hr]`. Use `infer_instance`.
-/
private theorem finite_span_of_killed {K X : Type} {d : ℕ} (ρ : K → Matrix (Fin d) (Fin d) ℂ) (ψ : K → X → ℂ)
    (h : ∀ x : K →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ g : X, (x.sum fun k c => c * ψ k g) = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) := by
  let A : (K →₀ ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ := Finsupp.linearCombination ℂ ρ
  let B : (K →₀ ℂ) →ₗ[ℂ] (X → ℂ) := Finsupp.linearCombination ℂ ψ
  have hAB : LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext g
    have := h x (by simpa [A, Finsupp.linearCombination_apply] using hx) g
    simpa [B, Finsupp.linearCombination_apply, Finsupp.sum_apply'] using this
  haveI : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker A) :=
    Module.Finite.equiv A.quotKerEquivRange.symm
  have hr : LinearMap.range ((LinearMap.ker A).liftQ B hAB) = Submodule.span ℂ (Set.range ψ) := by
    rw [Submodule.range_liftQ]
    exact Finsupp.range_linearCombination ℂ
  rw [← hr]
  infer_instance

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep in
/- English proof (translation)
Introduce `E _ _ _ n ρ φ hφ`. Use `⟨fun k x hx g => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : ((x.mapDomain fun k' => k' * k).sum fun k' c => c • ρ.ρ k') = 0`. Rewrite using `[Finsupp.sum_mapDomain_index (h := fun k' c => c • ρ.ρ k') (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Establish `: (x.sum fun k' c => c • ρ.ρ (k' * k)) = (x.sum fun k' c => c • ρ.ρ k') * ρ.ρ k`.

Rewrite using `[Finsupp.sum_mul]`. Simplify using `only [map_mul, smul_mul_assoc]`. Rewrite using `[this, hx, zero_mul]`. Establish `h1` using `hφ _ h0 g`. Rewrite `h1` using `[Finsupp.sum_mapDomain_index (h := fun (k' : KA E n) c => c * φ.1 (g * (k' : GA E n))) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]`.

Simplify using `only [Subgroup.coe_mul, ← mul_assoc] at h1`. Conclude with `h1`. Unfold `GroundTheory.Automorphic.AutomorphicForm.IsKFinite`. Conclude with `finite_span_of_killed ρ.ρ _ (fun x hx g => hφ x hx g)`.
-/
theorem UpperTheory.ConvolutionTheory.BW.killedOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KilledOps E := by
  intro E _ _ _ n ρ φ hφ
  refine ⟨fun k x hx g => ?_, ?_⟩
  · have h0 : ((x.mapDomain fun k' => k' * k).sum fun k' c => c • ρ.ρ k') = 0 := by
      rw [Finsupp.sum_mapDomain_index (h := fun k' c => c • ρ.ρ k') (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
      have : (x.sum fun k' c => c • ρ.ρ (k' * k)) = (x.sum fun k' c => c • ρ.ρ k') * ρ.ρ k := by
        rw [Finsupp.sum_mul]
        simp only [map_mul, smul_mul_assoc]
      rw [this, hx, zero_mul]
    have h1 := hφ _ h0 g
    rw [Finsupp.sum_mapDomain_index (h := fun (k' : KA E n) c => c * φ.1 (g * (k' : GA E n))) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at h1
    simp only [Subgroup.coe_mul, ← mul_assoc] at h1
    exact h1
  · unfold GroundTheory.Automorphic.AutomorphicForm.IsKFinite
    exact finite_span_of_killed ρ.ρ _ (fun x hx g => hφ x hx g)
