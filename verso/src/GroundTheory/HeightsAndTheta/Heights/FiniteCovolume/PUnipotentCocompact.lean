import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `D La x₀ hLa hx₀ hne hiso`. Take `⟨w₀, h1, h2⟩` from `WittPartner.proof h x₀ hne hiso`. Establish `hp : IsHyperbolicPair h x₀ w₀` using `⟨hiso, h2, h1⟩`. Take `⟨K₁, hK₁, hred⟩` from `hH D La x₀ w₀ hLa hx₀ hp`. Take `⟨K, hK, hcen⟩` from `hC D La x₀ w₀ hLa hx₀ hp K₁ hK₁`.

Use `⟨{n | unipCoord h v x₀ w₀ n ∈ K}, hP x₀ w₀ hp K hK, fun n => ?_⟩` and prove the remaining obligations. Take `⟨δ₁, hδ₁, t, ht⟩` from `hred n`. Take `⟨δ₂, hδ₂, hK'⟩` from `hcen (δ₁ * n) ⟨t, ht⟩`. Use `⟨δ₂ * δ₁, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.mul_mem _ hδ₂ hδ₁`.

Express the relevant statement in the definitionally equal form `unipCoord h v x₀ w₀ (δ₂ * δ₁ * n) ∈ K`. Rewrite using `[mul_assoc]` and apply the resulting hypothesis.
-/
theorem UnipotentCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : UnipotentCoordProper.Statement h v) (hH : UnipotentHorizontal.Statement h v)
    (hC : UnipotentCentral.Statement h v) : UnipotentCocompact.Statement h v := by
  intro D La x₀ hLa hx₀ hne hiso
  obtain ⟨w₀, h1, h2⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, h2, h1⟩
  obtain ⟨K₁, hK₁, hred⟩ := hH D La x₀ w₀ hLa hx₀ hp
  obtain ⟨K, hK, hcen⟩ := hC D La x₀ w₀ hLa hx₀ hp K₁ hK₁
  refine ⟨{n | unipCoord h v x₀ w₀ n ∈ K}, hP x₀ w₀ hp K hK, fun n => ?_⟩
  obtain ⟨δ₁, hδ₁, t, ht⟩ := hred n
  obtain ⟨δ₂, hδ₂, hK'⟩ := hcen (δ₁ * n) ⟨t, ht⟩
  refine ⟨δ₂ * δ₁, ?_, ?_⟩
  · exact Subgroup.mul_mem _ hδ₂ hδ₁
  · change unipCoord h v x₀ w₀ (δ₂ * δ₁ * n) ∈ K
    rwa [mul_assoc]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
