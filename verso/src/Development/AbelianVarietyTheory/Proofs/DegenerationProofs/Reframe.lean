import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

/- English proof (translation)
Introduce `hT Q L₀ g u₀ _ _ _`. Take `⟨rig, hrig⟩` from `Q.rigid`. Take `⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, -, hEf, -⟩` from `hT Q rig hrig`. Take `⟨F, hF₀, -⟩` from `HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb L₀ Q.L g Q.g u₀ u ht₁ ht₂ (𝟙 _) inferInstance`. Establish `hF : ∀ z, u.ex (F z) = u₀.ex z` using `fun z => (hF₀ z).trans (Category.comp_id _)`.

Establish `hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ u₀.Λ` using `fun z => by rw [← u.ker, hF, u₀.ker]`. Establish `cΛ : (u.Λ : Set (Fin Q.g → ℂ)).Countable`. Use `u.discrete` as an intermediate fact. Conclude with `(countable_of_Lindelof_of_discrete : Countable u.Λ)`. Establish `cΛ₀ : (u₀.Λ : Set (Fin g → ℂ)).Countable`.

Use `u₀.discrete` as an intermediate fact. Conclude with `(countable_of_Lindelof_of_discrete : Countable u₀.Λ)`. Establish `Finj : Function.Injective F` using `(injective_iff_map_eq_zero F).2 fun z hz => FibreUnif.eq_zero_of_smul_mem_countable cΛ₀ fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)`. Establish `Fsurj : Function.Surjective F` using `FibreUnif.surjective_of_countable F cΛ fun v => by`. Take `⟨z, hz⟩` from `u₀.ex_onto (u.ex v)`.

Use `⟨z, (u.ker _).1 ?_⟩` and prove the remaining obligations. Use `u.ex_add (v - F z) (F z)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, hF, hz]`. Conclude with `right_eq_mul.1 this`. Conclude with `⟨u, Hm, χ, Ef, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, hEf, hF⟩`.
-/
theorem reframe : ThetaUnifAV → ReframeSt := by
  intro hT Q L₀ g u₀ _ _ _
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, -, hEf, -⟩ := hT Q rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb L₀ Q.L g Q.g u₀ u ht₁ ht₂
    (𝟙 _) inferInstance
  have hF : ∀ z, u.ex (F z) = u₀.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ u₀.Λ := fun z => by rw [← u.ker, hF, u₀.ker]
  have cΛ : (u.Λ : Set (Fin Q.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cΛ₀ : (u₀.Λ : Set (Fin g → ℂ)).Countable := by
    have := u₀.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u₀.Λ)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    FibreUnif.eq_zero_of_smul_mem_countable cΛ₀ fun t =>
      (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := FibreUnif.surjective_of_countable F cΛ fun v => by
    obtain ⟨z, hz⟩ := u₀.ex_onto (u.ex v)
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hz] at this
    exact right_eq_mul.1 this
  exact ⟨u, Hm, χ, Ef, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, hEf, hF⟩

end GlobalTheory.Ex.Arch
