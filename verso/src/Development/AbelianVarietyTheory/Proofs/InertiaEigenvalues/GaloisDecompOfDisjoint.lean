import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
namespace GlobalTheory.InertiaEigenvalues

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem galois_decomp_of_disjoint : ∀ (l : ℕ) [Fact l.Prime] (K M : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] K → IsGalois ℚ_[l] K → K ⊓ M = ⊥ → ∀ g : GQ l, ∃ h ∈ K.fixingSubgroup, ∃ k ∈ M.fixingSubgroup, g = h * k := by
  intro l _ K M _ _ hKM g
  let r : GQ l →* (K ≃ₐ[ℚ_[l]] K) := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) K
  have hr : ∀ (σ : GQ l) (y : K), ((r σ y : K) : Om l) = σ (y : Om l) := fun σ y =>
    AlgEquiv.restrictNormal_commutes σ K y
  let H : Subgroup (K ≃ₐ[ℚ_[l]] K) := M.fixingSubgroup.map r
  have hfix : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxM : (x : Om l) ∈ M := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro k
      have := hx ⟨r k, Subgroup.mem_map_of_mem r k.2⟩
      have h2 := congrArg (fun z : K => (z : Om l)) this
      change (k : GQ l) (x : Om l) = x
      simpa [hr] using h2
    have hxKM : (x : Om l) ∈ K ⊓ M := ⟨x.2, hxM⟩
    rw [hKM, IntermediateField.mem_bot] at hxKM
    obtain ⟨c, hc⟩ := hxKM
    rw [IntermediateField.mem_bot]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa using hc
  have hH : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfix, IntermediateField.fixingSubgroup_bot]
  have hg : r g ∈ H := by rw [hH]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
  refine ⟨g * k⁻¹, ?_, k, hk, by group⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : r (g * k⁻¹) = 1 := by rw [map_mul, map_inv, ← hkg, mul_inv_cancel]
  have := hr (g * k⁻¹) ⟨x, hx⟩
  rw [h1] at this
  simpa using this.symm

end GlobalTheory.InertiaEigenvalues
