import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

noncomputable section
open scoped Pointwise

namespace GlobalTheory.TwistIntegral

/- English proof (translation)
Introduce `g M hM D hD V _ _ _ ψ l₀ a hper htw ha`. Take `⟨hdisc, hlat⟩` from `hM`. Use `haveI : MeasurableVAdd M (Fl g) := (inferInstance : MeasurableVAdd M.toAddSubgroup (Fl g))`. Use `haveI : VAddInvariantMeasure M (Fl g) volume := (inferInstance : VAddInvariantMeasure M.toAddSubgroup (Fl g) volume)`. Use `haveI : Countable M := inferInstance`.

Establish `ht : IsAddFundamentalDomain M (l₀ +ᵥ D) volume` using `hD.vadd_of_comm l₀`. Establish `e1 : ∫ y in D, ψ y = ∫ y in l₀ +ᵥ D, ψ y` using `hD.setIntegral_eq ht (fun m y => by`. Break down `m with ⟨m, hm⟩` into its components or cases. Simplify `hper m hm y)` using `[Submodule.vadd_def, add_comm]`. Establish `e2 : ∫ y in l₀ +ᵥ D, ψ y = ∫ y in D, ψ (y + l₀)`.

Use `(measurePreserving_add_right (volume : Measure (Fl g)) l₀).setIntegral_preimage_emb (measurableEmbedding_addRight l₀) ψ (l₀ +ᵥ D)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 2`. Use extensionality with `y`. Simplify using `[Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]`.

Establish `e3 : ∫ y in D, ψ (y + l₀) = a • ∫ y in D, ψ y`. Repeatedly rewrite using `[htw]`. Conclude with `integral_smul a _`. Establish `h0 : (1 - a) • ∫ y in D, ψ y = 0` using `by rw [sub_smul, one_smul, ← e3, ← e2, ← e1, sub_self]`. Conclude with `(smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm ha))`.
-/
theorem setIntegral_eq_zero_of_twist : ∀ {g : ℕ} (M : Submodule ℤ (Fl g)), IsLat M → ∀ (D : Set (Fl g)),
    IsAddFundamentalDomain M D volume → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (ψ : Fl g → V) (l₀ : Fl g) (a : ℂ), (∀ l ∈ M, ∀ x, ψ (x + l) = ψ x) → (∀ x, ψ (x + l₀) = a • ψ x) →
    a ≠ 1 → ∫ x in D, ψ x = 0 := by
  intro g M hM D hD V _ _ _ ψ l₀ a hper htw ha
  obtain ⟨hdisc, hlat⟩ := hM
  haveI : MeasurableVAdd M (Fl g) := (inferInstance : MeasurableVAdd M.toAddSubgroup (Fl g))
  haveI : VAddInvariantMeasure M (Fl g) volume :=
    (inferInstance : VAddInvariantMeasure M.toAddSubgroup (Fl g) volume)
  haveI : Countable M := inferInstance
  have ht : IsAddFundamentalDomain M (l₀ +ᵥ D) volume := hD.vadd_of_comm l₀
  have e1 : ∫ y in D, ψ y = ∫ y in l₀ +ᵥ D, ψ y :=
    hD.setIntegral_eq ht (fun m y => by
      rcases m with ⟨m, hm⟩
      simpa [Submodule.vadd_def, add_comm] using hper m hm y)
  have e2 : ∫ y in l₀ +ᵥ D, ψ y = ∫ y in D, ψ (y + l₀) := by
    have := (measurePreserving_add_right (volume : Measure (Fl g)) l₀).setIntegral_preimage_emb
      (measurableEmbedding_addRight l₀) ψ (l₀ +ᵥ D)
    rw [← this]
    congr 2
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]
  have e3 : ∫ y in D, ψ (y + l₀) = a • ∫ y in D, ψ y := by
    simp_rw [htw]
    exact integral_smul a _
  have h0 : (1 - a) • ∫ y in D, ψ y = 0 := by rw [sub_smul, one_smul, ← e3, ← e2, ← e1, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

end GlobalTheory.TwistIntegral
