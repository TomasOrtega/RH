import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

/- English proof (translation)
Introduce `A hO hfg`. Establish `: AddGroup.FG A` using `(AddGroup.fg_iff_addSubgroup_fg A).mpr hfg`. Take `⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A` from `Module.basisOfFiniteTypeTorsionFree'`. Set `f : A →ₗ[ℤ] E` to `A.subtype.toIntLinearMap`. Set `v : Fin n → E` to `fun i => (b i : E)`.

Establish `hv : v = f ∘ b` using `rfl`. Establish `hliZ : LinearIndependent ℤ v` using `b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)`. Establish `hliQ : LinearIndependent ℚ v` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ`. Establish `hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v)`. Introduce `a ha`.

Establish `h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b)` using `Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)`. Rewrite `h1` using `[← Set.range_comp, ← hv]`. Conclude with `Submodule.span_le_restrictScalars ℤ ℚ _ h1`. Establish `hsp : ⊤ ≤ Submodule.span ℚ (Set.range v)`. Rewrite using `[← (integralBasis E).span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[integralBasis_apply]`. Conclude with `hA _ (hO ⟨_, rfl⟩)`. Establish `hn : finrank ℚ E = n`. Rewrite using `[finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]`.

Conclude with `⟨b.reindex (finCongr hn.symm)⟩`.
-/
theorem CoeffLatticeBasis.proof (E : Type*) [Field E] [NumberField E] :
    CoeffLatticeBasis.Statement E := by
  intro A hO hfg
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).mpr hfg
  obtain ⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A := Module.basisOfFiniteTypeTorsionFree'

  let f : A →ₗ[ℤ] E := A.subtype.toIntLinearMap
  let v : Fin n → E := fun i => (b i : E)
  have hv : v = f ∘ b := rfl
  have hliZ : LinearIndependent ℤ v :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v) := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)
    rw [← Set.range_comp, ← hv] at h1
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← (integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact hA _ (hO ⟨_, rfl⟩)
  have hn : finrank ℚ E = n := by
    rw [finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]
  exact ⟨b.reindex (finCongr hn.symm)⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
