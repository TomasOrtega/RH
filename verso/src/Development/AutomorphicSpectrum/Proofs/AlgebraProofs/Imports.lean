import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfShortExactStatement

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂] (r r₂ : ℕ) (L : AddSubgroup E) (C C' : AddSubgroup E₂) (Δ : AddSubgroup (E × E₂)), LocFree R r L → LocFree R r₂ C → LocFree R r₂ C' → (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → (∀ v w, (v, w) ∈ Δ → v ∈ L ∧ w ∈ C) → (∀ v ∈ L, ∃ w, (v, w) ∈ Δ) → (∀ w, (0, w) ∈ Δ ↔ w ∈ C') → (∀ w ∈ C, ∃ v, (v, w) ∈ Δ) → LocFree R (r + r₂) Δ ∧ LocFree R r (Δ.comap (AddMonoidHom.inl E E₂)) := by
  intro o Ω _ _ _ R E E₂ _ _ _ _ r r₂ L C C' Δ hL hC hC' hsm hsub hliftL hker hliftC
  have hC'eq : AddSubgroup.comap (LinearMap.inr Ω E E₂).toAddMonoidHom Δ = C' := by
    ext w
    change (0, w) ∈ Δ ↔ w ∈ C'
    exact hker w
  have hLeq : AddSubgroup.map (LinearMap.fst Ω E E₂).toAddMonoidHom Δ = L := by
    ext v
    constructor
    · rintro ⟨⟨v', w⟩, h, rfl⟩
      exact (hsub v' w h).1
    · intro hv
      obtain ⟨w, hw⟩ := hliftL v hv
      exact ⟨(v, w), hw, rfl⟩
  have hCeq : AddSubgroup.map (LinearMap.snd Ω E E₂).toAddMonoidHom Δ = C := by
    ext w
    constructor
    · rintro ⟨⟨v, w'⟩, h, rfl⟩
      exact (hsub v w' h).2
    · intro hw
      obtain ⟨v, hv⟩ := hliftC w hw
      exact ⟨(v, w), hv, rfl⟩
  have hΔ : LocFree R (r + r₂) Δ := by
    have h := GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt.main R (LinearMap.inr Ω E E₂) (LinearMap.fst Ω E E₂)
      LinearMap.inr_injective LinearMap.fst_surjective
      (LinearMap.range_inr (R := Ω) (M := E) (M₂ := E₂)) Δ r₂ r hsm
      (by rw [hC'eq]; exact hC') (by rw [hLeq]; exact hL)
    rwa [Nat.add_comm] at h
  refine ⟨hΔ, ?_⟩
  have h := GlobalTheory.T.locally_free_of_short_exact R (LinearMap.inl Ω E E₂) (LinearMap.snd Ω E E₂)
    LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl (R := Ω) (M := E) (M₂ := E₂)) Δ r r₂ hΔ (by rw [hCeq]; exact hC)
  have he : (LinearMap.inl Ω E E₂).toAddMonoidHom = AddMonoidHom.inl E E₂ := by
    ext x <;> simp
  rw [he] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel
