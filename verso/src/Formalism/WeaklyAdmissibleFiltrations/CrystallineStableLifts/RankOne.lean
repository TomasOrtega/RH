import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

namespace FilPhi

variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rankOne_isSub_bot_or_top [NeZero n] (F : FilPhi LL D n Emb)
    (hl : ∀ i, finrank LL ↥(F.Dl i) = 1) (D' : Submodule LL D) (hD : F.IsSub D') :
    D' = ⊥ ∨ D' = ⊤ := by
  by_cases h : ∀ i, D' ⊓ F.Dl i = ⊥
  · left
    rw [hD.2]
    simp [h]
  · right
    push Not at h
    obtain ⟨i, hi⟩ := h
    have key : ∀ j, F.Dl j ≤ D' → F.Dl (j + 1) ≤ D' := by
      intro j hj
      rw [← F.φ_Dl j]
      rintro _ ⟨x, hx, rfl⟩
      exact hD.1 x (hj hx)
    have hi' : F.Dl i ≤ D' := by
      have hle : D' ⊓ F.Dl i ≤ F.Dl i := inf_le_right
      have h1 : finrank LL ↥(D' ⊓ F.Dl i) ≠ 0 := by
        rw [Ne, Submodule.finrank_eq_zero]; exact hi
      have h2 : finrank LL ↥(D' ⊓ F.Dl i) ≤ finrank LL ↥(F.Dl i) := Submodule.finrank_mono hle
      have heq : D' ⊓ F.Dl i = F.Dl i :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hl i] at h2 ⊢; omega)
      rw [← heq]; exact inf_le_left
    have hall : ∀ k : ℕ, F.Dl (i + k) ≤ D' := by
      intro k
      induction k with
      | zero => simpa using hi'
      | succ k ih =>
        have := key _ ih
        rwa [add_assoc, ← Nat.cast_succ] at this
    have hj : ∀ j, F.Dl j ≤ D' := by
      intro j
      have := hall (j - i).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    rw [eq_top_iff, ← F.internal.submodule_iSup_eq_top]
    exact iSup_le hj

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rankOne_tH_bot (F : FilPhi LL D n Emb) : F.tH ⊥ = 0 := by
  have h0 : ∀ S : Submodule LL D, finrank LL ↥(S ⊓ ⊥) = 0 := fun S => by
    rw [Submodule.finrank_eq_zero]; exact inf_bot_eq S
  simp [tH, tHw, mult, h0]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rankOne_det_bot (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊥ : Submodule LL D), F.φ x ∈ (⊥ : Submodule LL D)) :
    LinearMap.det (F.φres ⊥ h) = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem rankOne_det_top (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊤ : Submodule LL D), F.φ x ∈ (⊤ : Submodule LL D)) :
    LinearMap.det (F.φres ⊤ h) = LinearMap.det (F.φ : D →ₗ[LL] D) := by
  have hc : (F.φ : D →ₗ[LL] D) = (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).toLinearMap ∘ₗ
      F.φres ⊤ h ∘ₗ (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).symm.toLinearMap := by
    ext x; rfl
  rw [hc, LinearMap.det_conj]

end FilPhi

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rankOneWA : RankOneWA := by
  intro LL _ D _ _ _ n _ Emb _ F v hl
  constructor
  · exact fun h => h.1
  · intro htop
    refine ⟨htop, fun D' h => ?_⟩
    rcases F.rankOne_isSub_bot_or_top hl D' h with rfl | rfl
    · unfold FilPhi.NewtonAbove
      rw [F.rankOne_tH_bot, F.rankOne_det_bot, AddValuation.map_one]
      simp
    · unfold FilPhi.NewtonAbove
      rw [F.rankOne_det_top]
      exact le_of_eq htop

end Formalism.WeaklyAdmissibleFiltrations
