import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

namespace FilPhi

variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

/- English proof (translation)
Distinguish the cases in `h : ∀ i, D' ⊓ F.Dl i = ⊥`. Use `left`. Rewrite using `[hD.2]`. Simplify using `[h]`. Use `right push Not at h`.

Take `⟨i, hi⟩` from `h`. Establish `key : ∀ j, F.Dl j ≤ D' → F.Dl (j + 1) ≤ D'`. Introduce `j hj`. Rewrite using `[← F.φ_Dl j]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `hD.1 x (hj hx)`. Establish `hi' : F.Dl i ≤ D'`. Establish `hle : D' ⊓ F.Dl i ≤ F.Dl i` using `inf_le_right`. Establish `h1 : finrank LL ↥(D' ⊓ F.Dl i) ≠ 0`. Rewrite using `[Ne, Submodule.finrank_eq_zero]`.

Conclude with `hi`. Establish `h2 : finrank LL ↥(D' ⊓ F.Dl i) ≤ finrank LL ↥(F.Dl i)` using `Submodule.finrank_mono hle`. Establish `heq : D' ⊓ F.Dl i = F.Dl i` using `Submodule.eq_of_le_of_finrank_eq hle (by rw [hl i] at h2 ⊢; omega)`. Rewrite using `[← heq]`. Conclude with `inf_le_left`.

Establish `hall : ∀ k : ℕ, F.Dl (i + k) ≤ D'`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hi'`. Consider the case `succ k ih`.

Use `key _ ih` as an intermediate fact. Rewrite `this` using `[add_assoc, ← Nat.cast_succ]`. Then use the resulting hypothesis. Establish `hj : ∀ j, F.Dl j ≤ D'`. Introduce `j`. Use `hall (j - i).val` as an intermediate fact.

Rewrite `this` using `[ZMod.natCast_zmod_val, add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[eq_top_iff, ← F.internal.submodule_iSup_eq_top]`. Conclude with `iSup_le hj`.
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
Establish `h0 : ∀ S : Submodule LL D, finrank LL ↥(S ⊓ ⊥) = 0` using `fun S => by`. Rewrite using `[Submodule.finrank_eq_zero]`. Conclude with `inf_bot_eq S`. Simplify using `[tH, tHw, mult, h0]`.
-/
theorem rankOne_tH_bot (F : FilPhi LL D n Emb) : F.tH ⊥ = 0 := by
  have h0 : ∀ S : Submodule LL D, finrank LL ↥(S ⊓ ⊥) = 0 := fun S => by
    rw [Submodule.finrank_eq_zero]; exact inf_bot_eq S
  simp [tH, tHw, mult, h0]

/- English proof (translation)
The claim follows from `LinearMap.det_eq_one_of_subsingleton _`.
-/
theorem rankOne_det_bot (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊥ : Submodule LL D), F.φ x ∈ (⊥ : Submodule LL D)) :
    LinearMap.det (F.φres ⊥ h) = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

/- English proof (translation)
Establish `hc : (F.φ : D →ₗ[LL] D) = (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).toLinearMap ∘ₗ F.φres ⊤ h ∘ₗ (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).symm.toLinearMap`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[hc, LinearMap.det_conj]`.
-/
theorem rankOne_det_top (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊤ : Submodule LL D), F.φ x ∈ (⊤ : Submodule LL D)) :
    LinearMap.det (F.φres ⊤ h) = LinearMap.det (F.φ : D →ₗ[LL] D) := by
  have hc : (F.φ : D →ₗ[LL] D) = (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).toLinearMap ∘ₗ
      F.φres ⊤ h ∘ₗ (Submodule.topEquiv : ↥(⊤ : Submodule LL D) ≃ₗ[LL] D).symm.toLinearMap := by
    ext x; rfl
  rw [hc, LinearMap.det_conj]

end FilPhi

/- English proof (translation)
Introduce `LL _ D _ _ _ n _ Emb _ F v hl`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `htop`. Use `⟨htop, fun D' h => ?_⟩` and prove the remaining obligations.

Break down `F.rankOne_isSub_bot_or_top hl D' h with rfl | rfl` into its components or cases. Unfold `FilPhi.NewtonAbove`. Rewrite using `[F.rankOne_tH_bot, F.rankOne_det_bot, AddValuation.map_one]`. Simplify using the standard rewrite rules. Unfold `FilPhi.NewtonAbove`.

Rewrite using `[F.rankOne_det_top]`. Conclude with `le_of_eq htop`.
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
