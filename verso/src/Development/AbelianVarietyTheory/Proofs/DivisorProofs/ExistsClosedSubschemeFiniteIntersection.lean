import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem closedSubscheme_iInter_exists :
    ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  intro H Idx _ Z i hi
  revert Z i hi
  refine Finite.induction_empty_option
    (P := fun (α : Type) => ∀ (Z : α → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h)
    ?_ ?_ ?_ Idx
  · intro α β e ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (e a)) (fun a => i (e a)) (fun a => hi (e a))
    refine ⟨Z₀, i₀, h₀, fun T h => (hp T h).trans ?_⟩
    exact e.forall_congr_right (q := fun k => ∃ z, z ≫ i k = h)
  · intro Z i _
    refine ⟨H, 𝟙 H, inferInstance, fun T h => ⟨fun _ k => k.elim, fun _ => ⟨h, Category.comp_id h⟩⟩⟩
  · intro α _ ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (some a)) (fun a => i (some a)) (fun a => hi (some a))
    haveI := h₀
    haveI := hi none
    refine ⟨Limits.pullback i₀ (i none), Limits.pullback.fst i₀ (i none) ≫ i₀, inferInstance, ?_⟩
    intro T h
    rw [Option.forall, ← hp T h]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨z ≫ Limits.pullback.snd _ _, ?_⟩, ⟨z ≫ Limits.pullback.fst _ _, ?_⟩⟩
      · rw [Category.assoc, ← Limits.pullback.condition]
      · rfl
    · rintro ⟨⟨z₂, h₂⟩, ⟨z₁, h₁⟩⟩
      exact ⟨Limits.pullback.lift z₁ z₂ (h₁.trans h₂.symm), by rw [Limits.pullback.lift_fst_assoc, h₁]⟩

end GlobalTheory
