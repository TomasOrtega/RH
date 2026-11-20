import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `H Idx _ Z i hi`. Use `revert Z i hi`. Use `Finite.induction_empty_option (P := fun (α : Type) => ∀ (Z : α → Scheme.{0}) (i : ∀ k, Z k ⟶ H), (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h) ?_ ?_ ?_ Idx` and prove the remaining obligations. Introduce `α β e ih Z i hi`. Take `⟨Z₀, i₀, h₀, hp⟩` from `ih (fun a => Z (e a)) (fun a => i (e a)) (fun a => hi (e a))`.

Use `⟨Z₀, i₀, h₀, fun T h => (hp T h).trans ?_⟩` and prove the remaining obligations. Conclude with `e.forall_congr_right (q := fun k => ∃ z, z ≫ i k = h)`. Introduce `Z i _`. Use `⟨H, 𝟙 H, inferInstance, fun T h => ⟨fun _ k => k.elim, fun _ => ⟨h, Category.comp_id h⟩⟩⟩` and prove the remaining obligations. Introduce `α _ ih Z i hi`.

Take `⟨Z₀, i₀, h₀, hp⟩` from `ih (fun a => Z (some a)) (fun a => i (some a)) (fun a => hi (some a))`. Use `haveI := h₀`. Use `haveI := hi none`. Use `⟨Limits.pullback i₀ (i none), Limits.pullback.fst i₀ (i none) ≫ i₀, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `T h`.

Rewrite using `[Option.forall, ← hp T h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Use `⟨⟨z ≫ Limits.pullback.snd _ _, ?_⟩, ⟨z ≫ Limits.pullback.fst _ _, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Limits.pullback.condition]`.

Both sides reduce to the same expression. Introduce and unpack `⟨⟨z₂, h₂⟩, ⟨z₁, h₁⟩⟩`. Conclude with `⟨Limits.pullback.lift z₁ z₂ (h₁.trans h₂.symm), by rw [Limits.pullback.lift_fst_assoc, h₁]⟩`.
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
