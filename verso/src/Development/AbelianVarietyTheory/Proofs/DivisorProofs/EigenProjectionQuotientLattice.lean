import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Use `set W : Submodule C (Fin h → C) := ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1 with hW`. Establish `hW' : W = ⨆ σ, ⨆ (_ : σ ≠ τ), eig C ρ σ`. Rewrite using `[hW, iSup_subtype]`. Establish `hc : IsCompl (eig C ρ τ) W`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hW']`. Conclude with `hind τ`. Rewrite using `[codisjoint_iff, hW', ← iSup_split_single (fun σ => eig C ρ σ) τ, hspan]`. Use `set π := Submodule.projectionOnto (eig C ρ τ) W hc with hπ`. Establish `key : ∀ (z : Fin h → C) (x : eig C ρ τ), (z - (x : Fin h → C) ∈ W) ↔ x = π z`.

Introduce `z x`. Rewrite using `[← Submodule.projectionOnto_apply_eq_zero_iff hc, map_sub, Submodule.projectionOnto_apply_left, sub_eq_zero, eq_comm]`. Use `⟨π, fun x => Submodule.projectionOnto_apply_left hc x, key, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, ht⟩`. Conclude with `⟨t, ((key _ x).1 ht).symm⟩`. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨t, (key _ _).2 rfl⟩`.
-/
theorem eig_projection_quotLattice (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O)
    (hind : iSupIndep (fun σ : Λ →+* O => eig C ρ σ))
    (hspan : (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤) :
    ∃ π : (Fin h → C) →ₗ[C] eig C ρ τ, (∀ x : eig C ρ τ, π x = x) ∧
      (∀ (z : Fin h → C) (x : eig C ρ τ),
        (z - (x : Fin h → C) ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ x = π z) ∧
      quotLattice C ρ τ = Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) := by
  set W : Submodule C (Fin h → C) := ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1 with hW
  have hW' : W = ⨆ σ, ⨆ (_ : σ ≠ τ), eig C ρ σ := by
    rw [hW, iSup_subtype]
  have hc : IsCompl (eig C ρ τ) W := by
    constructor
    · rw [hW']; exact hind τ
    · rw [codisjoint_iff, hW', ← iSup_split_single (fun σ => eig C ρ σ) τ, hspan]
  set π := Submodule.projectionOnto (eig C ρ τ) W hc with hπ
  have key : ∀ (z : Fin h → C) (x : eig C ρ τ), (z - (x : Fin h → C) ∈ W) ↔ x = π z := by
    intro z x
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hc, map_sub,
      Submodule.projectionOnto_apply_left, sub_eq_zero, eq_comm]
  refine ⟨π, fun x => Submodule.projectionOnto_apply_left hc x, key, ?_⟩
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ((key _ x).1 ht).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, (key _ _).2 rfl⟩

end GlobalTheory
