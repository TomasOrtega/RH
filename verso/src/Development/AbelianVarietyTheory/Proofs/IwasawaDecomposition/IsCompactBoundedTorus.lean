import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ hγ, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢`.

Establish `h` using `(valuation k).map_add (y - x) x`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `h.trans_lt (max_lt hy hx)`.
-/
theorem isOpen_setOf_valuation_lt_of_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans_lt (max_lt hy hx)

/- English proof (translation)
Introduce `k _ _ _ _ m R1 R2`. Establish `hS : IsCompact {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)}`. Rewrite using `[Units.isEmbedding_val₀.isCompact_iff]`. Establish `himg : (Units.val '' {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)}) = {y : k | valuation k y ≤ valuation k (R1 : k)} ∩ {y : k | valuation k (R2 : k) ≤ valuation k y}`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨hx.2, hx.1⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `hy : y ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at h2`. Conclude with `⟨Units.mk0 y hy, ⟨h2, h1⟩, rfl⟩`. Rewrite using `[himg]`. Use `(IsNonarchimedeanLocalField.isCompact_closedBall k _).inter_right ?_` and prove the remaining obligations.

Establish `hne : valuation k (R2 : k) ≠ 0` using `by simp`. Establish `ho` using `isOpen_setOf_valuation_lt_of_ne_zero (valuation k (R2 : k)) hne`. Establish `hc : {y : k | valuation k (R2 : k) ≤ valuation k y} = {y : k | valuation k y < valuation k (R2 : k)}ᶜ`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Rewrite using `[hc]`. Conclude with `ho.isClosed_compl`. Establish `: {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} = Set.pi Set.univ (fun _ => {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)})`. Use extensionality with `t`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => hS`.
-/
theorem isCompact_boundedTorus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (R1 R2 : kˣ), IsCompact {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} := by
  intro k _ _ _ _ m R1 R2
  have hS : IsCompact {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)} := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himg : (Units.val '' {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)})
        = {y : k | valuation k y ≤ valuation k (R1 : k)} ∩ {y : k | valuation k (R2 : k) ≤ valuation k y} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.2, hx.1⟩
      · rintro ⟨h1, h2⟩
        have hy : y ≠ 0 := by
          rintro rfl
          simp at h2
        exact ⟨Units.mk0 y hy, ⟨h2, h1⟩, rfl⟩
    rw [himg]
    refine (IsNonarchimedeanLocalField.isCompact_closedBall k _).inter_right ?_
    have hne : valuation k (R2 : k) ≠ 0 := by simp
    have ho := isOpen_setOf_valuation_lt_of_ne_zero (valuation k (R2 : k)) hne
    have hc : {y : k | valuation k (R2 : k) ≤ valuation k y} = {y : k | valuation k y < valuation k (R2 : k)}ᶜ := by
      ext y; simp
    rw [hc]
    exact ho.isClosed_compl
  have : {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)}
      = Set.pi Set.univ (fun _ => {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)}) := by
    ext t; simp
  rw [this]
  exact isCompact_univ_pi fun _ => hS

end GlobalTheory
