import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `k H _ _ _ _ C hC`. Establish `key : ∀ D : Submodule k H, Module.finrank k D = Module.finrank k (Submodule.map C.mkQ D) + Module.finrank k ↥(D ⊓ C)`. Introduce `D`. Establish `h` using `(C.mkQ.domRestrict D).finrank_range_add_finrank_ker`. Rewrite `h` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ]`.

Rewrite using `[← h, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨D₁, h₁⟩ ⟨D₂, h₂⟩ h`. Simplify using `only at h`. Establish `e₁` using `Submodule.comap_map_mkQ C D₁`.

Establish `e₂` using `Submodule.comap_map_mkQ C D₂`. Rewrite `e₁` using `[h, e₂, sup_eq_right.mpr h₂]`. Rewrite `e₁` using `[sup_eq_right.mpr h₁]`. Conclude with `Subtype.ext e₁.symm`. Introduce `E`.

Use `⟨⟨Submodule.comap C.mkQ E, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `[Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero C).mpr hx]`. Conclude with `Submodule.map_comap_eq_self (by simp [Submodule.range_mkQ])`. Introduce `D hD`.

Rewrite using `[key D, inf_eq_right.mpr hD, hC]`. Introduce `D hD`. Establish `hle : Module.finrank k ↥(D ⊓ C) ≤ 1` using `hC ▸ Submodule.finrank_mono inf_le_right`. Establish `hne : Module.finrank k ↥(D ⊓ C) ≠ 1`. Introduce `h1`.

Apply `hD` to reduce the goal to its premises. Use `Submodule.eq_of_le_of_finrank_eq (inf_le_right : D ⊓ C ≤ C) (h1.trans hC.symm)` as an intermediate fact. Conclude with `this ▸ inf_le_left`. Rewrite using `[key D]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.crystallineComparison.countIn_of :
    CountIn := by
  intro k H _ _ _ _ C hC
  have key : ∀ D : Submodule k H, Module.finrank k D
      = Module.finrank k (Submodule.map C.mkQ D) + Module.finrank k ↥(D ⊓ C) := by
    intro D
    have h := (C.mkQ.domRestrict D).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
    rw [← h, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨D₁, h₁⟩ ⟨D₂, h₂⟩ h
    simp only at h
    have e₁ := Submodule.comap_map_mkQ C D₁
    have e₂ := Submodule.comap_map_mkQ C D₂
    rw [h, e₂, sup_eq_right.mpr h₂] at e₁
    rw [sup_eq_right.mpr h₁] at e₁
    exact Subtype.ext e₁.symm
  · intro E
    refine ⟨⟨Submodule.comap C.mkQ E, ?_⟩, ?_⟩
    · intro x hx
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero C).mpr hx]
    · exact Submodule.map_comap_eq_self (by simp [Submodule.range_mkQ])
  · intro D hD
    rw [key D, inf_eq_right.mpr hD, hC]
  · intro D hD
    have hle : Module.finrank k ↥(D ⊓ C) ≤ 1 := hC ▸ Submodule.finrank_mono inf_le_right
    have hne : Module.finrank k ↥(D ⊓ C) ≠ 1 := by
      intro h1
      apply hD
      have := Submodule.eq_of_le_of_finrank_eq (inf_le_right : D ⊓ C ≤ C) (h1.trans hC.symm)
      exact this ▸ inf_le_left
    rw [key D]
    omega
