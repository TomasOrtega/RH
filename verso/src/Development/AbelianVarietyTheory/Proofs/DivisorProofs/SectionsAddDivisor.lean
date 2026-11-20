import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffineStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

namespace GlobalTheory.Cartier.SecAdd

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
The claim follows from `Submodule.mul_le.2 fun _ hm _ hn => mem_sections.2 fun x => (mem_sections.1 hm x).mul (mem_sections.1 hn x)`.
-/
theorem mul_le_sections_add (D E : CartierDiv X) :
    D.sections * E.sections ≤ (D + E).sections :=
  Submodule.mul_le.2 fun _ hm _ hn => mem_sections.2 fun x =>
    (mem_sections.1 hm x).mul (mem_sections.1 hn x)

/- English proof (translation)
Use `le_antisymm (fun h hh => ?_) (mul_le_sections_add D E)` and prove the remaining obligations. Set `𝔞 : Ideal Γ(X, ⊤)` to `(D.sections * E.sections).comap (LinearMap.toSpanSingleton _ _ h)`. Establish `mem𝔞 (a : Γ(X, ⊤)) : a ∈ 𝔞 ↔ a • h ∈ D.sections * E.sections` using `Iff.rfl`. Establish `cover : ∀ x : X, ∃ a ∈ 𝔞, x ∈ X.basicOpen a`. Introduce `x`.

Take `⟨g, hg⟩` from `D.exists_isEqn x`. Take `⟨g', hg'⟩` from `E.exists_isEqn x`. Establish `hreg : RegAt x (h * ((g * g' : X.functionFieldˣ) : X.functionField))` using `(hg.add hg').regularAt_iff.1 (mem_sections.1 hh x)`. Take `⟨s, hs, hsD⟩` from `hloc D x g hg ((g : X.functionField)⁻¹) (by`. Rewrite using `[inv_mul_cancel₀ g.ne_zero]`.

Conclude with `(unitAt_one x).regAt)`. Take `⟨s', hs', hsE⟩` from `hloc E x g' hg' (h * g) (by`. Rewrite `hreg` using `[Units.val_mul, ← mul_assoc]`. Conclude with `hreg)`. Use `⟨s * s', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem𝔞]`. Establish `e : (s * s') • h = (s • (g : X.functionField)⁻¹) * (s' • (h * g))`. Rewrite using `[smul_mul_smul_comm]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `Submodule.mul_mem_mul hsD hsE`. Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `⟨hs, hs'⟩`. Establish `htop : 𝔞 = ⊤`.

Rewrite using `[← Ideal.span_eq 𝔞, ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff, eq_top_iff]`. Introduce `x _`. Take `⟨a, ha, hx⟩` from `cover x`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hx⟩`. Establish `h1 : (1 : Γ(X, ⊤)) ∈ 𝔞` using `htop ▸ Submodule.mem_top`.

Rewrite `h1` using `[mem𝔞, one_smul]`. Conclude with `h1`.
-/
theorem sections_add_of_loc [IsAffine X]
    (hloc : ∀ (D : CartierDiv X) (x : X) (g : X.functionFieldˣ), D.IsEqn x g →
      ∀ f : X.functionField, RegAt x (f * g) →
        ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ s • f ∈ D.sections)
    (D E : CartierDiv X) : (D + E).sections = D.sections * E.sections := by
  refine le_antisymm (fun h hh => ?_) (mul_le_sections_add D E)
  let 𝔞 : Ideal Γ(X, ⊤) := (D.sections * E.sections).comap (LinearMap.toSpanSingleton _ _ h)
  have mem𝔞 (a : Γ(X, ⊤)) : a ∈ 𝔞 ↔ a • h ∈ D.sections * E.sections := Iff.rfl
  have cover : ∀ x : X, ∃ a ∈ 𝔞, x ∈ X.basicOpen a := by
    intro x
    obtain ⟨g, hg⟩ := D.exists_isEqn x
    obtain ⟨g', hg'⟩ := E.exists_isEqn x
    have hreg : RegAt x (h * ((g * g' : X.functionFieldˣ) : X.functionField)) :=
      (hg.add hg').regularAt_iff.1 (mem_sections.1 hh x)
    obtain ⟨s, hs, hsD⟩ := hloc D x g hg ((g : X.functionField)⁻¹) (by
      rw [inv_mul_cancel₀ g.ne_zero]; exact (unitAt_one x).regAt)
    obtain ⟨s', hs', hsE⟩ := hloc E x g' hg' (h * g) (by
      rw [Units.val_mul, ← mul_assoc] at hreg; exact hreg)
    refine ⟨s * s', ?_, ?_⟩
    · rw [mem𝔞]
      have e : (s * s') • h = (s • (g : X.functionField)⁻¹) * (s' • (h * g)) := by
        rw [smul_mul_smul_comm]
        congr 1
        field_simp
      rw [e]
      exact Submodule.mul_mem_mul hsD hsE
    · rw [Scheme.basicOpen_mul]
      exact ⟨hs, hs'⟩
  have htop : 𝔞 = ⊤ := by
    rw [← Ideal.span_eq 𝔞, ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff, eq_top_iff]
    intro x _
    obtain ⟨a, ha, hx⟩ := cover x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hx⟩
  have h1 : (1 : Γ(X, ⊤)) ∈ 𝔞 := htop ▸ Submodule.mem_top
  rw [mem𝔞, one_smul] at h1
  exact h1

end GlobalTheory.Cartier.SecAdd

namespace GlobalTheory.Cartier.SecAdd

/- English proof (translation)
Introduce `X _ _ D E`. Conclude with `sections_add_of_loc (fun D x g hg f hf => GlobalTheory.T.sections_locally_generated_affine X D x g hg f hf) D E`.
-/
theorem sections_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D E : CartierDiv X),
    (D + E).sections = D.sections * E.sections := by
  intro X _ _ D E
  exact sections_add_of_loc (fun D x g hg f hf => GlobalTheory.T.sections_locally_generated_affine X D x g hg f hf) D E

end GlobalTheory.Cartier.SecAdd
