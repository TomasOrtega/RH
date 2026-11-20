import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ O _ _ Λ _ h ρ hind htop`. Establish `hfin : {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite` using `WellFoundedGT.finite_ne_bot_of_iSupIndep hind`. Use `⟨hfin, fun S hS a => ?_⟩` and prove the remaining obligations. Use `set f : (Fin h → C) →ₗ[C] (Fin h → C) := Matrix.toLin' ((ρ a).map (algebraMap O C)) with hf`. Establish `hact : ∀ (σ : Λ →+* O) (x : Fin h → C), x ∈ eig C ρ σ → f x = algebraMap O C (σ a) • x`.

Introduce `σ x hx`. Establish `h1` using `(Submodule.mem_iInf _).1 hx a`. Conclude with `Module.End.mem_eigenspace_iff.1 h1`. Establish `hmaps : ∀ σ : Λ →+* O, Set.MapsTo f (eig C ρ σ) (eig C ρ σ)`. Introduce `σ x hx`.

Establish `hx' : x ∈ eig C ρ σ` using `hx`. Use `show f x ∈ eig C ρ σ`. Rewrite using `[hact σ x hx']`. Conclude with `Submodule.smul_mem _ _ hx'`. Establish `hint : DirectSum.IsInternal (fun σ : Λ →+* O => eig C ρ σ)` using `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop`.

Establish `htr` using `LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps`. Establish `hrestrict : ∀ σ : Λ →+* O, LinearMap.trace C (eig C ρ σ) (f.restrict (hmaps σ)) = (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a)`. Introduce `σ`. Establish `: f.restrict (hmaps σ) = algebraMap O C (σ a) • LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show f x.1 = algebraMap O C (σ a) • x.1`. Conclude with `hact σ x.1 x.2`. Rewrite using `[this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]`.

Establish `hleft : algebraMap O C (ρ a).trace = LinearMap.trace C (Fin h → C) f`. Rewrite using `[hf, Matrix.trace_toLin'_eq, Matrix.trace, Matrix.trace, map_sum]`. Both sides reduce to the same expression. Rewrite using `[hleft, htr]`. Simplify using `only [hrestrict]`.

Use `Finset.sum_subset (fun σ hσ => hS σ (by simpa using hσ)) ?_` and prove the remaining obligations. Introduce `σ _ hσ`. Establish `hbot : eig C ρ σ = ⊥`. Assume the negation of the conclusion as `hne`. Conclude with `hσ (by simpa using hne)`.

Rewrite using `[hbot]`. Simplify using the standard rewrite rules.
-/
theorem trace_eq_sum_eigenspaces : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite ∧ ∀ S : Finset (Λ →+* O), (∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S) → ∀ a : Λ, algebraMap O C (ρ a).trace = ∑ σ ∈ S, (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
  classical
  intro C _ O _ _ Λ _ h ρ hind htop
  have hfin : {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin, fun S hS a => ?_⟩
  set f : (Fin h → C) →ₗ[C] (Fin h → C) := Matrix.toLin' ((ρ a).map (algebraMap O C)) with hf
  have hact : ∀ (σ : Λ →+* O) (x : Fin h → C), x ∈ eig C ρ σ → f x = algebraMap O C (σ a) • x := by
    intro σ x hx
    have h1 := (Submodule.mem_iInf _).1 hx a
    exact Module.End.mem_eigenspace_iff.1 h1
  have hmaps : ∀ σ : Λ →+* O, Set.MapsTo f (eig C ρ σ) (eig C ρ σ) := by
    intro σ x hx
    have hx' : x ∈ eig C ρ σ := hx
    show f x ∈ eig C ρ σ
    rw [hact σ x hx']
    exact Submodule.smul_mem _ _ hx'
  have hint : DirectSum.IsInternal (fun σ : Λ →+* O => eig C ρ σ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr := LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps
  have hrestrict : ∀ σ : Λ →+* O, LinearMap.trace C (eig C ρ σ) (f.restrict (hmaps σ))
      = (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
    intro σ
    have : f.restrict (hmaps σ) = algebraMap O C (σ a) • LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      show f x.1 = algebraMap O C (σ a) • x.1
      exact hact σ x.1 x.2
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  have hleft : algebraMap O C (ρ a).trace = LinearMap.trace C (Fin h → C) f := by
    rw [hf, Matrix.trace_toLin'_eq, Matrix.trace, Matrix.trace, map_sum]
    rfl
  rw [hleft, htr]
  simp only [hrestrict]
  refine Finset.sum_subset (fun σ hσ => hS σ (by simpa using hσ)) ?_
  intro σ _ hσ
  have hbot : eig C ρ σ = ⊥ := by
    by_contra hne
    exact hσ (by simpa using hne)
  rw [hbot]
  simp

end GlobalTheory
