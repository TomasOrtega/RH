import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `g E _ _ U τ D hD h0 l hl`. Establish `hcov : ∀ (x : Fl g) (P : Pt E g), P ∈ cov U g → transl τ x P ∈ cov U g`. Introduce `x P hP`. Simplify `hP` using `[cov, transl]`. Establish `hz : ∀ P ∈ cov U g, D 0 P = 0`.

Introduce `P hP`. Establish `h` using `hD 0 (zero_mem _) 0 (zero_mem _) P hP`. Establish `ht : transl τ 0 P = P`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[transl, per, Matrix.vecMul, dotProduct]`. Rewrite `h` using `[add_zero, ht]`. Take the linear combination `-h`. Establish `hl' : l ∈ AddSubgroup.closure (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g)))` using `by first`. Consider the case `(rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hl)`.

Consider the case `(rw [← AddSubgroup.toIntSubmodule_closure] at hl; exact hl)`. Consider the case `(rw [← Submodule.toAddSubgroup_span_int] at hl; exact hl)`. Consider the case `exact (AddSubgroup.closure_eq_toAddSubgroup_span _).symm ▸ hl`. Establish `key` using `AddSubgroup.closure_induction (p := fun x _ => x ∈ stdLat g ∧ ∀ P ∈ cov U g, D x P = 0) (fun x hx => by`. Take `⟨i, rfl⟩` from `hx`.

Use `⟨Submodule.subset_span ⟨i, rfl⟩, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply]`. Conclude with `h0 i P hP)`. Use the proof step `⟨zero_mem _, hz⟩`. Use the proof step `(fun x y _ _ hx hy => ⟨add_mem hx.1 hy.1, fun P hP => by`.

Rewrite using `[hD x hx.1 y hy.1 P hP, hx.2 _ (hcov y P hP), hy.2 P hP, add_zero]⟩)`. Use the proof step `(fun x _ hx => ⟨neg_mem hx.1, fun P hP => by`. Establish `h` using `hD x hx.1 (-x) (neg_mem hx.1) P hP`. Rewrite `h` using `[add_neg_cancel, hz P hP, hx.2 _ (hcov (-x) P hP), zero_add]`. Conclude with `h.symm⟩)`.

Use the proof step `hl'`. Conclude with `key.2`.
-/
theorem cocycle_vanish_stdLat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (D : Fl g → Pt E g → ℂ), (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, D (l + l') P = D l (transl τ l' P) + D l' P) → (∀ i : Fin g ⊕ Fin g, ∀ P ∈ cov U g, D (Pi.single i (1 : ℝ)) P = 0) → ∀ l ∈ stdLat g, ∀ P ∈ cov U g, D l P = 0 := by
  intro g E _ _ U τ D hD h0 l hl
  have hcov : ∀ (x : Fl g) (P : Pt E g), P ∈ cov U g → transl τ x P ∈ cov U g := by
    intro x P hP
    simpa [cov, transl] using hP
  have hz : ∀ P ∈ cov U g, D 0 P = 0 := by
    intro P hP
    have h := hD 0 (zero_mem _) 0 (zero_mem _) P hP
    have ht : transl τ 0 P = P := by
      refine Prod.ext rfl ?_
      funext i
      simp [transl, per, Matrix.vecMul, dotProduct]
    rw [add_zero, ht] at h
    linear_combination -h
  have hl' : l ∈ AddSubgroup.closure (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g))) := by
    first
      | (rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hl)
      | (rw [← AddSubgroup.toIntSubmodule_closure] at hl; exact hl)
      | (rw [← Submodule.toAddSubgroup_span_int] at hl; exact hl)
      | exact (AddSubgroup.closure_eq_toAddSubgroup_span _).symm ▸ hl
  have key := AddSubgroup.closure_induction
    (p := fun x _ => x ∈ stdLat g ∧ ∀ P ∈ cov U g, D x P = 0)
    (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      refine ⟨Submodule.subset_span ⟨i, rfl⟩, fun P hP => ?_⟩
      rw [Pi.basisFun_apply]
      exact h0 i P hP)
    ⟨zero_mem _, hz⟩
    (fun x y _ _ hx hy => ⟨add_mem hx.1 hy.1, fun P hP => by
      rw [hD x hx.1 y hy.1 P hP, hx.2 _ (hcov y P hP), hy.2 P hP, add_zero]⟩)
    (fun x _ hx => ⟨neg_mem hx.1, fun P hP => by
      have h := hD x hx.1 (-x) (neg_mem hx.1) P hP
      rw [add_neg_cancel, hz P hP, hx.2 _ (hcov (-x) P hP), zero_add] at h
      exact h.symm⟩)
    hl'
  exact key.2

end GlobalTheory
