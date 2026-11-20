import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n A E _ _ _ D x M hM H B _ _ h`. Establish `key : ∀ e : E, ((1 : B) ⊗ₜ[A] e) ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M)`. Introduce `e`. Establish `he : e ∈ Submodule.span A M` using `hM ▸ Submodule.mem_top`. Proceed by induction on `he using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [tmul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul a y _ hy`.

Rewrite using `[tmul_smul, ← algebraMap_smul B]`. Conclude with `Submodule.smul_mem _ _ hy`. Establish `hh : h ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M)`. Proceed by induction on `h with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => exact add_mem ha hb`. Consider the case `tmul b e`. Establish `: b ⊗ₜ[A] e = b • ((1 : B) ⊗ₜ[A] e)` using `by simp [smul_tmul']`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (key e)`.

Take `⟨k, f, g, rfl⟩` from `Submodule.mem_span_set'.1 hh`. Use `choose m hm hmg using fun i => (g i).2`. Establish `h1` using `D.nat _ B (MvPolynomial.aeval f) (1 + Det.gen m * (1 ⊗ₜ x))`. Rewrite `h1` using `[H k m hm, map_one]`. Use `Eq.trans (congrArg _ ?_) h1` and prove the remaining obligations.

Simplify using `only [Det.gen, map_add, map_mul, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X, AlgHom.id_apply, ← hmg, smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem UpperTheory.V.CA.d_kills_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (h : Fin k → E), (∀ a, h a ∈ M) → D.D (MvPolynomial (Fin k) A) (1 + Det.gen h * (1 ⊗ₜ x)) = 1) → D.Kills x := by
  intro n A E _ _ _ D x M hM H B _ _ h
  have key : ∀ e : E, ((1 : B) ⊗ₜ[A] e) ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    intro e
    have he : e ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a y _ hy =>
      rw [tmul_smul, ← algebraMap_smul B]
      exact Submodule.smul_mem _ _ hy
  have hh : h ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    induction h with
    | zero => simp
    | add a b ha hb => exact add_mem ha hb
    | tmul b e =>
      have : b ⊗ₜ[A] e = b • ((1 : B) ⊗ₜ[A] e) := by simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key e)
  obtain ⟨k, f, g, rfl⟩ := Submodule.mem_span_set'.1 hh
  choose m hm hmg using fun i => (g i).2
  have h1 := D.nat _ B (MvPolynomial.aeval f) (1 + Det.gen m * (1 ⊗ₜ x))
  rw [H k m hm, map_one] at h1
  refine Eq.trans (congrArg _ ?_) h1
  simp only [Det.gen, map_add, map_mul, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
    AlgHom.id_apply, ← hmg, smul_tmul', smul_eq_mul, mul_one]
