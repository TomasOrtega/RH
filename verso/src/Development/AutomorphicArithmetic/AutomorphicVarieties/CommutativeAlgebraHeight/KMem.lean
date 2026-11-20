import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n A E _ _ _ D x`. Establish `key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)), Algebra.TensorProduct.lid A E w ∈ D.CH`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨z, hz, rfl⟩` from `hy`. Simplify using `using hz`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul a y _ hy => rw [map_smul, Algebra.smul_def]`. Conclude with `TwoSidedIdeal.mul_mem_left _ _ _ hy`. Establish `h1` using `(d_chS D A).1 (1 ⊗ₜ x)`. Establish `h2 : D.chiS A (1 ⊗ₜ x) = D.chi x` using `by simp [Det.chiS, Det.chi]`. Rewrite `h1` using `[h2]`.

Establish `h3` using `key _ h1`. Rewrite `h3` using `[← Polynomial.aeval_algHom_apply]`. Simplify using `using h3`.
-/
theorem UpperTheory.V.CA.k_mem :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), Polynomial.aeval x (D.chi x) ∈ D.CH := by
  intro n A E _ _ _ D x
  have key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)),
      Algebra.TensorProduct.lid A E w ∈ D.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a y _ hy => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hy
  have h1 := (d_chS D A).1 (1 ⊗ₜ x)
  have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
  rw [h2] at h1
  have h3 := key _ h1
  rw [← Polynomial.aeval_algHom_apply] at h3
  simpa using h3
