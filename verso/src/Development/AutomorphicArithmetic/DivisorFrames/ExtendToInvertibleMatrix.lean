import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `A _ _ n g v s h`. Establish `h' : IsUnit (Matrix.of fun l i => v l (s i) : Matrix (Fin n) (Fin n) A).det` using `h`. Establish `hs : Function.Injective s`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`.

Establish `: (Matrix.of fun l i => v l (s i) : Matrix (Fin n) (Fin n) A).det = 0` using `Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])`. Rewrite `h'` using `[this]`. Conclude with `not_isUnit_zero h'`. Set `E : Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s} ≃ Fin g` to `(Equiv.sumCongr (Equiv.ofInjective s hs) (Equiv.refl _)).trans (Equiv.sumCompl (fun x => x ∈ Set.range s))`. Establish `hE : ∀ m, E (Sum.inl m) = s m` using `fun m => rfl`.

Set `C : Matrix (Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s}) (Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s}) A` to `Matrix.fromBlocks (Matrix.of fun l i => v l (s i)) (Matrix.of fun l i => v l i.1) 0 1`. Use `⟨⟨s, hs⟩, Matrix.reindex E E C, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`. Conclude with `h'`. Introduce `m`.

Use function extensionality and compare the values at `j`. Take `⟨k, rfl⟩` from `E.surjective j`. Establish `h1 : (Matrix.reindex E E C) (E (Sum.inl m)) (E k) = C (Sum.inl m) k`. Simplify using `[Matrix.reindex_apply]`. Express the relevant statement in the definitionally equal form `(Matrix.reindex E E C) (E (Sum.inl m)) (E k) = _`.

Rewrite using `[h1]`. Consider the cases of `k with`. Consider the case `inl k => rfl`. Consider the case `inr k => rfl`.
-/
theorem UpperTheory.extend_to_invertible_matrix :
    ∀ (A : Type) [CommRing A] [Nontrivial A] (n g : ℕ) (v : Fin n → Fin g → A) (s : Fin n → Fin g), IsUnit (minor v le_rfl s) → ∃ (e : Fin n ↪ Fin g) (B : Matrix (Fin g) (Fin g) A), IsUnit B.det ∧ ∀ m, B (e m) = v m := by
  intro A _ _ n g v s h
  classical
  have h' : IsUnit (Matrix.of fun l i => v l (s i) : Matrix (Fin n) (Fin n) A).det := h
  have hs : Function.Injective s := by
    intro i j hij
    by_contra hne
    have : (Matrix.of fun l i => v l (s i) : Matrix (Fin n) (Fin n) A).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])
    rw [this] at h'
    exact not_isUnit_zero h'
  let E : Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s} ≃ Fin g :=
    (Equiv.sumCongr (Equiv.ofInjective s hs) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun x => x ∈ Set.range s))
  have hE : ∀ m, E (Sum.inl m) = s m := fun m => rfl
  let C : Matrix (Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s})
      (Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s}) A :=
    Matrix.fromBlocks (Matrix.of fun l i => v l (s i)) (Matrix.of fun l i => v l i.1) 0 1
  refine ⟨⟨s, hs⟩, Matrix.reindex E E C, ?_, ?_⟩
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    exact h'
  · intro m
    funext j
    obtain ⟨k, rfl⟩ := E.surjective j
    have h1 : (Matrix.reindex E E C) (E (Sum.inl m)) (E k) = C (Sum.inl m) k := by
      simp [Matrix.reindex_apply]
    change (Matrix.reindex E E C) (E (Sum.inl m)) (E k) = _
    rw [h1]
    cases k with
    | inl k => rfl
    | inr k => rfl
