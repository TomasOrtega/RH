import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Introduce `S S' f h`. Use `haveI : ∀ n : SimplexCategoryᵒᵖ, IsIso (f.app n) := by`. Introduce `n`. Use `haveI : ∀ T : Schemeᵒᵖ, IsIso ((f.app n).app T) := by`. Introduce `T`.

Take `⟨⟨k⟩⟩` from `n`. Take `⟨T⟩` from `T`. Rewrite using `[isIso_iff_bijective]`. Conclude with `h k T`. Conclude with `NatIso.isIso_of_isIso_app _`.

Conclude with `NatIso.isIso_of_isIso_app _`.
-/
theorem UpperTheory.isIso_of_bijective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Bijective (fun x : Sx S k T => x.map f)) → IsIso f := by
  intro S S' f h
  haveI : ∀ n : SimplexCategoryᵒᵖ, IsIso (f.app n) := by
    intro n
    haveI : ∀ T : Schemeᵒᵖ, IsIso ((f.app n).app T) := by
      intro T
      obtain ⟨⟨k⟩⟩ := n
      obtain ⟨T⟩ := T
      rw [isIso_iff_bijective]
      exact h k T
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _
