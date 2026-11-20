import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.isPullback_of_unique_simplices_pullback :
    ∀ {P A B C : Spc} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (u : B ⟶ C), t ≫ r = l ≫ u →
        (∀ (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u → ∃! z : Sx P k T, z.map t = x ∧ z.map l = y) →
        IsPullback t l r u := by
  intro P A B C t l r u hw h
  refine IsPullback.of_forall_isPullback_app (fun n => ?_)
  refine IsPullback.of_forall_isPullback_app (fun T => ?_)
  obtain ⟨⟨k⟩⟩ := n
  obtain ⟨T⟩ := T
  have hw' : ∀ x : Sx P k T, Sx.map r (Sx.map t x) = Sx.map u (Sx.map l x) := by
    intro x
    have := congrArg (fun f : P ⟶ C => (f.app (op ⟨k⟩)).app (op T) x) hw
    simpa [Sx.map] using this
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact hw' x
  · rintro x y ⟨h1, h2⟩
    obtain ⟨z, -, hz⟩ := h k T (Sx.map t (x : Sx P k T)) (Sx.map l (x : Sx P k T)) (hw' x)
    have hx := hz x ⟨rfl, rfl⟩
    have hy := hz y ⟨h1.symm, h2.symm⟩
    exact hx.trans hy.symm
  · intro a b hab
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := h k T a b hab
    exact ⟨z, h1, h2⟩
