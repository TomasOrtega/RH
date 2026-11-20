import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

/- English proof (translation)
Introduce `A B _ _ i σ N hi hσ`. Establish `hmem : ∀ g : GL (Fin N) A, Matrix.GeneralLinearGroup.map (n` using `Fin N) i g ∈ (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) := by`. Introduce `g`. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map (n := Fin N) σ (Matrix.GeneralLinearGroup.map (n := Fin N) i g) = Matrix.GeneralLinearGroup.map (n := Fin N) i g`. Use extensionality with `a b`.

Conclude with `(hσ _).2 ⟨g a b, rfl⟩`. Establish `hM : ∀ X Y : Matrix (Fin N) (Fin N) A, X.map i = Y.map i → X = Y`. Introduce `X Y h`. Use extensionality with `a b`. Conclude with `hi (congrFun (congrFun h a) b)`.

Establish `hpre : ∀ g : GL (Fin N) B, g ∈ (Matrix.GeneralLinearGroup.map (n` using `Fin N) σ).eqLocus (MonoidHom.id _) → ∃ X : Matrix (Fin N) (Fin N) A, X.map i = (g : Matrix (Fin N) (Fin N) B) := by`. Introduce `g hg`. Establish `hg' : Matrix.GeneralLinearGroup.map (n` using `Fin N) σ g = g := hg`. Establish `h1 : ∀ a b, ∃ x : A, i x = (g : Matrix (Fin N) (Fin N) B) a b`. Introduce `a b`.

Use `(hσ _).1 ?_` and prove the remaining obligations. Use `congrArg (fun k : GL (Fin N) B => (k : Matrix (Fin N) (Fin N) B) a b) hg'` as an intermediate fact. Conclude with `this`. Use `choose X hX using h1`. Conclude with `⟨Matrix.of X, by ext a b; exact hX a b⟩`.

Use `⟨(MulEquiv.ofBijective ((Matrix.GeneralLinearGroup.map (n := Fin N) i).codRestrict _ hmem) ⟨?_, ?_⟩).symm⟩` and prove the remaining obligations. Introduce `g k h`. Establish `h1 : Matrix.GeneralLinearGroup.map (n` using `Fin N) i g = Matrix.GeneralLinearGroup.map (n := Fin N) i k := congrArg Subtype.val h`. Apply `Units.ext` to reduce the goal to its premises. Apply `hM` to reduce the goal to its premises.

Conclude with `congrArg Units.val h1`. Introduce and unpack `⟨g, hg⟩`. Take `⟨X, hX⟩` from `hpre g hg`. Take `⟨Y, hY⟩` from `hpre g⁻¹ (inv_mem hg)`. Use `⟨⟨X, Y, hM _ _ ?_, hM _ _ ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]`. Conclude with `g.mul_inv`. Rewrite using `[Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]`. Conclude with `g.inv_mul`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `hX`.
-/
theorem UpperTheory.building_fixed_points_equiv :
    UpperTheory.V.Af.BA.FixEquiv := by
  intro A B _ _ i σ N hi hσ
  have hmem : ∀ g : GL (Fin N) A, Matrix.GeneralLinearGroup.map (n := Fin N) i g ∈
      (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) := by
    intro g
    change Matrix.GeneralLinearGroup.map (n := Fin N) σ (Matrix.GeneralLinearGroup.map (n := Fin N) i g) =
      Matrix.GeneralLinearGroup.map (n := Fin N) i g
    ext a b
    exact (hσ _).2 ⟨g a b, rfl⟩
  have hM : ∀ X Y : Matrix (Fin N) (Fin N) A, X.map i = Y.map i → X = Y := by
    intro X Y h
    ext a b
    exact hi (congrFun (congrFun h a) b)
  have hpre : ∀ g : GL (Fin N) B,
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) →
      ∃ X : Matrix (Fin N) (Fin N) A, X.map i = (g : Matrix (Fin N) (Fin N) B) := by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (n := Fin N) σ g = g := hg
    have h1 : ∀ a b, ∃ x : A, i x = (g : Matrix (Fin N) (Fin N) B) a b := by
      intro a b
      refine (hσ _).1 ?_
      have := congrArg (fun k : GL (Fin N) B => (k : Matrix (Fin N) (Fin N) B) a b) hg'
      exact this
    choose X hX using h1
    exact ⟨Matrix.of X, by ext a b; exact hX a b⟩
  refine ⟨(MulEquiv.ofBijective
    ((Matrix.GeneralLinearGroup.map (n := Fin N) i).codRestrict _ hmem) ⟨?_, ?_⟩).symm⟩
  · intro g k h
    have h1 : Matrix.GeneralLinearGroup.map (n := Fin N) i g =
      Matrix.GeneralLinearGroup.map (n := Fin N) i k := congrArg Subtype.val h
    apply Units.ext
    apply hM
    exact congrArg Units.val h1
  · rintro ⟨g, hg⟩
    obtain ⟨X, hX⟩ := hpre g hg
    obtain ⟨Y, hY⟩ := hpre g⁻¹ (inv_mem hg)
    refine ⟨⟨X, Y, hM _ _ ?_, hM _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.mul_inv
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.inv_mul
    · apply Subtype.ext
      apply Units.ext
      exact hX
