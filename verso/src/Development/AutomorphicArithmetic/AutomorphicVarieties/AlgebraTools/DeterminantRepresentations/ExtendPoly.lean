import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.LiftIndep

open Polynomial UpperTheory.V.W

/- English proof (translation)
Introduce `n A G _ _ d hnat hhom`. Establish `hsurj : ∀ (B : Type) [CommRing B] [Algebra A B], Function.Surjective (MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B))`. Introduce `B _ _`. Rewrite using `[MonoidAlgebra.coe_mapRingHom]`. Use `MonoidAlgebra.map_surjective _ ?_` and prove the remaining obligations.

Introduce `b`. Conclude with `⟨MvPolynomial.X b, by simp⟩`. Establish `spec : ∀ (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B G), MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) (hsurj B y).choose = y` using `fun B _ _ y => (hsurj B y).choose_spec`. Establish `ind : ∀ (B : Type) [CommRing B] [Algebra A B] (x x' : MonoidAlgebra (MvPolynomial B A) G), MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x = MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : …` using `fun B _ _ x x' h => UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B B B _ _ x x' h`. Use `⟨⟨fun B _ _ => { toFun := fun y => MvPolynomial.aeval id (d B (hsurj B y).choose) map_one' := ?_ map_mul' := ?_ }, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show MvPolynomial.aeval id (d B (hsurj B 1).choose) = 1`. Rewrite using `[ind B _ 1 (by rw [spec, map_one]), map_one, map_one]`. Introduce `y y' show MvPolynomial.aeval id (d B (hsurj B (y * y')).choose) = MvPolynomial.aeval id (d B (hsurj B y).choose) * MvPolynomial.aeval id (d B (hsurj B y').choose)`. Rewrite using `[ind B _ ((hsurj B y).choose * (hsurj B y').choose) (by rw [spec, map_mul, spec, spec]), map_mul, map_mul]`. Introduce `B B' _ _ _ _ f y`.

Establish `h` using `UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B' B' B (MvPolynomial.aeval id) (f.comp (MvPolynomial.aeval id)) (hsurj B' (MonoidAlgebra.mapRingHom G (f : B →+* B') y)).choose (hsurj B y).choose (by`. Rewrite using `[spec]`. Use `conv_lhs => rw [← spec B y]`. Rewrite using `[← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]`. Use the proof step `rfl)`.

Conclude with `h`. Introduce `B _ _ b y show MvPolynomial.aeval id (d B (hsurj B (b • y)).choose) = b ^ n * MvPolynomial.aeval id (d B (hsurj B y).choose)`. Rewrite using `[ind B _ (MvPolynomial.X b • (hsurj B y).choose) (by`. Rewrite using `[spec]`. Use `conv_lhs => rw [← spec B y]`.

Use extensionality with `m`. Rewrite using `[MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply (MvPolynomial.X b : MvPolynomial B A) (hsurj B y).choose m]`. Simplify using `[smul_eq_mul]), hhom, map_mul, map_pow, MvPolynomial.aeval_X, id]`. Introduce `σ x show MvPolynomial.aeval id (d (MvPolynomial σ A) (hsurj (MvPolynomial σ A) x).choose) = d σ x`. Establish `h` using `UpperTheory.V.AlgebraTools.Det.liftIndep d hnat (MvPolynomial σ A) (MvPolynomial σ A) σ (MvPolynomial.aeval id) (AlgHom.id A _) _ x (by rw [spec])`.

Simplify using `using h`.
-/
theorem UpperTheory.V.AlgebraTools.Det.extendPoly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    (∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G), d σ (b • x) = b ^ n * d σ x) →
    ∃ D : GDet n A G, ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), D.D (MvPolynomial σ A) x = d σ x := by
  intro n A G _ _ d hnat hhom
  have hsurj : ∀ (B : Type) [CommRing B] [Algebra A B],
      Function.Surjective (MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)) := by
    intro B _ _
    rw [MonoidAlgebra.coe_mapRingHom]
    refine MonoidAlgebra.map_surjective _ ?_
    intro b
    exact ⟨MvPolynomial.X b, by simp⟩
  have spec : ∀ (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B G),
      MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)
        (hsurj B y).choose = y :=
    fun B _ _ y => (hsurj B y).choose_spec
  have ind : ∀ (B : Type) [CommRing B] [Algebra A B] (x x' : MonoidAlgebra (MvPolynomial B A) G),
      MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x =
        MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x' →
      MvPolynomial.aeval id (d B x) = MvPolynomial.aeval id (d B x') :=
    fun B _ _ x x' h => UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B B B _ _ x x' h
  refine ⟨⟨fun B _ _ =>
    { toFun := fun y => MvPolynomial.aeval id (d B (hsurj B y).choose)
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_⟩, ?_⟩
  · show MvPolynomial.aeval id (d B (hsurj B 1).choose) = 1
    rw [ind B _ 1 (by rw [spec, map_one]), map_one, map_one]
  · intro y y'
    show MvPolynomial.aeval id (d B (hsurj B (y * y')).choose) =
      MvPolynomial.aeval id (d B (hsurj B y).choose) * MvPolynomial.aeval id (d B (hsurj B y').choose)
    rw [ind B _ ((hsurj B y).choose * (hsurj B y').choose) (by rw [spec, map_mul, spec, spec]),
      map_mul, map_mul]
  · intro B B' _ _ _ _ f y
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B' B' B (MvPolynomial.aeval id)
      (f.comp (MvPolynomial.aeval id)) (hsurj B' (MonoidAlgebra.mapRingHom G (f : B →+* B') y)).choose
      (hsurj B y).choose (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]
        rfl)
    exact h
  · intro B _ _ b y
    show MvPolynomial.aeval id (d B (hsurj B (b • y)).choose) =
      b ^ n * MvPolynomial.aeval id (d B (hsurj B y).choose)
    rw [ind B _ (MvPolynomial.X b • (hsurj B y).choose) (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        ext m
        rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_smul_apply (MvPolynomial.X b : MvPolynomial B A) (hsurj B y).choose m]
        simp [smul_eq_mul]), hhom, map_mul, map_pow, MvPolynomial.aeval_X, id]
  · intro σ x
    show MvPolynomial.aeval id (d (MvPolynomial σ A) (hsurj (MvPolynomial σ A) x).choose) = d σ x
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat (MvPolynomial σ A) (MvPolynomial σ A) σ
      (MvPolynomial.aeval id) (AlgHom.id A _) _ x (by rw [spec])
    simpa using h
