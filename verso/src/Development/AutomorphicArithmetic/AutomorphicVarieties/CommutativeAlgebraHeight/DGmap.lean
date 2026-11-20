import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Establish `: i = j` using `Algebra.algebra_ext _ _ h`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
private theorem gdet_inst {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext _ _ h
  subst this
  rfl

/- English proof (translation)
Use `letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra`. Set `φ : A[X] →ₐ[A] B[X]` to `{ Polynomial.mapRingHom f with commutes' := fun a => by`. Express the relevant statement in the definitionally equal form `Polynomial.map f (C a) = C (f a)`. Conclude with `Polynomial.map_C f }`. Establish `h` using `D.nat A[X] B[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)`.

Use `Eq.trans ?_ h` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.D B[X] _ = D.D B[X] _`. Use `congr 1`. Establish `hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f` using `rfl`. Rewrite using `[hφ]`.

Use extensionality with `g : 2`. Simplify using the standard rewrite rules.
-/
private theorem gdet_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] B[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f }
  have h := D.nat A[X] B[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  change D.D B[X] _ = D.D B[X] _
  congr 1
  have hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f := rfl
  rw [hφ]
  ext g : 2
  simp

/- English proof (translation)
Introduce `n A G _ _ D`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `GDet.ext fun B _ j x => gdet_inst D B ((algebraMap A B).comp (RingHom.id A)).toAlgebra j (fun _ => rfl) x`. Introduce `B C _ _ f g`. Conclude with `GDet.ext fun S _ _ x => gdet_inst D S _ _ (fun _ => rfl) x`.

Introduce `B _ f y`. Use `⟨gdet_chi D f y, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [GDet.lam, gdet_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]`. Introduce `B _ f ρ`. Use `GDet.ext fun S _ _ x => ?_` and prove the remaining obligations.

Use `letI : Algebra A S := ((algebraMap B S).comp f).toAlgebra`. Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ S x).det = (GDet.repAlg (f.mapMatrix.toMonoidHom.comp ρ) S x).det`. Use `congr 2`.
-/
theorem UpperTheory.V.CA.d_gmap :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.map (RingHom.id A) = D ∧ (∀ {B C : Type} [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), (D.map f).map g = D.map (g.comp f)) ∧ (∀ {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G), (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f ∧ ∀ i, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧ ∀ {B : Type} [CommRing B] (f : A →+* B) (ρ : G →* Matrix (Fin n) (Fin n) A), (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  intro n A G _ _ D
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact GDet.ext fun B _ j x =>
      gdet_inst D B ((algebraMap A B).comp (RingHom.id A)).toAlgebra j (fun _ => rfl) x
  · intro B C _ _ f g
    exact GDet.ext fun S _ _ x => gdet_inst D S _ _ (fun _ => rfl) x
  · intro B _ f y
    refine ⟨gdet_chi D f y, fun i => ?_⟩
    simp only [GDet.lam, gdet_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  · intro B _ f ρ
    refine GDet.ext fun S _ _ x => ?_
    letI : Algebra A S := ((algebraMap B S).comp f).toAlgebra
    change (GDet.repAlg ρ S x).det = (GDet.repAlg (f.mapMatrix.toMonoidHom.comp ρ) S x).det
    congr 2
