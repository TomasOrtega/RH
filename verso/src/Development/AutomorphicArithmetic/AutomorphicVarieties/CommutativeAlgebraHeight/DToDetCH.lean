import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Establish `: i = j` using `Algebra.algebra_ext i j h`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
private theorem D_congr {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext i j h
  subst this; rfl

/- English proof (translation)
Simplify using `only [Det.gen, GDet.gen, map_sum, ofT_tmul]`. Both sides reduce to the same expression.
-/
private theorem ofT_gen {A G : Type} [CommRing A] [Group G] {m : ℕ} (y : Fin m → MonoidAlgebra A G) :
    ofT A G (MvPolynomial (Fin m) A) (Det.gen (A := A) y) = GDet.gen y := by
  simp only [Det.gen, GDet.gen, map_sum, ofT_tmul]
  rfl

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s y => ext1`. Use `ext1 g`.

Simplify using `[ofT_tmul]`.
-/
private theorem ofT_map {A G : Type} [CommRing A] [Group G] (S : Type) [CommRing S] [Algebra A S]
    (x : S ⊗[A] MonoidAlgebra A G) :
    ofT A G S[X] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A _) x) =
      MonoidAlgebra.mapRingHom G (C : S →+* S[X]) (ofT A G S x) := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s y => ext1; ext1 g; simp [ofT_tmul]

/- English proof (translation)
Establish `h : ofT A G (MvPolynomial (Fin m) A)[X] (X ⊗ₜ 1 - Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]) (AlgHom.id A _) x) = MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (ofT A G _ x)`. Rewrite using `[map_sub, ofT_map, ofT_tmul, map_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]`. Use `(congrArg (D.D (MvPolynomial (Fin m) A)[X]) h).trans ?_` and prove the remaining obligations. Conclude with `D_congr D (MvPolynomial (Fin m) A)[X] inferInstance ((algebraMap (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]).comp MvPolynomial.C).toAlgebra (fun a => rfl) _`.
-/
private theorem chiS_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (x : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) :
    D.toDet.chiS (MvPolynomial (Fin m) A) x =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (ofT A G _ x) := by
  have h : ofT A G (MvPolynomial (Fin m) A)[X] (X ⊗ₜ 1 -
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X])
        (AlgHom.id A _) x) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (ofT A G _ x) := by
    rw [map_sub, ofT_map, ofT_tmul, map_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  refine (congrArg (D.D (MvPolynomial (Fin m) A)[X]) h).trans ?_
  exact D_congr D (MvPolynomial (Fin m) A)[X] inferInstance
    ((algebraMap (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]).comp MvPolynomial.C).toAlgebra (fun a => rfl) _

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_add, ha, hb]`. Consider the case `tmul s y => simp [ofT_tmul, mul_comm s, MvPolynomial.coeff_C_mul, mul_comm (y.coeff g)]`.
-/
private theorem coeff_lid {A G : Type} [CommRing A] [Group G] {m : ℕ} (β : Fin m →₀ ℕ)
    (w : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) (g : G) :
    (TensorProduct.lid A (MonoidAlgebra A G) ((MvPolynomial.lcoeff A β).rTensor _ w)).coeff g =
      MvPolynomial.coeff β ((ofT A G _ w).coeff g) := by
  induction w with
  | zero => simp
  | add a b ha hb => simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_add, ha, hb]
  | tmul s y => simp [ofT_tmul, mul_comm s, MvPolynomial.coeff_C_mul, mul_comm (y.coeff g)]

/- English proof (translation)
Rewrite using `[Det.chElt, coeff_lid, chiS_eq, ← Polynomial.aeval_algHom_apply, ofT_gen]`.
-/
private theorem chElt_coeff {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) (g : G) :
    (D.toDet.chElt y β).coeff g = MvPolynomial.coeff β
      ((Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))).coeff g) := by
  rw [Det.chElt, coeff_lid, chiS_eq, ← Polynomial.aeval_algHom_apply, ofT_gen]

/- English proof (translation)
Introduce `n A G _ _ D`. Rewrite using `[Det.CH]`. Use `congr 1`. Use `ext1 z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, y, β, rfl⟩`. Conclude with `⟨m, y, β, chElt_coeff D y β⟩`. Introduce and unpack `⟨m, y, β, h⟩`. Use `⟨m, y, β, ?_⟩` and prove the remaining obligations. Use extensionality with `g`.

Rewrite using `[h, chElt_coeff]`.
-/
theorem UpperTheory.V.CA.d_toDet_CH :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.toDet.CH = TwoSidedIdeal.span D.CH := by
  intro n A G _ _ D
  rw [Det.CH]
  congr 1
  ext1 z
  constructor
  · rintro ⟨m, y, β, rfl⟩
    exact ⟨m, y, β, chElt_coeff D y β⟩
  · rintro ⟨m, y, β, h⟩
    refine ⟨m, y, β, ?_⟩
    ext g
    rw [h, chElt_coeff]
