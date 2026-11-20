import Mathlib

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

noncomputable section

def GraphAlgebra (_f : τ → MvPolynomial σ R) : Type u := MvPolynomial σ R

instance instCommRingGraphAlgebra (f : τ → MvPolynomial σ R) : CommRing (GraphAlgebra f) :=
  inferInstanceAs (CommRing (MvPolynomial σ R))

instance instAlgebraGraphAlgebra (f : τ → MvPolynomial σ R) : Algebra R (GraphAlgebra f) :=
  inferInstanceAs (Algebra R (MvPolynomial σ R))

def graphAlgebraEquiv (f : τ → MvPolynomial σ R) : MvPolynomial σ R ≃ₐ[R] GraphAlgebra f :=
  AlgEquiv.refl

def aevalGraphAlgebra (f : τ → MvPolynomial σ R) : MvPolynomial τ R →ₐ[R] GraphAlgebra f :=
  (graphAlgebraEquiv f).toAlgHom.comp (MvPolynomial.aeval f)

instance instAlgebraBaseGraphAlgebra (f : τ → MvPolynomial σ R) :
    Algebra (MvPolynomial τ R) (GraphAlgebra f) :=
  (aevalGraphAlgebra f).toRingHom.toAlgebra

/- English proof (authored)
The algebra structure on the graph ring is given by evaluating each graph coordinate at its defining polynomial and then identifying the resulting polynomial with its element in the graph ring. This is the stated formula for its algebra map.
-/
theorem algebraMap_graphAlgebra (f : τ → MvPolynomial σ R) (p : MvPolynomial τ R) :
    algebraMap (MvPolynomial τ R) (GraphAlgebra f) p = graphAlgebraEquiv f (MvPolynomial.aeval f p) :=
  rfl

/- English proof (authored)
The graph algebra map evaluates polynomials at the defining functions. Evaluation sends a scalar to that same scalar, and the polynomial-to-graph identification respects scalars. Thus passing through the ring of graph coordinates gives the ordinary scalar map to the graph ring.
-/
private theorem algebraMap_graphAlgebra_eq_algebraMap_mvPolynomial (f : τ → MvPolynomial σ R) (r : R) :
    algebraMap R (GraphAlgebra f) r
      = algebraMap (MvPolynomial τ R) (GraphAlgebra f) (algebraMap R (MvPolynomial τ R) r) := by
  rw [algebraMap_graphAlgebra, AlgHom.commutes, AlgEquiv.commutes]

instance instIsScalarTowerGraphAlgebra (f : τ → MvPolynomial σ R) :
    IsScalarTower R (MvPolynomial τ R) (GraphAlgebra f) :=
  IsScalarTower.of_algebraMap_eq (algebraMap_graphAlgebra_eq_algebraMap_mvPolynomial f)

def graphRelation (f : τ → MvPolynomial σ R) (i : τ) : MvPolynomial σ (MvPolynomial τ R) :=
  MvPolynomial.C (MvPolynomial.X i)
    - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (f i)

abbrev graphRelationIdeal (f : τ → MvPolynomial σ R) : Ideal (MvPolynomial σ (MvPolynomial τ R)) :=
  Ideal.span (Set.range (graphRelation f))

def graphAlgebraAeval (f : τ → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial τ R) →ₐ[MvPolynomial τ R] GraphAlgebra f :=
  MvPolynomial.aeval (fun i : σ => graphAlgebraEquiv f (MvPolynomial.X i))

/- English proof (authored)
The evaluation map sends a variable to its prescribed value. The prescribed value is the corresponding original polynomial variable viewed in the graph ring.
-/
theorem graphAlgebraAeval_X (f : τ → MvPolynomial σ R) (i : σ) :
    graphAlgebraAeval f (MvPolynomial.X i) = graphAlgebraEquiv f (MvPolynomial.X i) :=
  MvPolynomial.aeval_X _ i

/- English proof (authored)
Evaluation sends a constant coefficient to its image under the algebra map. The coefficient here is a polynomial in the graph coordinates, so its image is evaluation at the defining polynomials, viewed in the graph ring.
-/
private theorem graphAlgebraAeval_C (f : τ → MvPolynomial σ R) (a : MvPolynomial τ R) :
    graphAlgebraAeval f (MvPolynomial.C a) = graphAlgebraEquiv f (MvPolynomial.aeval f a) := by
  have h : graphAlgebraAeval f (MvPolynomial.C a)
      = algebraMap (MvPolynomial τ R) (GraphAlgebra f) a := by
    simp [graphAlgebraAeval]
  rw [h, algebraMap_graphAlgebra]

/- English proof (authored)
Use polynomial induction. For a scalar, the coefficient inclusion followed by evaluation gives the same scalar in the graph ring. Sums follow by additivity. Multiplication by a variable follows because the coefficient inclusion preserves that variable and evaluation sends it to the corresponding variable of the graph ring.
-/
private theorem graphAlgebraAeval_map_C (f : τ → MvPolynomial σ R) (p : MvPolynomial σ R) :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)
      = graphAlgebraEquiv f p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [MvPolynomial.map_C, graphAlgebraAeval_C, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.map_X, hp, graphAlgebraAeval_X]

/- English proof (authored)
In the graph relation, the first term is the graph coordinate as a constant coefficient. Evaluation substitutes its defining polynomial. The second term, obtained by including that polynomial's coefficients, evaluates to the same polynomial in the graph ring. Their difference is zero.
-/
theorem graphAlgebraAeval_graphRelation (f : τ → MvPolynomial σ R) (i : τ) :
    graphAlgebraAeval f (graphRelation f i) = 0 := by
  simp only [graphRelation, map_sub, graphAlgebraAeval_C, graphAlgebraAeval_map_C, MvPolynomial.aeval_X, sub_self]

/- English proof (authored)
Represent the graph ring element by its polynomial under the inverse identification. Including the coefficients and evaluating returns that polynomial viewed in the graph ring, hence the original element.
-/
private theorem graphAlgebraAeval_map_C_graphAlgebraEquiv_symm (f : τ → MvPolynomial σ R) (x : GraphAlgebra f) :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
      ((graphAlgebraEquiv f).symm x)) = x := by
  rw [graphAlgebraAeval_map_C, AlgEquiv.apply_symm_apply]

private def graphSubstitutionHom (f : τ → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial τ R) →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.aeval f : MvPolynomial τ R →ₐ[R] MvPolynomial σ R).toRingHom)
    MvPolynomial.X

/- English proof (authored)
Substitution acts on constant coefficients by substituting the defining polynomials into the graph variables. A polynomial constant in the original variables is therefore sent to this substituted coefficient.
-/
private theorem graphSubstitutionHom_C (f : τ → MvPolynomial σ R) (a : MvPolynomial τ R) :
    graphSubstitutionHom f (MvPolynomial.C a) = MvPolynomial.aeval f a := by
  simp [graphSubstitutionHom]

/- English proof (authored)
The substitution map evaluates the coefficients and sends each original polynomial variable to itself. Applying it to a variable therefore gives the same variable.
-/
private theorem graphSubstitutionHom_X (f : τ → MvPolynomial σ R) (i : σ) :
    graphSubstitutionHom f (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [graphSubstitutionHom]

/- English proof (authored)
Compare the two maps on the polynomial generators. On coefficients both substitute the defining polynomials for the graph variables. On the original variables both return the corresponding graph ring variables. They preserve addition and multiplication, so they agree on every polynomial.
-/
private theorem graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    graphAlgebraAeval f p = graphAlgebraEquiv f (graphSubstitutionHom f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [graphAlgebraAeval_C, graphSubstitutionHom_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X q i hq => simp only [map_mul, hq, graphAlgebraAeval_X, graphSubstitutionHom_X]

/- English proof (authored)
Work modulo the ideal generated by the graph relations. In this quotient, each graph variable in the coefficient ring equals its defining polynomial in the original variables. Scalars agree on both sides. Addition preserves this equality, and multiplication by a graph variable preserves it by the corresponding graph relation. Polynomial induction proves that every coefficient polynomial agrees with its substituted polynomial modulo the ideal, which puts the stated difference in the ideal.
-/
private theorem C_sub_map_C_aeval_mem_graphRelationIdeal (f : τ → MvPolynomial σ R) (a : MvPolynomial τ R) :
    MvPolynomial.C a - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
      (MvPolynomial.aeval f a) ∈ graphRelationIdeal f := by
  induction a using MvPolynomial.induction_on with
  | C r =>
      have key : (MvPolynomial.C (MvPolynomial.C r : MvPolynomial τ R) :
            MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (MvPolynomial.C r : MvPolynomial τ R)) = 0 := by
        simp [MvPolynomial.algebraMap_eq]
      rw [key]
      exact Ideal.zero_mem _
  | add p q hp hq =>
      have key : (MvPolynomial.C (p + q) : MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (p + q))
          = (MvPolynomial.C p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (MvPolynomial.aeval f p))
            + (MvPolynomial.C q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (MvPolynomial.aeval f q)) := by
        simp only [map_add]
        ring
      rw [key]
      exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      have hrel : graphRelation f j ∈ graphRelationIdeal f := Ideal.subset_span ⟨j, rfl⟩
      have key : (MvPolynomial.C (p * MvPolynomial.X j) : MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (p * MvPolynomial.X j))
          = MvPolynomial.C p * graphRelation f j
            + (MvPolynomial.C p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
                (MvPolynomial.aeval f p))
              * MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (f j) := by
        simp only [graphRelation, map_mul, MvPolynomial.aeval_X]
        ring
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hrel) (Ideal.mul_mem_right _ _ hp)

/- English proof (authored)
Work modulo the graph relation ideal. For a constant coefficient, the preceding coefficient result gives equality with its substitution. Addition preserves the equality, and multiplying by an original variable preserves it because the substitution fixes that variable. Thus every polynomial agrees with its substituted polynomial after including its coefficients back into the original ring.
-/
private theorem sub_map_C_mem_graphRelationIdeal (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f p)
      ∈ graphRelationIdeal f := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [graphSubstitutionHom_C]
      exact C_sub_map_C_aeval_mem_graphRelationIdeal f a
  | add p q hp hq =>
      have key : p + q
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f (p + q))
          = (p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f p))
            + (q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
                (graphSubstitutionHom f q)) := by
        simp only [map_add]
        ring
      rw [key]
      exact Ideal.add_mem _ hp hq
  | mul_X q i hq =>
      have key : q * MvPolynomial.X i
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (graphSubstitutionHom f (q * MvPolynomial.X i))
          = (q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f q))
            * MvPolynomial.X i := by
        simp only [map_mul, graphSubstitutionHom_X, MvPolynomial.map_X]
        ring
      rw [key]
      exact Ideal.mul_mem_right _ _ hq

def graphAlgebraGenerators (f : τ → MvPolynomial σ R) :
    Algebra.Generators (MvPolynomial τ R) (GraphAlgebra f) σ where
  val := fun i => graphAlgebraEquiv f (MvPolynomial.X i)
  σ' := fun x =>
    MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) ((graphAlgebraEquiv f).symm x)
  aeval_val_σ' := graphAlgebraAeval_map_C_graphAlgebraEquiv_symm f

/- English proof (authored)
The generator map evaluates the original variables at their corresponding graph ring elements. This is the graph evaluation map, so its kernel consists exactly of the polynomials evaluating to zero.
-/
private theorem mem_ker_graphAlgebraGenerators_iff (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    p ∈ (graphAlgebraGenerators f).ker ↔ graphAlgebraAeval f p = 0 := Iff.rfl

/- English proof (authored)
Every graph relation evaluates to zero, so their span is in the kernel. Conversely, if a polynomial evaluates to zero in the graph ring, its substituted polynomial is zero by injectivity of the polynomial-to-graph identification. The polynomial differs from its substituted form by an element of the graph relation ideal, so it belongs to that ideal.
-/
private theorem span_range_graphRelation_eq_ker (f : τ → MvPolynomial σ R) :
    Ideal.span (Set.range (graphRelation f)) = (graphAlgebraGenerators f).ker := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simp only [SetLike.mem_coe]
    exact (mem_ker_graphAlgebraGenerators_iff f _).2 (graphAlgebraAeval_graphRelation f i)
  · intro p hp
    have hp' : graphAlgebraAeval f p = 0 := (mem_ker_graphAlgebraGenerators_iff f p).1 hp
    have h0 : graphSubstitutionHom f p = 0 := by
      have h1 := graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom f p
      rw [hp'] at h1
      have h2 : graphAlgebraEquiv f (graphSubstitutionHom f p) = graphAlgebraEquiv f 0 := by
        rw [← h1, map_zero]
      exact (graphAlgebraEquiv f).injective h2
    have hmem := sub_map_C_mem_graphRelationIdeal f p
    rwa [h0, map_zero, sub_zero] at hmem

def graphPresentation (f : τ → MvPolynomial σ R) :
    Algebra.Presentation (MvPolynomial τ R) (GraphAlgebra f) σ τ where
  toGenerators := graphAlgebraGenerators f
  relation := graphRelation f
  span_range_relation_eq_ker := span_range_graphRelation_eq_ker f

def graphPreSubmersivePresentation (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebra f) σ τ where
  toPresentation := graphPresentation f
  map := v
  map_inj := hv

/- English proof (authored)
The pre-submersive presentation retains the graph presentation's relations, which are the graph coordinate minus its defining polynomial for each index.
-/
@[simp] theorem graphPreSubmersivePresentation_relation (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).relation = graphRelation f :=
  rfl

/- English proof (authored)
The pre-submersive graph presentation is equipped with the given injection from the relation indices to the chosen variable indices. Its selected variable for each relation is therefore the value of that injection.
-/
@[simp] theorem graphPreSubmersivePresentation_map (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).map = v :=
  rfl

def graphJacobianMinorMatrix (f : τ → MvPolynomial σ R) (v : τ → σ) : Matrix τ τ (MvPolynomial σ R) :=
  Matrix.of fun i j => MvPolynomial.pderiv (v i) (f j)

/- English proof (authored)
By construction, the entry in the chosen row and column is the partial derivative of the column's polynomial with respect to the row's selected variable.
-/
theorem graphJacobianMinorMatrix_apply (f : τ → MvPolynomial σ R) (v : τ → σ) (i j : τ) :
    graphJacobianMinorMatrix f v i j = MvPolynomial.pderiv (v i) (f j) :=
  rfl

/- English proof (authored)
Differentiate each graph relation with respect to its selected row variable. The graph coordinate is a constant coefficient, so its derivative is zero. Differentiation commutes with the inclusion of the original coefficients, so the remaining term is the negative of the included partial derivative of the corresponding defining polynomial. These are the entries of the asserted negative matrix.
-/
theorem graphPreSubmersivePresentation_jacobiMatrix [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobiMatrix
      = -((graphJacobianMinorMatrix f v).map
          (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)) := by
  ext i j
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp only [graphPreSubmersivePresentation_relation, graphPreSubmersivePresentation_map,
    graphRelation, map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_map, zero_sub,
    Matrix.neg_apply, Matrix.map_apply, graphJacobianMinorMatrix_apply]

/- English proof (authored)
Use the entrywise calculation to write the presentation's Jacobian matrix as the negative of the scalar-extended minor matrix. Taking the determinant contributes one factor of minus one for each row and commutes with the coefficient inclusion. Evaluating the determinant in the graph ring undoes that coefficient inclusion on the original polynomial determinant. This gives the claimed signed determinant.
-/
theorem graphPreSubmersivePresentation_jacobian [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobian
      = (-1 : GraphAlgebra f) ^ Fintype.card τ * graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det := by
  have hmap : ((graphJacobianMinorMatrix f v).map
      (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)).det
      = MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphJacobianMinorMatrix f v).det :=
    (RingHom.map_det (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R))
      (graphJacobianMinorMatrix f v)).symm
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    graphPreSubmersivePresentation_jacobiMatrix, Matrix.det_neg, hmap, map_mul, map_pow,
    map_neg, map_one]
  congr 1
  exact graphAlgebraAeval_map_C f _

end

end FunctorialResolution.EmbeddedResolution
