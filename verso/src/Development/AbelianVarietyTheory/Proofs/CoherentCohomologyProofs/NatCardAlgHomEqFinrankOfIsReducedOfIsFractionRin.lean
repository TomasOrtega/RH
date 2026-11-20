import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

section Index

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[← Algebra.discr_of_matrix_vecMul, e.toMatrix_map_vecMul v]`.
-/
theorem discr_eq_det_toMatrix_sq_mul (e : Basis ι R S) (v : ι → S) :
    Algebra.discr R v = (e.toMatrix v).det ^ 2 * Algebra.discr R e := by
  rw [← Algebra.discr_of_matrix_vecMul, e.toMatrix_map_vecMul v]

/- English proof (translation)
Rewrite using `[discr_eq_det_toMatrix_sq_mul e, Basis.det_apply]`.
-/
theorem discr_eq_basis_det_sq_mul (e : Basis ι R S) (v : ι → S) :
    Algebra.discr R v = e.det v ^ 2 * Algebra.discr R e := by
  rw [discr_eq_det_toMatrix_sq_mul e, Basis.det_apply]

/- English proof (translation)
Rewrite using `[Algebra.norm_apply]`. Conclude with `e.det_comp (LinearMap.mul R S u) v`.
-/
theorem basis_det_mul_left (e : Basis ι R S) (u : S) (v : ι → S) :
    e.det (fun i => u * v i) = Algebra.norm R u * e.det v := by
  rw [Algebra.norm_apply]
  exact e.det_comp (LinearMap.mul R S u) v

/- English proof (translation)
Rewrite using `[discr_eq_basis_det_sq_mul e, discr_eq_basis_det_sq_mul e v, basis_det_mul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem discr_mul_left_of_basis (e : Basis ι R S) (u : S) (v : ι → S) :
    Algebra.discr R (fun i => u * v i) = Algebra.norm R u ^ 2 * Algebra.discr R v := by
  rw [discr_eq_basis_det_sq_mul e, discr_eq_basis_det_sq_mul e v, basis_det_mul_left]
  ring

variable [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Rewrite using `[discr_eq_basis_det_sq_mul e, addVal_mul, addVal_pow, length_quotient_span_eq_addVal_det e, nsmul_eq_mul, Nat.cast_ofNat]`.
-/
theorem addVal_discr_eq_two_mul_length_add (e : Basis ι R S) (v : ι → S) :
    addVal R (Algebra.discr R v) =
      2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) := by
  rw [discr_eq_basis_det_sq_mul e, addVal_mul, addVal_pow, length_quotient_span_eq_addVal_det e,
    nsmul_eq_mul, Nat.cast_ofNat]

/- English proof (translation)
Rewrite using `[addVal_discr_eq_two_mul_length_add e]`. Conclude with `le_self_add`.
-/
theorem two_mul_length_le_addVal_discr (e : Basis ι R S) (v : ι → S) :
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) := by
  rw [addVal_discr_eq_two_mul_length_add e]
  exact le_self_add

/- English proof (translation)
The claim follows from `two_mul_length_le_addVal_discr (Module.finBasisOfFinrankEq R S h.symm |>.reindex (Fintype.equivFin ι).symm) v`.
-/
theorem two_mul_length_le_addVal_discr_of_card [Module.Free R S] [Module.Finite R S]
    (h : Fintype.card ι = finrank R S) (v : ι → S) :
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) :=
  two_mul_length_le_addVal_discr (Module.finBasisOfFinrankEq R S h.symm |>.reindex
    (Fintype.equivFin ι).symm) v

/- English proof (translation)
Rewrite using `[length_quotient_span_ne_top_iff e]`. Introduce `h`. Rewrite `hv` using `[discr_eq_basis_det_sq_mul e, h]`. Simplify using `at hv`.
-/
theorem length_quotient_span_ne_top_of_discr_ne_zero (e : Basis ι R S) {v : ι → S}
    (hv : Algebra.discr R v ≠ 0) :
    Module.length R (S ⧸ Submodule.span R (Set.range v)) ≠ ⊤ := by
  rw [length_quotient_span_ne_top_iff e]
  intro h
  rw [discr_eq_basis_det_sq_mul e, h] at hv
  simp at hv

/- English proof (translation)
Rewrite using `[addVal_discr_eq_two_mul_length_add e, (Submodule.Quotient.equiv (Submodule.span R (Set.range v)) (Submodule.span R (Set.range fun i => φ (v i))) φ ?_).length_eq]`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem addVal_discr_eq_two_mul_length_add_of_equiv {M : Type*} [AddCommGroup M] [Module R M]
    (φ : M ≃ₗ[R] S) (e : Basis ι R S) (v : ι → M) :
    addVal R (Algebra.discr R fun i => φ (v i)) =
      2 * Module.length R (M ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) := by
  rw [addVal_discr_eq_two_mul_length_add e,
    (Submodule.Quotient.equiv (Submodule.span R (Set.range v))
      (Submodule.span R (Set.range fun i => φ (v i))) φ ?_).length_eq]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

/- English proof (translation)
Rewrite using `[addVal_discr_eq_two_mul_length_add_of_equiv φ e]`. Conclude with `le_self_add`.
-/
theorem two_mul_length_le_addVal_discr_of_equiv {M : Type*} [AddCommGroup M] [Module R M]
    (φ : M ≃ₗ[R] S) (e : Basis ι R S) (v : ι → M) :
    2 * Module.length R (M ⧸ Submodule.span R (Set.range v)) ≤
      addVal R (Algebra.discr R fun i => φ (v i)) := by
  rw [addVal_discr_eq_two_mul_length_add_of_equiv φ e]
  exact le_self_add

end Index

section Points

variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `h`. Take `⟨c, hc, hc₀⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h`. Establish `hli` using `(linearIndependent_algHom_toLinearMap R S L).comp P hP`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Use `hc (funext (hli c (e.ext fun i => ?_)))` and prove the remaining obligations.

Use `congrFun hc₀ i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem det_algHom_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : (Matrix.of fun i j => P j (e i)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hc₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hli := (linearIndependent_algHom_toLinearMap R S L).comp P hP
  rw [Fintype.linearIndependent_iff] at hli
  refine hc (funext (hli c (e.ext fun i => ?_)))
  have := congrFun hc₀ i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

omit [IsDomain L] in

/- English proof (translation)
Use extensionality with `j k`. Rewrite using `[Matrix.diagonal_mul, Matrix.of_apply, ← map_mul, ← e.sum_repr (x * e k), map_sum, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply, mul_comm]`.
-/
theorem algHom_matrix_mul_leftMulMatrix (e : Basis ι R S) (P : ι → (S →ₐ[R] L)) (x : S) :
    (Matrix.of fun j i => P j (e i)) * (Algebra.leftMulMatrix e x).map (algebraMap R L) =
      Matrix.diagonal (fun j => P j x) * Matrix.of fun j i => P j (e i) := by
  ext j k
  rw [Matrix.diagonal_mul, Matrix.of_apply, ← map_mul, ← e.sum_repr (x * e k), map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Matrix.of_apply, mul_comm]

/- English proof (translation)
Use `set Q : Matrix ι ι L := Matrix.of fun j i => P j (e i) with hQ`. Establish `hQ₀ : Q.det ≠ 0`. Rewrite using `[← Matrix.det_transpose]`. Conclude with `det_algHom_basis_ne_zero e hP`. Establish `h` using `algHom_matrix_mul_leftMulMatrix e P x`.

Rewrite `h` using `[← hQ]`. Rewrite using `[← Matrix.charpoly_map, ← Matrix.charpoly_diagonal]`. Use `set A := (Algebra.leftMulMatrix e x).map (algebraMap R L)`. Use `set D := Matrix.diagonal fun j => P j x`. Establish `h₁ : (C : L →+* L[X]).mapMatrix Q * A.charmatrix = D.charmatrix * (C : L →+* L[X]).mapMatrix Q`.

Simplify using `only [Matrix.charmatrix, mul_sub, sub_mul, ← map_mul, h]`. Use `congr 1`. Conclude with `(Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm`. Establish `h₂` using `congrArg Matrix.det h₁`. Rewrite `h₂` using `[Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, mul_comm]`.

Conclude with `mul_right_cancel₀ (C_ne_zero.mpr hQ₀) h₂`.
-/
theorem map_charpoly_leftMulMatrix_eq_prod_algHom (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    (Algebra.leftMulMatrix e x).charpoly.map (algebraMap R L) = ∏ j, (X - C (P j x)) := by
  set Q : Matrix ι ι L := Matrix.of fun j i => P j (e i) with hQ
  have hQ₀ : Q.det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact det_algHom_basis_ne_zero e hP
  have h := algHom_matrix_mul_leftMulMatrix e P x
  rw [← hQ] at h
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal]
  set A := (Algebra.leftMulMatrix e x).map (algebraMap R L)
  set D := Matrix.diagonal fun j => P j x
  have h₁ : (C : L →+* L[X]).mapMatrix Q * A.charmatrix =
      D.charmatrix * (C : L →+* L[X]).mapMatrix Q := by
    simp only [Matrix.charmatrix, mul_sub, sub_mul, ← map_mul, h]
    congr 1
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm
  have h₂ := congrArg Matrix.det h₁
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, mul_comm] at h₂
  exact mul_right_cancel₀ (C_ne_zero.mpr hQ₀) h₂

/- English proof (translation)
Establish `hQ₀ : (Matrix.of fun j i => P j (e i)).det ≠ 0`. Rewrite using `[← Matrix.det_transpose]`. Conclude with `det_algHom_basis_ne_zero e hP`. Establish `h` using `congrArg Matrix.det (algHom_matrix_mul_leftMulMatrix e P x)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm]`.

Rewrite using `[Algebra.norm_eq_matrix_det e, RingHom.map_det]`. Conclude with `mul_right_cancel₀ hQ₀ h`.
-/
theorem algebraMap_norm_eq_prod_algHom_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.norm R x) = ∏ j, P j x := by
  have hQ₀ : (Matrix.of fun j i => P j (e i)).det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact det_algHom_basis_ne_zero e hP
  have h := congrArg Matrix.det (algHom_matrix_mul_leftMulMatrix e P x)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h
  rw [Algebra.norm_eq_matrix_det e, RingHom.map_det]
  exact mul_right_cancel₀ hQ₀ h

/- English proof (translation)
Establish `h` using `map_charpoly_leftMulMatrix_eq_prod_algHom e hP x`. Rewrite `h` using `[← Matrix.charpoly_map, ← Matrix.charpoly_diagonal]`. Rewrite using `[Algebra.trace_eq_matrix_trace e, ← Matrix.trace_diagonal, Matrix.trace_eq_neg_charpoly_nextCoeff (Matrix.diagonal _), ← h, ← Matrix.trace_eq_neg_charpoly_nextCoeff, AddMonoidHom.map_trace]`.
-/
theorem algebraMap_trace_eq_sum_algHom_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  have h := map_charpoly_leftMulMatrix_eq_prod_algHom e hP x
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal] at h
  rw [Algebra.trace_eq_matrix_trace e, ← Matrix.trace_diagonal,
    Matrix.trace_eq_neg_charpoly_nextCoeff (Matrix.diagonal _), ← h,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, AddMonoidHom.map_trace]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[algebraMap_trace_eq_sum_algHom_of_basis e hP, Matrix.mul_apply]`.
-/
theorem map_traceMatrix_eq_mul_transpose_of_basis {κ : Type*} (e : Basis ι R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : κ → S) :
    (Algebra.traceMatrix R v).map (algebraMap R L) =
      (Matrix.of fun i j => P j (v i)) * (Matrix.of fun i j => P j (v i)).transpose := by
  ext i k
  simp [algebraMap_trace_eq_sum_algHom_of_basis e hP, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply, map_traceMatrix_eq_mul_transpose_of_basis e hP, Matrix.det_mul, Matrix.det_transpose, pow_two]`.
-/
theorem algebraMap_discr_eq_det_sq_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_traceMatrix_eq_mul_transpose_of_basis e hP, Matrix.det_mul, Matrix.det_transpose, pow_two]

/- English proof (translation)
Rewrite using `[algebraMap_discr_eq_det_sq_of_basis e hP]`. Conclude with `pow_ne_zero _ (det_algHom_basis_ne_zero e hP)`.
-/
theorem algebraMap_discr_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : algebraMap R L (Algebra.discr R e) ≠ 0 := by
  rw [algebraMap_discr_eq_det_sq_of_basis e hP]
  exact pow_ne_zero _ (det_algHom_basis_ne_zero e hP)

variable [Module.Free R S] [Module.Finite R S]

omit [DecidableEq ι] in

/- English proof (translation)
Use `(algebraMap R L).domain_nontrivial` as an intermediate fact. Conclude with `algebraMap_norm_eq_prod_algHom_of_basis ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x`.
-/
theorem algebraMap_norm_eq_prod_algHom_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.norm R x) = ∏ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_norm_eq_prod_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x

omit [DecidableEq ι] in

/- English proof (translation)
Use `(algebraMap R L).domain_nontrivial` as an intermediate fact. Conclude with `algebraMap_trace_eq_sum_algHom_of_basis ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x`.
-/
theorem algebraMap_trace_eq_sum_algHom_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_trace_eq_sum_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x

/- English proof (translation)
Use `(algebraMap R L).domain_nontrivial` as an intermediate fact. Conclude with `algebraMap_discr_eq_det_sq_of_basis ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP v`.
-/
theorem algebraMap_discr_eq_det_sq_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_discr_eq_det_sq_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP v

end Points

section Count

/- English proof (translation)
Establish `: IsArtinianRing S` using `.of_finite K S`. Establish `(I : MaximalSpectrum S) : Algebra.FormallyEtale K (S ⧸ I.asIdeal)`. Use `letI := Ideal.Quotient.field I.asIdeal`. Conclude with `Algebra.FormallyEtale.of_isSeparable K (S ⧸ I.asIdeal)`. Conclude with `⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars K).symm, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩`.
-/
theorem etale_of_isReduced_of_perfectField (K S : Type*) [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Module.Finite K S] [IsReduced S] : Algebra.Etale K S := by
  have : IsArtinianRing S := .of_finite K S
  have (I : MaximalSpectrum S) : Algebra.FormallyEtale K (S ⧸ I.asIdeal) := by
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyEtale.of_isSeparable K (S ⧸ I.asIdeal)
  exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars K).symm,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]

/- English proof (translation)
Use `(algebraMap R L).domain_nontrivial` as an intermediate fact. Establish `: IsArtinianRing (L ⊗[R] S)` using `.of_finite L _`. Use `Fintype.ofFinite (PrimeSpectrum (L ⊗[R] S))` as an intermediate fact. Rewrite using `[Nat.card_congr (AlgHom.liftEquiv R L S L), Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[R] S)), ← Module.finrank_baseChange (R := L) (S := R) (M' := S), (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[R] S)).toLinearEquiv.finrank_eq, Module.finrank_fi …`.
-/
theorem natCard_algHom_eq_finrank_of_etale_baseChange [Module.Free R S] [Module.Finite R S]
    [IsSepClosed L] [Algebra.FormallyEtale L (L ⊗[R] S)] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have := (algebraMap R L).domain_nontrivial
  have : IsArtinianRing (L ⊗[R] S) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[R] S))
  rw [Nat.card_congr (AlgHom.liftEquiv R L S L),
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[R] S)),
    ← Module.finrank_baseChange (R := L) (S := R) (M' := S),
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[R] S)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/- English proof (translation)
The claim follows from `have := etale_of_isReduced_of_perfectField L (L ⊗[R] S) natCard_algHom_eq_finrank_of_etale_baseChange R S L`.
-/
theorem natCard_algHom_eq_finrank_of_isReduced_baseChange [Module.Free R S] [Module.Finite R S]
    [IsAlgClosed L] [IsReduced (L ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have := etale_of_isReduced_of_perfectField L (L ⊗[R] S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L

/- English proof (translation)
The claim follows from `have : Algebra.FormallyEtale L (L ⊗[R] S) := .of_equiv (Algebra.TensorProduct.cancelBaseChange R K L L S) natCard_algHom_eq_finrank_of_etale_baseChange R S L`.
-/
theorem natCard_algHom_eq_finrank_of_etale_tower [Module.Free R S] [Module.Finite R S]
    (K : Type*) [Field K] [Algebra R K] [Algebra K L] [IsScalarTower R K L] [IsSepClosed L]
    [Algebra.FormallyEtale K (K ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have : Algebra.FormallyEtale L (L ⊗[R] S) :=
    .of_equiv (Algebra.TensorProduct.cancelBaseChange R K L L S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L

/- English proof (translation)
Establish `: IsReduced (K ⊗[R] S)`. Use `letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra`. Use `haveI := IsLocalization.tensorRight (S := S) K (nonZeroDivisors R)`. Conclude with `isReduced_of_injective (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (K ⊗[R] S) (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))) (AlgEquiv.injective _)`. Use `etale_of_isReduced_of_perfectField K (K ⊗[R] S)` as an intermediate fact.

Conclude with `natCard_algHom_eq_finrank_of_etale_tower R S L K`.
-/
theorem natCard_algHom_eq_finrank_of_isReduced_of_isFractionRing [Module.Free R S]
    [Module.Finite R S] [IsReduced S] (K : Type*) [Field K] [PerfectField K] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L] [IsSepClosed L] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have : IsReduced (K ⊗[R] S) := by
    letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    haveI := IsLocalization.tensorRight (S := S) K (nonZeroDivisors R)
    exact isReduced_of_injective (IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (K ⊗[R] S)
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))))
      (AlgEquiv.injective _)
  have := etale_of_isReduced_of_perfectField K (K ⊗[R] S)
  exact natCard_algHom_eq_finrank_of_etale_tower R S L K

end Count

section Etale

variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]

variable (S) in

/- English proof (translation)
The claim follows from `have := Algebra.FormallyUnramified.finite_of_free K S natCard_algHom_eq_finrank_of_etale_baseChange K S L`.
-/
theorem natCard_algHom_eq_finrank_of_etale : Nat.card (S →ₐ[K] L) = finrank K S :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  natCard_algHom_eq_finrank_of_etale_baseChange K S L

variable (S) in

/- English proof (translation)
Use `Algebra.FormallyUnramified.finite_of_free K S` as an intermediate fact. Use `Fintype.ofFinite (S →ₐ[K] L)` as an intermediate fact. Rewrite using `[← Fintype.card_eq, h, ← natCard_algHom_eq_finrank_of_etale K S L, Nat.card_eq_fintype_card]`.
-/
theorem nonempty_equiv_algHom_of_etale {ι : Type*} [Fintype ι] (h : Fintype.card ι = finrank K S) :
    Nonempty (ι ≃ (S →ₐ[K] L)) := by
  have := Algebra.FormallyUnramified.finite_of_free K S
  have := Fintype.ofFinite (S →ₐ[K] L)
  rw [← Fintype.card_eq, h, ← natCard_algHom_eq_finrank_of_etale K S L, Nat.card_eq_fintype_card]

/- English proof (translation)
The claim follows from `have := Algebra.FormallyUnramified.finite_of_free K S algebraMap_norm_eq_prod_algHom_of_card (Nat.card_eq_fintype_card.symm.trans (natCard_algHom_eq_finrank_of_etale K S L)) Function.injective_id x`.
-/
theorem algebraMap_norm_eq_prod_algHom [Fintype (S →ₐ[K] L)] (x : S) :
    algebraMap K L (Algebra.norm K x) = ∏ P : S →ₐ[K] L, P x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_norm_eq_prod_algHom_of_card
    (Nat.card_eq_fintype_card.symm.trans (natCard_algHom_eq_finrank_of_etale K S L))
    Function.injective_id x

/- English proof (translation)
The claim follows from `have := Algebra.FormallyUnramified.finite_of_free K S algebraMap_trace_eq_sum_algHom_of_card (Nat.card_eq_fintype_card.symm.trans (natCard_algHom_eq_finrank_of_etale K S L)) Function.injective_id x`.
-/
theorem algebraMap_trace_eq_sum_algHom [Fintype (S →ₐ[K] L)] (x : S) :
    algebraMap K L (Algebra.trace K S x) = ∑ P : S →ₐ[K] L, P x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_trace_eq_sum_algHom_of_card
    (Nat.card_eq_fintype_card.symm.trans (natCard_algHom_eq_finrank_of_etale K S L))
    Function.injective_id x

variable {K L} {ι : Type*} [Fintype ι]

/- English proof (translation)
Rewrite using `[← natCard_algHom_eq_finrank_of_etale K S L, ← Nat.card_congr P, Nat.card_eq_fintype_card]`.
-/
theorem card_eq_finrank_of_equiv_algHom (P : ι ≃ (S →ₐ[K] L)) : Fintype.card ι = finrank K S := by
  rw [← natCard_algHom_eq_finrank_of_etale K S L, ← Nat.card_congr P, Nat.card_eq_fintype_card]

/- English proof (translation)
The claim follows from `have := Algebra.FormallyUnramified.finite_of_free K S algebraMap_norm_eq_prod_algHom_of_card (card_eq_finrank_of_equiv_algHom P) P.injective x`.
-/
theorem algebraMap_norm_eq_prod_of_equiv_algHom (P : ι ≃ (S →ₐ[K] L)) (x : S) :
    algebraMap K L (Algebra.norm K x) = ∏ j, P j x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_norm_eq_prod_algHom_of_card (card_eq_finrank_of_equiv_algHom P) P.injective x

/- English proof (translation)
The claim follows from `have := Algebra.FormallyUnramified.finite_of_free K S algebraMap_trace_eq_sum_algHom_of_card (card_eq_finrank_of_equiv_algHom P) P.injective x`.
-/
theorem algebraMap_trace_eq_sum_of_equiv_algHom (P : ι ≃ (S →ₐ[K] L)) (x : S) :
    algebraMap K L (Algebra.trace K S x) = ∑ j, P j x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_trace_eq_sum_algHom_of_card (card_eq_finrank_of_equiv_algHom P) P.injective x

/- English proof (translation)
The claim follows from `have := Algebra.FormallyUnramified.finite_of_free K S algebraMap_discr_eq_det_sq_of_card (card_eq_finrank_of_equiv_algHom P) P.injective v`.
-/
theorem algebraMap_discr_eq_det_sq_of_equiv_algHom [DecidableEq ι] (P : ι ≃ (S →ₐ[K] L))
    (v : ι → S) :
    algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2 :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_discr_eq_det_sq_of_card (card_eq_finrank_of_equiv_algHom P) P.injective v

/- English proof (translation)
Take `⟨P⟩` from `nonempty_equiv_algHom_of_etale K S (AlgebraicClosure K) (Module.finrank_eq_card_basis e).symm`. Introduce `h`. Conclude with `algebraMap_discr_basis_ne_zero e P.injective (by rw [h, map_zero])`.
-/
theorem discr_basis_ne_zero_of_etale [DecidableEq ι] (e : Basis ι K S) :
    Algebra.discr K e ≠ 0 := by
  obtain ⟨P⟩ := nonempty_equiv_algHom_of_etale K S (AlgebraicClosure K)
    (Module.finrank_eq_card_basis e).symm
  intro h
  exact algebraMap_discr_basis_ne_zero e P.injective (by rw [h, map_zero])

/- English proof (translation)
Assemble the required witnesses or components as `⟨card_eq_finrank_of_equiv_algHom P, algebraMap_discr_eq_det_sq_of_equiv_algHom P, algebraMap_norm_eq_prod_of_equiv_algHom P, algebraMap_trace_eq_sum_of_equiv_algHom P⟩`.
-/
theorem discr_norm_trace_of_etale [DecidableEq ι] (P : ι ≃ (S →ₐ[K] L)) :
    Fintype.card ι = finrank K S ∧
    (∀ v : ι → S, algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2) ∧
    (∀ x : S, algebraMap K L (Algebra.norm K x) = ∏ j, P j x) ∧
    (∀ x : S, algebraMap K L (Algebra.trace K S x) = ∑ j, P j x) :=
  ⟨card_eq_finrank_of_equiv_algHom P, algebraMap_discr_eq_det_sq_of_equiv_algHom P,
    algebraMap_norm_eq_prod_of_equiv_algHom P, algebraMap_trace_eq_sum_of_equiv_algHom P⟩

end Etale

section Reduced

variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
The claim follows from `have := etale_of_isReduced_of_perfectField K S ⟨card_eq_finrank_of_equiv_algHom P, algebraMap_discr_eq_det_sq_of_equiv_algHom P, algebraMap_norm_eq_prod_of_equiv_algHom P, algebraMap_trace_eq_sum_of_equiv_algHom P⟩`.
-/
theorem discr_norm_trace_of_isReduced (P : ι ≃ (S →ₐ[K] L)) :
    Fintype.card ι = finrank K S ∧
    (∀ v : ι → S, algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2) ∧
    (∀ x : S, algebraMap K L (Algebra.norm K x) = ∏ j, P j x) ∧
    (∀ x : S, algebraMap K L (Algebra.trace K S x) = ∑ j, P j x) :=
  have := etale_of_isReduced_of_perfectField K S
  ⟨card_eq_finrank_of_equiv_algHom P, algebraMap_discr_eq_det_sq_of_equiv_algHom P,
    algebraMap_norm_eq_prod_of_equiv_algHom P, algebraMap_trace_eq_sum_of_equiv_algHom P⟩

end Reduced

section Both

variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(algebraMap_discr_eq_det_sq_of_basis e hP v).symm, discr_eq_det_toMatrix_sq_mul e v, fun h => algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero]), addVal_discr_eq_two_mul_length_add e v, two_mul_length_le_addVal_discr e v⟩`.
-/
theorem det_algHom_sq_eq_discr_and_addVal (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    (Matrix.of fun i j => P j (v i)).det ^ 2 = algebraMap R L (Algebra.discr R v) ∧
    Algebra.discr R v = (e.toMatrix v).det ^ 2 * Algebra.discr R e ∧
    Algebra.discr R e ≠ 0 ∧
    addVal R (Algebra.discr R v) =
      2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) ∧
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) :=
  ⟨(algebraMap_discr_eq_det_sq_of_basis e hP v).symm, discr_eq_det_toMatrix_sq_mul e v,
    fun h => algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero]),
    addVal_discr_eq_two_mul_length_add e v, two_mul_length_le_addVal_discr e v⟩

end Both

/- English proof (translation)
Use `etale_of_isReduced_of_perfectField ℝ (ℝ × ℂ)` as an intermediate fact. Rewrite using `[natCard_algHom_eq_finrank_of_etale ℝ (ℝ × ℂ) ℂ]`. Simplify using the standard rewrite rules.
-/
example : Nat.card (ℝ × ℂ →ₐ[ℝ] ℂ) = 3 := by
  have := etale_of_isReduced_of_perfectField ℝ (ℝ × ℂ)
  rw [natCard_algHom_eq_finrank_of_etale ℝ (ℝ × ℂ) ℂ]
  simp

end GlobalTheory
