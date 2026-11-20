import Mathlib
import GroundTheory.AutomorphicForms.HermitianBinaryValues
import GroundTheory.AutomorphicForms.UnitaryGroupScheme

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

section QuadConj

variable {F : Type*} [Field F] (a : F)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem algebraTrace_quadraticAlgebra (z : QuadraticAlgebra F a 0) :
    Algebra.trace F (QuadraticAlgebra F a 0) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a 0), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp [QuadraticAlgebra.basis]
  ring

instance isQuadraticExtension_quadraticAlgebra :
    Algebra.IsQuadraticExtension F (QuadraticAlgebra F a 0) :=
  ⟨QuadraticAlgebra.finrank_eq_two a 0⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem conj_quadraticAlgebra (z : QuadraticAlgebra F a 0) :
    conj F (QuadraticAlgebra F a 0) z = star z := by
  rw [conj_apply, algebraTrace_quadraticAlgebra]
  ext <;> simp [QuadraticAlgebra.algebraMap_eq]; ring

end QuadConj

section Coordinates

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities.

By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_algEquiv_quadraticAlgebra (h2 : (2 : K) ≠ 0) :
    ∃ (d : K) (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0), (∀ r : K, r ^ 2 ≠ d) ∧
      ∀ x, ψ (conj K E x) = star (ψ x) := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := K) (E := E)
  set α := ζ - algebraMap K E (Algebra.trace K E ζ / 2) with hαdef
  have hα : α ∉ Set.range (algebraMap K E) := by
    rintro ⟨c, hc⟩
    apply hζ
    exact ⟨c + Algebra.trace K E ζ / 2, by rw [map_add, hc, hαdef]; ring⟩
  have htr : Algebra.trace K E α = 0 := by
    rw [hαdef, map_sub, trace_algebraMap_quadratic]
    field_simp
    ring
  have hconj : conj K E α = -α := by rw [conj_apply, htr, map_zero, zero_sub]
  set d := -Algebra.norm K α with hd
  have hαα : α * α = algebraMap K E d := by
    have := mul_conj (F := K) α
    rw [hconj] at this
    rw [hd, map_neg]
    linear_combination -this
  let f : QuadraticAlgebra K d 0 →ₐ[K] E :=
    QuadraticAlgebra.lift ⟨α, by rw [hαα, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]⟩
  have hf : ∀ z : QuadraticAlgebra K d 0,
      f z = algebraMap K E z.re + algebraMap K E z.im * α := by
    intro z
    simp [f, Algebra.smul_def]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [hf] at hz
    by_cases him : z.im = 0
    · rw [him, map_zero, zero_mul, add_zero] at hz
      ext
      · exact (algebraMap K E).injective (by simp [hz])
      · simpa using him
    · exfalso
      apply hα
      refine ⟨-z.re / z.im, ?_⟩
      have him' : algebraMap K E z.im ≠ 0 := (map_ne_zero _).2 him
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hz
  have hbij : Function.Bijective f := by
    refine ⟨hinj, ?_⟩
    have := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by rw [QuadraticAlgebra.finrank_eq_two, Algebra.IsQuadraticExtension.finrank_eq_two])
    exact this.1 hinj
  refine ⟨d, (AlgEquiv.ofBijective f hbij).symm, ?_, ?_⟩
  · intro r hr
    apply hα
    have h0 : (α - algebraMap K E r) * (α + algebraMap K E r) = 0 := by
      rw [← hr, map_pow] at hαα
      linear_combination hαα
    rcases mul_eq_zero.1 h0 with h | h
    · exact ⟨r, by linear_combination -h⟩
    · exact ⟨-r, by rw [map_neg]; linear_combination -h⟩
  · intro x
    obtain ⟨z, rfl⟩ := hbij.2 x
    apply (AlgEquiv.ofBijective f hbij).injective
    rw [AlgEquiv.apply_symm_apply]
    change conj K E (f z) = f (star ((AlgEquiv.ofBijective f hbij).symm (f z)))
    have : (AlgEquiv.ofBijective f hbij).symm (f z) = z :=
      (AlgEquiv.ofBijective f hbij).symm_apply_apply z
    rw [this, hf, hf, map_add, map_mul, conj_algebraMap, conj_algebraMap, hconj,
      QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    simp

end Coordinates

section BaseChange

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
  {d : K} (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0) (R : Type*) [CommRing R] [Algebra K R]

def tensorQuadEquiv : R ⊗[K] E ≃ₐ[R] QuadraticAlgebra R (algebraMap K R d) 0 :=
  (Algebra.TensorProduct.congr AlgEquiv.refl ψ).trans (quadTensorEquiv d R)

omit [Algebra.IsQuadraticExtension K E] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem tensorQuadEquiv_tmul (r : R) (x : E) :
    tensorQuadEquiv ψ R (r ⊗ₜ x) =
      ⟨r * algebraMap K R (ψ x).re, r * algebraMap K R (ψ x).im⟩ := by
  simp [tensorQuadEquiv, quadTensorEquiv_tmul]

variable {ψ} in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Treat this case separately.
-/
theorem tensorQuadEquiv_conjBase (hψ : ∀ x, ψ (conj K E x) = star (ψ x)) (z : R ⊗[K] E) :
    tensorQuadEquiv ψ R (conjBase K E R z) = star (tensorQuadEquiv ψ R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [conjBase_tmul, tensorQuadEquiv_tmul, tensorQuadEquiv_tmul, hψ]
    ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]

end BaseChange

section Congr

variable {A : Type*} [CommRing A] (s : A →+* A) {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsCongr (H H' : Matrix ι ι A) : Prop :=
  ∃ P : Matrix ι ι A, IsUnit P.det ∧ (P.map s)ᵀ * H * P = H'

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsCongr.refl (H : Matrix ι ι A) : IsCongr s H H :=
  ⟨1, by simp, by simp [Matrix.map_one _ (map_zero s) (map_one s)]⟩

variable {s}

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem IsCongr.trans {H H' H'' : Matrix ι ι A} (h : IsCongr s H H') (h' : IsCongr s H' H'') :
    IsCongr s H H'' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨Q, hQ, rfl⟩ := h'
  refine ⟨P * Q, by rw [det_mul]; exact hP.mul hQ, ?_⟩
  rw [Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem IsCongr.symm {H H' : Matrix ι ι A} (h : IsCongr s H H') :
    IsCongr s H' H := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P⁻¹, (isUnit_nonsing_inv_det_iff).2 hP, ?_⟩
  have h1 : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have h2 : (P.map s) * (P⁻¹.map s) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero s) (map_one s)]
  calc (P⁻¹.map s)ᵀ * ((P.map s)ᵀ * H * P) * P⁻¹
      = ((P.map s) * (P⁻¹.map s))ᵀ * H * (P * P⁻¹) := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [h1, h2, transpose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsCongr.map {B : Type*} [CommRing B] {t : B →+* B} (φ : A →+* B)
    (hφ : ∀ x, φ (s x) = t (φ x)) {H H' : Matrix ι ι A} (h : IsCongr s H H') :
    IsCongr t (H.map φ) (H'.map φ) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.map φ, ?_, (map_unitaryExpr φ hφ H P).symm⟩
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hP.map φ

end Congr

section Bridge

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem gram_diagForm (a : ι → Fˣ) :
    gram (diagForm (E := A) a).toSesq (Pi.basisFun A ι) =
      diagonal fun i => algebraMap F A (a i) := by
  ext i j
  rw [gram_apply, diagForm_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simp [Ne.symm hij]
    · simp [hk]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isometric_iff_isCongr (h h' : HermitianForm F A (ι → A)) :
    HermitianForm.Isometric h h' ↔
      IsCongr (conjHom F A) (gram h'.toSesq (Pi.basisFun A ι)) (gram h.toSesq (Pi.basisFun A ι)) := by
  set b := Pi.basisFun A ι
  constructor
  · rintro ⟨e, he⟩
    refine ⟨LinearMap.toMatrix b b (e : (ι → A) →ₗ[A] (ι → A)), LinearEquiv.isUnit_det e b b, ?_⟩
    ext i j
    rw [← sesq_apply_map_basis]
    simp only [LinearEquiv.coe_coe, he, gram_apply]
  · rintro ⟨P, hP, hPH⟩
    have hP' : IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b P)).det := by
      rwa [LinearMap.toMatrix_toLin]
    refine ⟨LinearEquiv.ofIsUnitDet hP', fun x y => ?_⟩
    have key : (h'.toSesq.comp (Matrix.toLin b b P)).compl₂ (Matrix.toLin b b P) = h.toSesq := by
      refine LinearMap.ext_basis b b fun i j => ?_
      have := congrFun (congrFun hPH i) j
      rw [← LinearMap.toMatrix_toLin b b P, ← sesq_apply_map_basis] at this
      rw [LinearMap.compl₂_apply, LinearMap.comp_apply, this, gram_apply]
    exact LinearMap.congr_fun₂ key x y

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem isometric_prod_diagForm_cons {n : ℕ} (a₀ : Fˣ) (a : Fin n → Fˣ) :
    HermitianForm.Isometric ((HermitianForm.ofUnit (E := A) a₀).prod (diagForm a))
      (diagForm (Fin.cons a₀ a : Fin (n + 1) → Fˣ)) := by
  refine ⟨Fin.consLinearEquiv A (fun _ : Fin (n + 1) => A), fun p q => ?_⟩
  rw [diagForm_apply, Fin.sum_univ_succ, HermitianForm.prod_apply, HermitianForm.ofUnit_apply,
    diagForm_apply]
  simp

end Bridge

section LocalQuad

variable {F : Type*} [Field F] (d : F) {ι : Type*} [Fintype ι] [DecidableEq ι]

end LocalQuad

end GroundTheory.Automorphic
