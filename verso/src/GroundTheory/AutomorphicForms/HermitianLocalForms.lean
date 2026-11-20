import Mathlib
import GroundTheory.AutomorphicForms.HermitianBinaryValues
import GroundTheory.AutomorphicForms.UnitaryGroupScheme

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

section QuadConj

variable {F : Type*} [Field F] (a : F)

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a 0), Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]`. Simplify using `[QuadraticAlgebra.basis]`. Expand and normalize the polynomial expressions, which then agree.
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
Rewrite using `[conj_apply, algebraTrace_quadraticAlgebra]`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.algebraMap_eq]; ring`.
-/
theorem conj_quadraticAlgebra (z : QuadraticAlgebra F a 0) :
    conj F (QuadraticAlgebra F a 0) z = star z := by
  rw [conj_apply, algebraTrace_quadraticAlgebra]
  ext <;> simp [QuadraticAlgebra.algebraMap_eq]; ring

end QuadConj

section Coordinates

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `exists_not_mem_range (F := K) (E := E)`. Use `set α := ζ - algebraMap K E (Algebra.trace K E ζ / 2) with hαdef`. Establish `hα : α ∉ Set.range (algebraMap K E)`. Introduce and unpack `⟨c, hc⟩`. Apply `hζ` to reduce the goal to its premises.

Conclude with `⟨c + Algebra.trace K E ζ / 2, by rw [map_add, hc, hαdef]; ring⟩`. Establish `htr : Algebra.trace K E α = 0`. Rewrite using `[hαdef, map_sub, trace_algebraMap_quadratic]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hconj : conj K E α = -α` using `by rw [conj_apply, htr, map_zero, zero_sub]`. Use `set d := -Algebra.norm K α with hd`. Establish `hαα : α * α = algebraMap K E d`. Use `mul_conj (F := K) α` as an intermediate fact. Rewrite `this` using `[hconj]`.

Rewrite using `[hd, map_neg]`. Take the linear combination `-this`. Set `f : QuadraticAlgebra K d 0 →ₐ[K] E` to `QuadraticAlgebra.lift ⟨α, by rw [hαα, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]⟩`. Establish `hf : ∀ z : QuadraticAlgebra K d 0, f z = algebraMap K E z.re + algebraMap K E z.im * α`. Introduce `z`.

Simplify using `[f, Algebra.smul_def]`. Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Rewrite `hz` using `[hf]`.

Distinguish the cases in `him : z.im = 0`. Rewrite `hz` using `[him, map_zero, zero_mul, add_zero]`. Use `ext`. Conclude with `(algebraMap K E).injective (by simp [hz])`. Simplify using `using him`.

It suffices to derive a contradiction. Apply `hα` to reduce the goal to its premises. Use `⟨-z.re / z.im, ?_⟩` and prove the remaining obligations. Establish `him' : algebraMap K E z.im ≠ 0` using `(map_ne_zero _).2 him`. Rewrite using `[map_div₀, map_neg]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hz`. Establish `hbij : Function.Bijective f`. Use `⟨hinj, ?_⟩` and prove the remaining obligations. Use `LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) (by rw [QuadraticAlgebra.finrank_eq_two, Algebra.IsQuadraticExtension.finrank_eq_two])` as an intermediate fact.

Conclude with `this.1 hinj`. Use `⟨d, (AlgEquiv.ofBijective f hbij).symm, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Apply `hα` to reduce the goal to its premises. Establish `h0 : (α - algebraMap K E r) * (α + algebraMap K E r) = 0`.

Rewrite `hαα` using `[← hr, map_pow]`. Take the linear combination `hαα`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `⟨r, by linear_combination -h⟩`. Conclude with `⟨-r, by rw [map_neg]; linear_combination -h⟩`.

Introduce `x`. Take `⟨z, rfl⟩` from `hbij.2 x`. Apply `(AlgEquiv.ofBijective f hbij).injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `conj K E (f z) = f (star ((AlgEquiv.ofBijective f hbij).symm (f z)))`.

Establish `: (AlgEquiv.ofBijective f hbij).symm (f z) = z` using `(AlgEquiv.ofBijective f hbij).symm_apply_apply z`. Rewrite using `[this, hf, hf, map_add, map_mul, conj_algebraMap, conj_algebraMap, hconj, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]`. Simplify using the standard rewrite rules.
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
Simplify using `[tensorQuadEquiv, quadTensorEquiv_tmul]`.
-/
theorem tensorQuadEquiv_tmul (r : R) (x : E) :
    tensorQuadEquiv ψ R (r ⊗ₜ x) =
      ⟨r * algebraMap K R (ψ x).re, r * algebraMap K R (ψ x).im⟩ := by
  simp [tensorQuadEquiv, quadTensorEquiv_tmul]

variable {ψ} in

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[conjBase_tmul, tensorQuadEquiv_tmul, tensorQuadEquiv_tmul, hψ]`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy, star_add]`.
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
Assemble the required witnesses or components as `⟨1, by simp, by simp [Matrix.map_one _ (map_zero s) (map_one s)]⟩`.
-/
theorem IsCongr.refl (H : Matrix ι ι A) : IsCongr s H H :=
  ⟨1, by simp, by simp [Matrix.map_one _ (map_zero s) (map_one s)]⟩

variable {s}

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Take `⟨Q, hQ, rfl⟩` from `h'`. Use `⟨P * Q, by rw [det_mul]; exact hP.mul hQ, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem IsCongr.trans {H H' H'' : Matrix ι ι A} (h : IsCongr s H H') (h' : IsCongr s H' H'') :
    IsCongr s H H'' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨Q, hQ, rfl⟩ := h'
  refine ⟨P * Q, by rw [det_mul]; exact hP.mul hQ, ?_⟩
  rw [Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Use `⟨P⁻¹, (isUnit_nonsing_inv_det_iff).2 hP, ?_⟩` and prove the remaining obligations. Establish `h1 : P * P⁻¹ = 1` using `mul_nonsing_inv P hP`. Establish `h2 : (P.map s) * (P⁻¹.map s) = 1`. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero s) (map_one s)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = H := by rw [h1, h2, transpose_one, Matrix.one_mul, Matrix.mul_one]`.
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
Take `⟨P, hP, rfl⟩` from `h`. Use `⟨P.map φ, ?_, (map_unitaryExpr φ hφ H P).symm⟩` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hP.map φ`.
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
Use extensionality with `i j`. Rewrite using `[gram_apply, diagForm_apply, Pi.basisFun_apply, Pi.basisFun_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[hk]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[Ne.symm hij]`. Simplify using `[hk]`.
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
Use `set b := Pi.basisFun A ι`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he⟩`. Use `⟨LinearMap.toMatrix b b (e : (ι → A) →ₗ[A] (ι → A)), LinearEquiv.isUnit_det e b b, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Rewrite using `[← sesq_apply_map_basis]`. Simplify using `only [LinearEquiv.coe_coe, he, gram_apply]`. Introduce and unpack `⟨P, hP, hPH⟩`. Establish `hP' : IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b P)).det`. Rewrite using `[LinearMap.toMatrix_toLin]` and apply the resulting hypothesis.

Use `⟨LinearEquiv.ofIsUnitDet hP', fun x y => ?_⟩` and prove the remaining obligations. Establish `key : (h'.toSesq.comp (Matrix.toLin b b P)).compl₂ (Matrix.toLin b b P) = h.toSesq`. Use `LinearMap.ext_basis b b fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun hPH i) j` as an intermediate fact. Rewrite `this` using `[← LinearMap.toMatrix_toLin b b P, ← sesq_apply_map_basis]`.

Rewrite using `[LinearMap.compl₂_apply, LinearMap.comp_apply, this, gram_apply]`. Conclude with `LinearMap.congr_fun₂ key x y`.
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
Use `⟨Fin.consLinearEquiv A (fun _ : Fin (n + 1) => A), fun p q => ?_⟩` and prove the remaining obligations. Rewrite using `[diagForm_apply, Fin.sum_univ_succ, HermitianForm.prod_apply, HermitianForm.ofUnit_apply, diagForm_apply]`. Simplify using the standard rewrite rules.
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
