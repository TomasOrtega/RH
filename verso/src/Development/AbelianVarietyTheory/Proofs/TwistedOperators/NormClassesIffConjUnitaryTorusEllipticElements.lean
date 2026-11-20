import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} {P : PPol σ r}
  {k : Type} [CommRing k] [Algebra F k]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algBase_tmul (a : k) (e : E) :
    algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (a ⊗ₜ e) = a ⊗ₜ algebraMap E (Fld P) e := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Matrix.det (((alphaRat P).1 : Matrix (Fin 1) (Fin 1) (Fld P)).map (inclR k)) = _`. Rewrite using `[Matrix.det_fin_one]`. Simplify using `[alphaRat, inclR]`.
-/
theorem torUnit_alpha :
    (torUnit (diagH (star' P) (one₁ P) k (alphaRat P))).1 = (1 : k) ⊗ₜ[F] alpha P := by
  change Matrix.det (((alphaRat P).1 : Matrix (Fin 1) (Fin 1) (Fld P)).map (inclR k)) = _
  rw [Matrix.det_fin_one]
  simp [alphaRat, inclR]

/- English proof (translation)
Set `S : Subalgebra (k ⊗[F] E) (k ⊗[F] Fld P)` to `{ carrier := {z | ∀ y, f (z * y) = z * f y} mul_mem' := fun {a b} ha hb y => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[mul_assoc, ha, hb, mul_assoc]`. Use the proof step `add_mem' := fun {a b} ha hb y => by`. Simplify using `only [Set.mem_setOf_eq] at *`.

Rewrite using `[add_mul, map_add, ha, hb, add_mul]`. Use the proof step `algebraMap_mem' := fun a y => by`. Rewrite using `[← Algebra.smul_def, map_smul, Algebra.smul_def] }`. Establish `h1 : ∀ l : Fld P, (1 : k) ⊗ₜ[F] l ∈ S`. Introduce `l`.

Establish `hl : l ∈ Algebra.adjoin E {alpha P}`. Rewrite using `[show Algebra.adjoin E {alpha P} = ⊤ from AdjoinRoot.adjoinRoot_eq_top]`. Conclude with `Algebra.mem_top`. Proceed by induction on `hl using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `hf`. Consider the case `algebraMap e`. Rewrite using `[← algBase_tmul]`. Conclude with `S.algebraMap_mem _`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[TensorProduct.tmul_add]`. Conclude with `S.add_mem hx hy`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[← mul_one (1 : k), ← Algebra.TensorProduct.tmul_mul_tmul]`.

Conclude with `S.mul_mem hx hy`. Establish `h2 : ∀ z, z ∈ S`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact S.zero_mem`.

Consider the case `tmul a l`. Establish `e : a ⊗ₜ[F] l = algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (a ⊗ₜ 1) * ((1 : k) ⊗ₜ l)`. Rewrite using `[algBase_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_one, one_mul]`. Rewrite using `[e]`. Conclude with `S.mul_mem (S.algebraMap_mem _) (h1 l)`.

Consider the case `add a b ha hb => exact S.add_mem ha hb`. Conclude with `h2 z y`.
-/
theorem comm_of_alpha (f : (k ⊗[F] Fld P) →ₗ[k ⊗[F] E] (k ⊗[F] Fld P))
    (hf : ∀ y, f ((1 : k) ⊗ₜ[F] alpha P * y) = (1 : k) ⊗ₜ[F] alpha P * f y) (z y : k ⊗[F] Fld P) :
    f (z * y) = z * f y := by
  let S : Subalgebra (k ⊗[F] E) (k ⊗[F] Fld P) :=
    { carrier := {z | ∀ y, f (z * y) = z * f y}
      mul_mem' := fun {a b} ha hb y => by
        simp only [Set.mem_setOf_eq] at *
        rw [mul_assoc, ha, hb, mul_assoc]
      add_mem' := fun {a b} ha hb y => by
        simp only [Set.mem_setOf_eq] at *
        rw [add_mul, map_add, ha, hb, add_mul]
      algebraMap_mem' := fun a y => by
        rw [← Algebra.smul_def, map_smul, Algebra.smul_def] }
  have h1 : ∀ l : Fld P, (1 : k) ⊗ₜ[F] l ∈ S := by
    intro l
    have hl : l ∈ Algebra.adjoin E {alpha P} := by
      rw [show Algebra.adjoin E {alpha P} = ⊤ from AdjoinRoot.adjoinRoot_eq_top]
      exact Algebra.mem_top
    induction hl using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact hf
    | algebraMap e =>
      rw [← algBase_tmul]
      exact S.algebraMap_mem _
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← mul_one (1 : k), ← Algebra.TensorProduct.tmul_mul_tmul]
      exact S.mul_mem hx hy
  have h2 : ∀ z, z ∈ S := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | tmul a l =>
      have e : a ⊗ₜ[F] l = algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (a ⊗ₜ 1) * ((1 : k) ⊗ₜ l) := by
        rw [algBase_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_one, one_mul]
      rw [e]
      exact S.mul_mem (S.algebraMap_mem _) (h1 l)
    | add a b ha hb => exact S.add_mem ha hb
  exact h2 z y

/- English proof (translation)
Set `b` to `Module.finBasis E (Fld P)`. Establish `hB` using `traceForm_nondegenerate E (Fld P)`. Set `d` to `(Algebra.traceForm E (Fld P)).dualBasis hB b`. Establish `key : ∀ z : k ⊗[F] Fld P, ∑ i, algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (trBase P k (z * ((1 : k) ⊗ₜ b i))) * ((1 : k) ⊗ₜ d i) = z`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add u v hu hv`. Simplify using `only [add_mul, map_add, Finset.sum_add_distrib, hu, hv]`. Consider the case `tmul a l`.

Establish `hl : ∑ i, Algebra.trace E (Fld P) (l * b i) • d i = l` using `by conv_rhs => rw [← d.sum_repr l]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]`. Establish `e : ∀ i, algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (trBase P k (a ⊗ₜ l * ((1 : k) ⊗ₜ b i))) * ((1 : k) ⊗ₜ d i) = a ⊗ₜ (Algebra.trace E (Fld P) (l * b i) • d i)`. Introduce `i`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Simplify using `only [trBase, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply]`. Rewrite using `[algBase_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]`. Repeatedly rewrite using `[e]`. Rewrite using `[← TensorProduct.tmul_sum, hl]`.

Rewrite using `[← key w]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [hw, map_zero, zero_mul]`.
-/
theorem trBase_perfect [NumberField E] (w : k ⊗[F] Fld P) (hw : ∀ y, trBase P k (w * y) = 0) : w = 0 := by
  classical
  let b := Module.finBasis E (Fld P)
  have hB := traceForm_nondegenerate E (Fld P)
  let d := (Algebra.traceForm E (Fld P)).dualBasis hB b
  have key : ∀ z : k ⊗[F] Fld P,
      ∑ i, algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (trBase P k (z * ((1 : k) ⊗ₜ b i))) * ((1 : k) ⊗ₜ d i) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      simp only [add_mul, map_add, Finset.sum_add_distrib, hu, hv]
    | tmul a l =>
      have hl : ∑ i, Algebra.trace E (Fld P) (l * b i) • d i = l := by
        conv_rhs => rw [← d.sum_repr l]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
      have e : ∀ i, algebraMap (k ⊗[F] E) (k ⊗[F] Fld P) (trBase P k (a ⊗ₜ l * ((1 : k) ⊗ₜ b i))) *
          ((1 : k) ⊗ₜ d i) = a ⊗ₜ (Algebra.trace E (Fld P) (l * b i) • d i) := by
        intro i
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        simp only [trBase, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply]
        rw [algBase_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
      simp_rw [e]
      rw [← TensorProduct.tmul_sum, hl]
  rw [← key w]
  exact Finset.sum_eq_zero fun i _ => by rw [hw, map_zero, zero_mul]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem hform_eq_vecMul {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform s G a b = Matrix.vecMul (fun i => s (a i)) G ⬝ᵥ b := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `e : (fun i => s ((M *ᵥ a) i)) = Matrix.vecMul (fun i => s (a i)) (Formalism.UG.cT s M)`. Use extensionality with `i`. Simplify using `[Formalism.UG.cT, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]`. Rewrite using `[hform_eq_vecMul, hform_eq_vecMul, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, h]`.
-/
theorem hform_mulVec_of_unitary {A : Type} [CommRing A] (s : A →+* A) (G M : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT s M * G * M = G) (a b : Fin n → A) :
    Formalism.UG.hform s G (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform s G a b := by
  have e : (fun i => s ((M *ᵥ a) i)) = Matrix.vecMul (fun i => s (a i)) (Formalism.UG.cT s M) := by
    ext i
    simp [Formalism.UG.cT, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]
  rw [hform_eq_vecMul, hform_eq_vecMul, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, h]

/- English proof (translation)
The claim follows from `Matrix.toLin'.injective (LinearMap.ext fun v => by simp only [Matrix.toLin'_apply, h])`.
-/
theorem matrix_ext_mulVec {A : Type} [CommRing A] {M N : Matrix (Fin n) (Fin n) A} (h : ∀ v, M *ᵥ v = N *ᵥ v) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simp only [Matrix.toLin'_apply, h])

variable {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Use `matrix_ext_mulVec fun v => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `φ.surjective v`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulMat_mulVec, hc, hc, mulMat_mulVec, mul_left_comm]`.
-/
theorem mulMat_intertwine {φ φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) (c : k ⊗[F] Fld P) (hc : ∀ y, G *ᵥ φ y = φ' (c * y))
    (u : k ⊗[F] Fld P) : G * mulMat φ u = mulMat φ' u * G := by
  refine matrix_ext_mulVec fun v => ?_
  obtain ⟨y, rfl⟩ := φ.surjective v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulMat_mulVec, hc, hc, mulMat_mulVec, mul_left_comm]

/- English proof (translation)
Set `ψ : (k ⊗[F] Fld P) →ₗ[k ⊗[F] E] (k ⊗[F] Fld P)` to `φ'.symm.toLinearMap ∘ₗ Matrix.toLin' (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) ∘ₗ φ.toLinearMap`. Set `ψ' : (k ⊗[F] Fld P) →ₗ[k ⊗[F] E] (k ⊗[F] Fld P)` to `φ.symm.toLinearMap ∘ₗ Matrix.toLin' ((G⁻¹ : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) ∘ₗ φ'.toLinearMap`. Establish `hψ : ∀ y, ψ y = φ'.symm ((G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y)` using `fun y => rfl`. Establish `hψα : ∀ y, ψ ((1 : k) ⊗ₜ[F] alpha P * y) = (1 : k) ⊗ₜ[F] alpha P * ψ y`. Introduce `y`.

Rewrite using `[hψ, hψ, ← mulMat_mulVec, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec]`. Take `⟨w, hw⟩` from `φ'.surjective ((G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y)`. Rewrite using `[← hw, mulMat_mulVec, φ'.symm_apply_apply, φ'.symm_apply_apply]`. Establish `hψψ' : ψ (ψ' 1) = 1`. Express the relevant statement in the definitionally equal form `φ'.symm ((G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ (φ.symm (((G⁻¹ : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ' 1))) = 1`.

Rewrite using `[φ.apply_symm_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, φ'.symm_apply_apply]`. Establish `hmul : ∀ z, ψ z = z * ψ 1` using `fun z => by`. Rewrite using `[← comm_of_alpha ψ hψα z 1, mul_one]`. Establish `hu : ψ' 1 * ψ 1 = 1` using `by rw [← hmul, hψψ']`. Use `⟨Units.mkOfMulEqOne (ψ 1) (ψ' 1) (by rw [mul_comm, hu]), fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mkOfMulEqOne, mul_comm, ← hmul, hψ, φ'.apply_symm_apply]`.
-/
theorem exists_unit_of_comm {φ φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (G : GL (Fin n) (k ⊗[F] E))
    (hG : (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * mulMat φ ((1 : k) ⊗ₜ[F] alpha P) =
      mulMat φ' ((1 : k) ⊗ₜ[F] alpha P) * G) :
    ∃ c : (k ⊗[F] Fld P)ˣ, ∀ y, (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y = φ' (c * y) := by
  let ψ : (k ⊗[F] Fld P) →ₗ[k ⊗[F] E] (k ⊗[F] Fld P) :=
    φ'.symm.toLinearMap ∘ₗ Matrix.toLin' (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) ∘ₗ φ.toLinearMap
  let ψ' : (k ⊗[F] Fld P) →ₗ[k ⊗[F] E] (k ⊗[F] Fld P) :=
    φ.symm.toLinearMap ∘ₗ Matrix.toLin' ((G⁻¹ : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) ∘ₗ
      φ'.toLinearMap
  have hψ : ∀ y, ψ y = φ'.symm ((G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y) := fun y => rfl
  have hψα : ∀ y, ψ ((1 : k) ⊗ₜ[F] alpha P * y) = (1 : k) ⊗ₜ[F] alpha P * ψ y := by
    intro y
    rw [hψ, hψ, ← mulMat_mulVec, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec]
    obtain ⟨w, hw⟩ := φ'.surjective ((G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y)
    rw [← hw, mulMat_mulVec, φ'.symm_apply_apply, φ'.symm_apply_apply]
  have hψψ' : ψ (ψ' 1) = 1 := by
    change φ'.symm ((G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ (φ.symm
      (((G⁻¹ : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ' 1))) = 1
    rw [φ.apply_symm_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, φ'.symm_apply_apply]
  have hmul : ∀ z, ψ z = z * ψ 1 := fun z => by
    rw [← comm_of_alpha ψ hψα z 1, mul_one]
  have hu : ψ' 1 * ψ 1 = 1 := by rw [← hmul, hψψ']
  refine ⟨Units.mkOfMulEqOne (ψ 1) (ψ' 1) (by rw [mul_comm, hu]), fun y => ?_⟩
  rw [Units.val_mkOfMulEqOne, mul_comm, ← hmul, hψ, φ'.apply_symm_apply]

/- English proof (translation)
Use `sub_eq_zero.1 (trBase_perfect _ fun y => ?_)` and prove the remaining obligations. Establish `e : hx P k x y 1 = hx P k x' (c * y) (c * 1)`. Rewrite using `[← h, ← hform_mulVec_of_unitary _ _ _ hu, hc, hc, h']`. Simplify using `only [hx, mul_one, map_one] at e`. Rewrite using `[sub_mul, map_sub, e, sub_eq_zero]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_of_unitary [NumberField E] {x x' : k ⊗[F] Fld P} {φ φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (h' : IsIsom P k J x' φ') (G : Matrix (Fin n) (Fin n) (k ⊗[F] E))
    (hu : Formalism.UG.cT (sigR k σ) G * JR k J * G = JR k J) (c : k ⊗[F] Fld P)
    (hc : ∀ y, G *ᵥ φ y = φ' (c * y)) : x = x' * c * sigR k (star' P) c := by
  refine sub_eq_zero.1 (trBase_perfect _ fun y => ?_)
  have e : hx P k x y 1 = hx P k x' (c * y) (c * 1) := by
    rw [← h, ← hform_mulVec_of_unitary _ _ _ hu, hc, hc, h']
  simp only [hx, mul_one, map_one] at e
  rw [sub_mul, map_sub, e, sub_eq_zero]
  congr 1
  ring

/- English proof (translation)
Establish `: ∀ p q : ↥(HR k σ J), ((p.1 : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = q.1 → p = q` using `fun p q e => Subtype.ext (Units.ext e)`. Conclude with `this a b h`.
-/
theorem ha_ext {a b : HA k σ J}
    (h : ((HA.mat k σ J a : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = HA.mat k σ J b) :
    a = b := by
  have : ∀ p q : ↥(HR k σ J), ((p.1 : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = q.1 → p = q :=
    fun p q e => Subtype.ext (Units.ext e)
  exact this a b h

/- English proof (translation)
The claim follows from `(show ↥(HR k σ J) from g).2`.
-/
theorem ha_unitary (g : HA k σ J) :
    Formalism.UG.cT (sigR k σ) ((HA.mat k σ J g : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * JR k J *
      (HA.mat k σ J g : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = JR k J :=
  (show ↥(HR k σ J) from g).2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ha_mat_mul (a b : HA k σ J) : HA.mat k σ J (a * b) = HA.mat k σ J a * HA.mat k σ J b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ha_mat_inv (a : HA k σ J) : HA.mat k σ J a⁻¹ = (HA.mat k σ J a)⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ha_mat_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) :
    ((HA.mat k σ J (torEmb h t) : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) =
      mulMat φ (torUnit t).1 := rfl

/- English proof (translation)
Rewrite using `[gam, ha_mat_torEmb, torUnit_alpha]`.
-/
theorem ha_mat_gam {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) :
    ((HA.mat k σ J (gam h) : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) =
      mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  rw [gam, ha_mat_torEmb, torUnit_alpha]

/- English proof (translation)
Apply `ha_ext` to reduce the goal to its premises. Rewrite using `[ha_mat_mul, ha_mat_mul, ha_mat_inv, Units.val_mul, Units.val_mul, hG, mul_assoc, Units.mul_inv, mul_one]`.
-/
theorem ha_conj_of_intertwine (g a b : HA k σ J)
    (hG : ((HA.mat k σ J g : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * HA.mat k σ J a =
      (HA.mat k σ J b : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * HA.mat k σ J g) : b = g * a * g⁻¹ := by
  apply ha_ext
  rw [ha_mat_mul, ha_mat_mul, ha_mat_inv, Units.val_mul, Units.val_mul, hG, mul_assoc, Units.mul_inv, mul_one]

/- English proof (translation)
Rewrite using `[← e, ha_mat_mul, ha_mat_mul, ha_mat_inv, Units.val_mul, Units.val_mul, mul_assoc _ _ (HA.mat k σ J g).1, Units.inv_mul, mul_one]`.
-/
theorem intertwine_of_conj (g a b : HA k σ J) (e : g * a * g⁻¹ = b) :
    ((HA.mat k σ J g : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * HA.mat k σ J a =
      (HA.mat k σ J b : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * HA.mat k σ J g := by
  rw [← e, ha_mat_mul, ha_mat_mul, ha_mat_inv, Units.val_mul, Units.val_mul, mul_assoc _ _ (HA.mat k σ J g).1,
    Units.inv_mul, mul_one]

/- English proof (translation)
Apply `ha_conj_of_intertwine` to reduce the goal to its premises. Rewrite using `[ha_mat_torEmb, ha_mat_torEmb]`. Conclude with `mulMat_intertwine _ c hc _`.
-/
theorem torEmb_conj {x x' : k ⊗[F] Fld P} {φ φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (h' : IsIsom P k J x' φ') (g : HA k σ J) (c : k ⊗[F] Fld P)
    (hc : ∀ y, ((HA.mat k σ J g : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y = φ' (c * y))
    (t : Tor P k) : torEmb h' t = g * torEmb h t * g⁻¹ := by
  apply ha_conj_of_intertwine
  rw [ha_mat_torEmb, ha_mat_torEmb]
  exact mulMat_intertwine _ c hc _

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ r n P J _ k _ _ x φ h x' φ' h'`. Use `⟨fun heq => ?_, fun hcj => ?_, fun g hg t => ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite `heq` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Take `⟨c, hc⟩` from `heq`. Establish `hcU : c * Units.map (sigR k (star' P)).toMonoidHom c = (x.1)⁻¹ * x'.1` using `hc`.

Establish `hxU : x'.1 = x.1 * (c * Units.map (sigR k (star' P)).toMonoidHom c)`. Rewrite using `[hcU, mul_inv_cancel_left]`. Establish `hxx : (x'.1 : (k ⊗[F] Fld P)ˣ).1 = x.1.1 * (c.1 * sigR k (star' P) c.1)`. Rewrite using `[hxU]`. Both sides reduce to the same expression.

Set `mc : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (k ⊗[F] Fld P)` to `LinearEquiv.ofLinear (LinearMap.mulLeft (k ⊗[F] E) ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P)) (LinearMap.mulLeft (k ⊗[F] E) (c : k ⊗[F] Fld P)) (LinearMap.ext fun y => by simp [← mul_assoc]) (LinearMap.ext fun y => by simp [← mul_assoc])`. Set `L` to `(φ.symm.trans mc).trans φ'`. Set `G : GL (Fin n) (k ⊗[F] E)` to `⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap, matrix_ext_mulVec fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]`. Conclude with `L.apply_symm_apply v,`.

Use `matrix_ext_mulVec fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]`. Conclude with `L.symm_apply_apply v⟩`. Establish `hGv : ∀ y, (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y = φ' (((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) * y)` using `fun y => by`. Express the relevant statement in the definitionally equal form `LinearMap.toMatrix' L.toLinearMap *ᵥ φ y = _`.

Rewrite using `[LinearMap.toMatrix'_mulVec]`. Simplify using `[L, mc]`. Establish `hU : Formalism.UG.cT (sigR k σ) (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * JR k J * (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = JR k J` using `unitary_of_hform _ _ _ fun a b => by`. Take `⟨y', rfl⟩` from `φ.surjective a`. Take `⟨y, rfl⟩` from `φ.surjective b`.

Rewrite using `[hGv, hGv, h', h, hx, hx, hxx]`. Use `congr 1`. Establish `e1 : (c : k ⊗[F] Fld P) * ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) = 1` using `c.mul_inv`. Establish `e2 : sigR k (star' P) (c : k ⊗[F] Fld P) * sigR k (star' P) ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) = 1`. Rewrite using `[← map_mul, e1, map_one]`.

Rewrite using `[map_mul]`. Take the linear combination `(x.1.1 * y * sigR k (star' P) y' * sigR k (star' P) (c : k ⊗[F] Fld P) * sigR k (star' P) ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P)) * e1 + (x.1.1 * y * sigR k (star' P) y') * e2`. Conclude with `⟨show HA k σ J from ⟨G, hU⟩, torEmb_conj h h' _ _ hGv⟩`. Take `⟨g, hg⟩` from `isConj_iff.1 hcj`. Establish `hG` using `intertwine_of_conj g _ _ hg`.

Rewrite `hG` using `[ha_mat_gam, ha_mat_gam]`. Take `⟨c, hc⟩` from `exists_unit_of_comm _ hG`. Establish `e` using `eq_of_unitary h h' _ (ha_unitary g) c hc`. Establish `eU : x.1 = x'.1 * c * Units.map (sigR k (star' P)).toMonoidHom c` using `Units.ext e`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Use `⟨c⁻¹, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c⁻¹ * Units.map (sigR k (star' P)).toMonoidHom c⁻¹ = (x.1)⁻¹ * x'.1`. Rewrite using `[eU, map_inv]`. Use `group`. Conclude with `mul_comm _ _`.

Establish `hG` using `intertwine_of_conj g _ _ hg.symm`. Rewrite `hG` using `[ha_mat_gam, ha_mat_gam]`. Take `⟨c, hc⟩` from `exists_unit_of_comm _ hG`. Conclude with `torEmb_conj h h' g c hc t`. Set `Gm : Matrix (Fin n) (Fin n) (k ⊗[F] E)` to `(HA.mat k σ J g : GL (Fin n) (k ⊗[F] E))`.

Set `Ge : (Fin n → k ⊗[F] E) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)` to `LinearEquiv.ofLinear (Matrix.toLin' Gm) (Matrix.toLin' (((HA.mat k σ J g)⁻¹ : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E))) (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])`. Establish `h0 : IsIsom P k J x.1.1 (φ.trans Ge)` using `fun y y' => by`. Express the relevant statement in the definitionally equal form `Formalism.UG.hform _ _ (Gm *ᵥ φ y') (Gm *ᵥ φ y) = _`. Rewrite using `[hform_mulVec_of_unitary _ _ _ (ha_unitary g)]`. Conclude with `h y y'`.

Use `⟨x, φ.trans Ge, h0, rfl, ?_⟩` and prove the remaining obligations. Use `ha_conj_of_intertwine g _ _ ?_` and prove the remaining obligations. Rewrite using `[ha_mat_gam, ha_mat_gam]`. Conclude with `mulMat_intertwine _ 1 (fun y => by rw [one_mul]; rfl) _`.
-/
theorem cls_conj_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k], ∀ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ) (x' : plusUnits P k) (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), ((QuotientGroup.mk x : Cls P k) = QuotientGroup.mk x' → ∃ g : HA k σ J, ∀ t, torEmb h' t = g * torEmb h t * g⁻¹) ∧ (IsConj (gam h) (gam h') → (QuotientGroup.mk x : Cls P k) = QuotientGroup.mk x') ∧ (∀ g : HA k σ J, gam h' = g * gam h * g⁻¹ → ∀ t, torEmb h' t = g * torEmb h t * g⁻¹) ∧ ∀ g : HA k σ J, HasCls P k J (g * gam h * g⁻¹) (QuotientGroup.mk x) := by
  intro F E _ _ _ _ _ σ _ r n P J _ k _ _ x φ h x' φ' h'
  refine ⟨fun heq => ?_, fun hcj => ?_, fun g hg t => ?_, fun g => ?_⟩
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at heq
    obtain ⟨c, hc⟩ := heq
    have hcU : c * Units.map (sigR k (star' P)).toMonoidHom c = (x.1)⁻¹ * x'.1 := hc
    have hxU : x'.1 = x.1 * (c * Units.map (sigR k (star' P)).toMonoidHom c) := by
      rw [hcU, mul_inv_cancel_left]
    have hxx : (x'.1 : (k ⊗[F] Fld P)ˣ).1 = x.1.1 * (c.1 * sigR k (star' P) c.1) := by
      rw [hxU]; rfl
    let mc : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (k ⊗[F] Fld P) :=
      LinearEquiv.ofLinear (LinearMap.mulLeft (k ⊗[F] E) ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P))
        (LinearMap.mulLeft (k ⊗[F] E) (c : k ⊗[F] Fld P))
        (LinearMap.ext fun y => by simp [← mul_assoc]) (LinearMap.ext fun y => by simp [← mul_assoc])
    let L := (φ.symm.trans mc).trans φ'
    let G : GL (Fin n) (k ⊗[F] E) :=
      ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap,
        matrix_ext_mulVec fun v => by
          rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
          exact L.apply_symm_apply v,
        matrix_ext_mulVec fun v => by
          rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
          exact L.symm_apply_apply v⟩
    have hGv : ∀ y, (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) *ᵥ φ y =
        φ' (((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) * y) := fun y => by
      change LinearMap.toMatrix' L.toLinearMap *ᵥ φ y = _
      rw [LinearMap.toMatrix'_mulVec]
      simp [L, mc]
    have hU : Formalism.UG.cT (sigR k σ) (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) * JR k J *
        (G : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = JR k J :=
      unitary_of_hform _ _ _ fun a b => by
        obtain ⟨y', rfl⟩ := φ.surjective a
        obtain ⟨y, rfl⟩ := φ.surjective b
        rw [hGv, hGv, h', h, hx, hx, hxx]
        congr 1
        have e1 : (c : k ⊗[F] Fld P) * ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) = 1 := c.mul_inv
        have e2 : sigR k (star' P) (c : k ⊗[F] Fld P) *
            sigR k (star' P) ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) = 1 := by
          rw [← map_mul, e1, map_one]
        rw [map_mul]
        linear_combination (x.1.1 * y * sigR k (star' P) y' * sigR k (star' P) (c : k ⊗[F] Fld P) *
          sigR k (star' P) ((c⁻¹ : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P)) * e1 + (x.1.1 * y * sigR k (star' P) y') * e2
    exact ⟨show HA k σ J from ⟨G, hU⟩, torEmb_conj h h' _ _ hGv⟩
  · obtain ⟨g, hg⟩ := isConj_iff.1 hcj
    have hG := intertwine_of_conj g _ _ hg
    rw [ha_mat_gam, ha_mat_gam] at hG
    obtain ⟨c, hc⟩ := exists_unit_of_comm _ hG
    have e := eq_of_unitary h h' _ (ha_unitary g) c hc
    have eU : x.1 = x'.1 * c * Units.map (sigR k (star' P)).toMonoidHom c := Units.ext e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨c⁻¹, ?_⟩
    change c⁻¹ * Units.map (sigR k (star' P)).toMonoidHom c⁻¹ = (x.1)⁻¹ * x'.1
    rw [eU, map_inv]
    group
    exact mul_comm _ _
  · have hG := intertwine_of_conj g _ _ hg.symm
    rw [ha_mat_gam, ha_mat_gam] at hG
    obtain ⟨c, hc⟩ := exists_unit_of_comm _ hG
    exact torEmb_conj h h' g c hc t
  · let Gm : Matrix (Fin n) (Fin n) (k ⊗[F] E) := (HA.mat k σ J g : GL (Fin n) (k ⊗[F] E))
    let Ge : (Fin n → k ⊗[F] E) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E) :=
      LinearEquiv.ofLinear (Matrix.toLin' Gm)
        (Matrix.toLin' (((HA.mat k σ J g)⁻¹ : GL (Fin n) (k ⊗[F] E)) : Matrix (Fin n) (Fin n) (k ⊗[F] E)))
        (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    have h0 : IsIsom P k J x.1.1 (φ.trans Ge) := fun y y' => by
      change Formalism.UG.hform _ _ (Gm *ᵥ φ y') (Gm *ᵥ φ y) = _
      rw [hform_mulVec_of_unitary _ _ _ (ha_unitary g)]
      exact h y y'
    refine ⟨x, φ.trans Ge, h0, rfl, ?_⟩
    refine ha_conj_of_intertwine g _ _ ?_
    rw [ha_mat_gam, ha_mat_gam]
    exact mulMat_intertwine _ 1 (fun y => by rw [one_mul]; rfl) _

end GlobalTheory.TrEll
