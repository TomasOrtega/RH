import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StTraceHermNondegenerate

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

omit [NumberField E] in

/- English proof (translation)
Apply `h.nonsingular.1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `LinearMap.ext hx`.
-/
theorem HermitianForm.eq_zero_of_toSesq_eq_zero (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

/- English proof (translation)
Establish `hT` using `(traceForm_nondegenerate ℚ E).1`. Prove the components needed by the constructor for the conclusion. Introduce `y hy`. Establish `key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0`. Introduce `w`.

Apply `hT` to reduce the goal to its premises. Introduce `a`. Use `hy (v.equivFun (a • w))` as an intermediate fact. Rewrite `this` using `[traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul]`. Rewrite using `[Algebra.traceForm_apply, mul_comm]`.

Conclude with `this`. Establish `h0` using `HermitianForm.eq_zero_of_toSesq_eq_zero h key`. Conclude with `(map_eq_zero_iff _ v.equivFun.symm.injective).1 h0`. Introduce `z hz`. Establish `key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0`.

Introduce `w`. Apply `hT` to reduce the goal to its premises. Introduce `a`. Use `hz (v.equivFun (conj F E a • w))` as an intermediate fact. Rewrite `this` using `[traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]`.

Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Simplify `this` using `[conj_conj]`. Establish `key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0`. Introduce `w`. Establish `e` using `(LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w`.

Rewrite `e` using `[key w]`. Conclude with `(map_eq_zero_iff _ (conjHom F E).injective).1 e`. Establish `h0` using `HermitianForm.eq_zero_of_toSesq_eq_zero h key'`. Conclude with `(map_eq_zero_iff _ v.equivFun.symm.injective).1 h0`.
-/
theorem TraceHermNondegenerate.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by
  have hT := (traceForm_nondegenerate ℚ E).1
  constructor
  · intro y hy
    have key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0 := by
      intro w
      apply hT
      intro a
      have := hy (v.equivFun (a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      exact this
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0
  · intro z hz
    have key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0 := by
      intro w
      apply hT
      intro a
      have := hz (v.equivFun (conj F E a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      simpa [conj_conj] using this
    have key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0 := by
      intro w
      have e := (LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w
      rw [key w] at e
      exact (map_eq_zero_iff _ (conjHom F E).injective).1 e
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key'
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
