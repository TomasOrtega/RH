import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.QuadraticAlgebra.Basic

open NumberField QuadraticAlgebra

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem real_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ψ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (ψ x) = ψ x := by
  have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk ψ)))
  have := RingHom.congr_fun hr x
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  exact this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
private theorem sq_neg_one {z : ℂ} (h : z * z = -1) : starRingEnd ℂ z = -z := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
    Complex.one_im] at h1 h2
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Apply the first step, then apply the next step to every resulting obligation. Assume the hypotheses and unpack their components. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_CM_extension :
    UpperTheory.V.Af.BA.ExCM := by
  intro F _ _ _
  let ψ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  haveI hfact : Fact (∀ r : F, r ^ 2 ≠ -1 + 0 * r) := by
    refine ⟨fun r hr => ?_⟩
    have h2 : ψ r * ψ r = -1 := by
      rw [← map_mul, ← pow_two, hr]
      simp
    have h3 := real_val ψ r
    rw [sq_neg_one h2] at h3
    have h4 : ψ r = 0 := by
      have : (2 : ℂ) * ψ r = 0 := by linear_combination -h3
      simpa using this
    rw [h4] at h2
    norm_num at h2
  haveI hNF : NumberField (QuadraticAlgebra F (-1) 0) :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F (QuadraticAlgebra F (-1) 0) }
  have hωω : (ω : QuadraticAlgebra F (-1) 0) * ω = -1 := by
    rw [omega_mul_omega_eq_mk]
    ext <;> simp
  have hφω : ∀ φ : QuadraticAlgebra F (-1) 0 →+* ℂ, starRingEnd ℂ (φ ω) = - φ ω := by
    intro φ
    apply sq_neg_one
    rw [← map_mul, hωω, map_neg, map_one]
  have hTC : IsTotallyComplex (QuadraticAlgebra F (-1) 0) := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)
    have h1 := RingHom.congr_fun hr ω
    rw [ComplexEmbedding.conjugate_coe_eq, hφω] at h1
    have h0 : v.embedding ω = 0 := by
      have : (2 : ℂ) * v.embedding ω = 0 := by linear_combination -h1
      simpa using this
    have h5 : v.embedding ω * v.embedding ω = -1 := by
      rw [← map_mul, hωω, map_neg, map_one]
    rw [h0] at h5
    norm_num at h5
  refine ⟨QuadraticAlgebra F (-1) 0, inferInstance, hNF, hTC, algebraMap F (QuadraticAlgebra F (-1) 0),
    starRingEnd (QuadraticAlgebra F (-1) 0), ?_, ?_⟩
  · intro φ x
    have hx : x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re +
        algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω := by
      ext <;> simp
    have hsx : starRingEnd (QuadraticAlgebra F (-1) 0) x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re -
        algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω := by
      show star x = _
      ext <;> simp
    have hreal : ∀ y : F, starRingEnd ℂ (φ (algebraMap F (QuadraticAlgebra F (-1) 0) y)) =
        φ (algebraMap F (QuadraticAlgebra F (-1) 0) y) :=
      fun y => real_val (φ.comp (algebraMap F (QuadraticAlgebra F (-1) 0))) y
    rw [hsx]
    conv_rhs => rw [hx]
    simp only [map_add, map_sub, map_mul, hreal, hφω]
    ring
  · intro x
    rw [RingHom.mem_range]
    constructor
    · intro hx
      have him := congrArg QuadraticAlgebra.im hx
      change (star x).im = x.im at him
      rw [im_star] at him
      have h0 : x.im = 0 := by
        have : (2 : F) * x.im = 0 := by linear_combination -him
        simpa using this
      refine ⟨x.re, ?_⟩
      ext <;> simp [h0]
    · rintro ⟨y, rfl⟩
      show star (algebraMap F (QuadraticAlgebra F (-1) 0) y) = _
      ext <;> simp
