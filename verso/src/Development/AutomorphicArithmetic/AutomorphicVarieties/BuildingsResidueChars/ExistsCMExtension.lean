import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.QuadraticAlgebra.Basic

open NumberField QuadraticAlgebra

/- English proof (translation)
Establish `hr` using `ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk ψ)))`. Use `RingHom.congr_fun hr x` as an intermediate fact. Rewrite `this` using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `this`.
-/
private theorem real_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ψ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (ψ x) = ψ x := by
  have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk ψ)))
  have := RingHom.congr_fun hr x
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  exact this

/- English proof (translation)
Establish `h1` using `congrArg Complex.re h`. Establish `h2` using `congrArg Complex.im h`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im] at h1 h2`. Establish `hre : z.re = 0`. Break down `mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h3 | h3` into its components or cases.

Conclude with `h3`. Rewrite `h1` using `[h3]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
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
Introduce `F _ _ _`. Set `ψ : F →+* ℂ` to `(IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom`. Use `haveI hfact : Fact (∀ r : F, r ^ 2 ≠ -1 + 0 * r) := by`. Use `⟨fun r hr => ?_⟩` and prove the remaining obligations. Establish `h2 : ψ r * ψ r = -1`.

Rewrite using `[← map_mul, ← pow_two, hr]`. Simplify using the standard rewrite rules. Establish `h3` using `real_val ψ r`. Rewrite `h3` using `[sq_neg_one h2]`. Establish `h4 : ψ r = 0`.

Establish `: (2 : ℂ) * ψ r = 0` using `by linear_combination -h3`. Simplify using `using this`. Rewrite `h2` using `[h4]`. Evaluate the numerical expressions using `at h2`. Use `haveI hNF : NumberField (QuadraticAlgebra F (-1) 0) := { to_charZero := inferInstance to_finiteDimensional := Module.Finite.trans F (QuadraticAlgebra F (-1) 0) }`.

Establish `hωω : (ω : QuadraticAlgebra F (-1) 0) * ω = -1`. Rewrite using `[omega_mul_omega_eq_mk]`. Apply the tactic sequence `ext <;> simp`. Establish `hφω : ∀ φ : QuadraticAlgebra F (-1) 0 →+* ℂ, starRingEnd ℂ (φ ω) = - φ ω`. Introduce `φ`.

Apply `sq_neg_one` to reduce the goal to its premises. Rewrite using `[← map_mul, hωω, map_neg, map_one]`. Establish `hTC : IsTotallyComplex (QuadraticAlgebra F (-1) 0)`. Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex]`.

Introduce `hv`. Establish `hr` using `ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)`. Establish `h1` using `RingHom.congr_fun hr ω`. Rewrite `h1` using `[ComplexEmbedding.conjugate_coe_eq, hφω]`. Establish `h0 : v.embedding ω = 0`.

Establish `: (2 : ℂ) * v.embedding ω = 0` using `by linear_combination -h1`. Simplify using `using this`. Establish `h5 : v.embedding ω * v.embedding ω = -1`. Rewrite using `[← map_mul, hωω, map_neg, map_one]`. Rewrite `h5` using `[h0]`.

Evaluate the numerical expressions using `at h5`. Use `⟨QuadraticAlgebra F (-1) 0, inferInstance, hNF, hTC, algebraMap F (QuadraticAlgebra F (-1) 0), starRingEnd (QuadraticAlgebra F (-1) 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `φ x`. Establish `hx : x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re + algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω`. Apply the tactic sequence `ext <;> simp`.

Establish `hsx : starRingEnd (QuadraticAlgebra F (-1) 0) x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re - algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω` using `by show star x = _`. Apply the tactic sequence `ext <;> simp`. Establish `hreal : ∀ y : F, starRingEnd ℂ (φ (algebraMap F (QuadraticAlgebra F (-1) 0) y)) = φ (algebraMap F (QuadraticAlgebra F (-1) 0) y)` using `fun y => real_val (φ.comp (algebraMap F (QuadraticAlgebra F (-1) 0))) y`. Rewrite using `[hsx]`. Use `conv_rhs => rw [hx]`.

Simplify using `only [map_add, map_sub, map_mul, hreal, hφω]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`. Rewrite using `[RingHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `him` using `congrArg QuadraticAlgebra.im hx`. Express the relevant statement in the definitionally equal form `(star x).im = x.im at him`. Rewrite `him` using `[im_star]`. Establish `h0 : x.im = 0`.

Establish `: (2 : F) * x.im = 0` using `by linear_combination -him`. Simplify using `using this`. Use `⟨x.re, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [h0]`. Introduce and unpack `⟨y, rfl⟩ show star (algebraMap F (QuadraticAlgebra F (-1) 0) y) = _`.

Apply the tactic sequence `ext <;> simp`.
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
