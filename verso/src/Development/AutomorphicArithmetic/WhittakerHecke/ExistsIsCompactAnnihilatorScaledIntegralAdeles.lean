import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Rewrite using `[← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), Rat.numberField_discr]`. Both sides reduce to the same expression.
-/
private theorem diff_top : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), Rat.numberField_discr]
  rfl

/- English proof (translation)
Rewrite `hz` using `[GroundTheory.Global.mem_localInvDifferent_iff_valued, diff_top, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one, WithZero.exp_zero]`. Conclude with `hz`.
-/
private theorem int_of_inv (v : HeightOneSpectrum (𝓞 ℚ)) {z : v.adicCompletion ℚ}
    (hz : z ∈ GroundTheory.Global.localInvDifferent v) : z ∈ v.adicCompletionIntegers ℚ := by
  rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, diff_top, FractionalIdeal.coeIdeal_top,
    FractionalIdeal.count_one, WithZero.exp_zero] at hz
  exact hz

/- English proof (translation)
Introduce `N hN`. Establish `hNq : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `set c : FiniteAdeleRing (𝓞 ℚ) ℚ := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ with hc`. Establish `hcN : c * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1`. Establish `: (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)`.

Simplify using the standard rewrite rules. Rewrite using `[this, hc, ← map_mul, inv_mul_cancel₀ hNq, map_one]`. Use `⟨(fun z => c * z) '' (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), (GroundTheory.Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id), fun x hx => ?_⟩` and prove the remaining obligations. Use `⟨x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩` and prove the remaining obligations. Introduce `v`.

Use `int_of_inv v ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha => ?_)` and prove the remaining obligations. Establish `hb : ∀ u, GroundTheory.Global.finiteAdeleSingleAdd v a u ∈ u.adicCompletionIntegers ℚ`. Introduce `u`. Break down `eq_or_ne u v with rfl | hu` into its components or cases. Rewrite using `[GroundTheory.Global.finiteAdeleSingleAdd_apply_self]` and apply the resulting hypothesis.

Rewrite using `[GroundTheory.Global.finiteAdeleSingleAdd_apply_of_ne hu]`. Conclude with `zero_mem _`. Establish `h` using `hx _ hb`. Establish `e : x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * GroundTheory.Global.finiteAdeleSingleAdd v a) = GroundTheory.Global.finiteAdeleSingleAdd v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v)`. Rewrite using `[← GroundTheory.Global.finiteAdeleSingleAdd_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Establish `h' : ((GroundTheory.Global.localAdelicChar ℚ v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) : Circle) : ℂ) = 1` using `h`. Conclude with `Circle.ext (by simpa using h')`. Use `show c * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) = x`.

Rewrite using `[mul_comm x, ← mul_assoc, hcN, one_mul]`.
-/
theorem UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles :
    ∀ N : ℕ, 0 < N → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ x : FiniteAdeleRing (𝓞 ℚ) ℚ,
        (∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ, (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ψ (((0, x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ)) = 1) → x ∈ K := by
  intro N hN
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  set c : FiniteAdeleRing (𝓞 ℚ) ℚ := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ with hc
  have hcN : c * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
    have : (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ) := by
      simp
    rw [this, hc, ← map_mul, inv_mul_cancel₀ hNq, map_one]
  refine ⟨(fun z => c * z) '' (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id),
    fun x hx => ?_⟩
  refine ⟨x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  · intro v
    refine int_of_inv v ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha => ?_)
    have hb : ∀ u, GroundTheory.Global.finiteAdeleSingleAdd v a u ∈ u.adicCompletionIntegers ℚ := by
      intro u
      rcases eq_or_ne u v with rfl | hu
      · rwa [GroundTheory.Global.finiteAdeleSingleAdd_apply_self]
      · rw [GroundTheory.Global.finiteAdeleSingleAdd_apply_of_ne hu]
        exact zero_mem _
    have h := hx _ hb
    have e : x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * GroundTheory.Global.finiteAdeleSingleAdd v a) =
        GroundTheory.Global.finiteAdeleSingleAdd v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) := by
      rw [← GroundTheory.Global.finiteAdeleSingleAdd_mul]
      ring
    rw [e] at h
    have h' : ((GroundTheory.Global.localAdelicChar ℚ v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) : Circle) : ℂ) = 1 := h
    exact Circle.ext (by simpa using h')
  · show c * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) = x
    rw [mul_comm x, ← mul_assoc, hcN, one_mul]
