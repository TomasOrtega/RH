import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveElementFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PrimitiveLinearForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

namespace PrimitiveElementFibres

variable {n d : ℕ}

/- English proof (translation)
Simplify using `[projHom, pullback]`. Both sides reduce to the same expression.
-/
theorem algebraMap_C_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (a : ℂ) :
    projHom J A (C a) = Ideal.Quotient.mk J (C a) := by
  simp [projHom, pullback]
  rfl

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `(projHom J A).toRingHom.toAlgebra`. Rewrite using `[eq_top_iff]`. Introduce and unpack `b -`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Proceed by induction on `P using MvPolynomial.induction_on with`.

Consider the case `C a`. Establish `h : Ideal.Quotient.mk J (C a) = algebraMap (MvPolynomial (Fin d) ℂ) _ (C a)` using `(algebraMap_C_eq J A a).symm`. Rewrite using `[h]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add p q hp hq => rw [map_add]`.

Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp => rw [map_mul]`. Conclude with `mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)`.
-/
theorem adjoin_eq_top (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    Algebra.adjoin (MvPolynomial (Fin d) ℂ)
      (Set.range fun j : Fin n => Ideal.Quotient.mk J (X j)) = ⊤ := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro b -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk J (C a) = algebraMap (MvPolynomial (Fin d) ℂ) _ (C a) :=
      (algebraMap_C_eq J A a).symm
    rw [h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) (hx : x ∈ zeroSet J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
  Ideal.Quotient.lift J (eval x) (fun q hq => hx q hq)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `eval x (pullback A P) = _`. Rewrite using `[FibreBound.eval_pullback, hx.2]`.
-/
theorem evalAt_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {y : Fin d → ℂ} {x : Fin n → ℂ} (hx : x ∈ fibre J A y) (P : MvPolynomial (Fin d) ℂ) :
    evalAt J x hx.1 (projHom J A P) = eval y P := by
  change eval x (pullback A P) = _
  rw [FibreBound.eval_pullback, hx.2]

/- English proof (translation)
Introduce `n d J A hJ _ hA`. Use `hJ` as an intermediate fact. Set `_ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `(projHom J A).toRingHom.toAlgebra`. Set `_ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `Algebra.toModule`. Establish `: Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `hA.finite`.

Establish `hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J))` using `hA.injective`. Take `⟨c, m, D, Q, hmon, hdeg, hdiv, hD, ⟨a, b, hab⟩, hQ⟩` from `PrimitiveLinearForm.exists_primitive_data hinj (MvPolynomial.C : ℂ →+* (MvPolynomial (Fin d) ℂ)) (fun j : Fin n => Ideal.Quotient.mk J (X j)) (adjoin_eq_top J A)`. Use `set ℓ : (MvPolynomial (Fin n) ℂ ⧸ J) := ∑ j, algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C (c j)) * Ideal.Quotient.mk J (X j) with hℓ`. Establish `hℓmk : ℓ = Ideal.Quotient.mk J (∑ j, C (c j) * X j)`. Rewrite using `[hℓ, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `congr 1`. Conclude with `algebraMap_C_eq J A (c j)`. Establish `hev : ∀ y (x : Fin n → ℂ) (hx : x ∈ fibre J A y) (p : Polynomial (MvPolynomial (Fin d) ℂ)), evalAt J x hx.1 (Polynomial.aeval ℓ p) = (p.map (eval y)).eval (∑ j, c j * x j)`.

Introduce `y x hx p`. Establish `h1 : (evalAt J x hx.1).comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = eval y` using `RingHom.ext fun P => evalAt_projHom J A hx P`. Establish `h2 : evalAt J x hx.1 ℓ = ∑ j, c j * x j`. Rewrite using `[hℓmk]`. Express the relevant statement in the definitionally equal form `eval x (∑ j, C (c j) * X j) = _`.

Simplify using the standard rewrite rules. Rewrite using `[Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, Polynomial.eval_map]`. Use `⟨c, m, D, Q, hmon, hdeg, hD, fun y hy => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `congrArg (Polynomial.map (eval y)) hab`. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← Polynomial.derivative_map] at h`.

Establish `hu : Polynomial.C (eval y D)⁻¹ * Polynomial.C (eval y D) = (1 : Polynomial ℂ)`. Rewrite using `[← Polynomial.C_mul, inv_mul_cancel₀ hy, Polynomial.C_1]`. Conclude with `⟨Polynomial.C (eval y D)⁻¹ * a.map (eval y), Polynomial.C (eval y D)⁻¹ * b.map (eval y), by linear_combination Polynomial.C (eval y D)⁻¹ * h + hu⟩`. Introduce `x hx`. Use `⟨?_, fun j => ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg (evalAt J x hx.1) ((hdiv m).mpr dvd_rfl)`. Rewrite `h` using `[hev y x hx, map_zero]`. Conclude with `h`. Establish `h` using `congrArg (evalAt J x hx.1) (hQ j)`. Establish `h3 : evalAt J x hx.1 (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) D) = eval y D` using `evalAt_projHom J A hx D`.

Establish `h4 : evalAt J x hx.1 (Ideal.Quotient.mk J (X j)) = x j` using `by simp [evalAt]`. Rewrite `h` using `[hev y x hx, map_mul, h3, h4]`. Conclude with `h`. Introduce `τ hτ`. Set `_ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)` to `(Polynomial.aeval ℓ).toRingHom.toAlgebra`.

Establish `: IsScalarTower (MvPolynomial (Fin d) ℂ) (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)` using `IsScalarTower.of_algebraMap_eq fun r => (Polynomial.aeval_C ℓ r).symm`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `Algebra.IsIntegral.of_finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)`. Establish `: Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)` using `⟨fun s => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s).tower_top⟩`. Set `evτ : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ` to `(Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (eval y))`. Establish `hmax : (RingHom.ker evτ).IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨Polynomial.C (C z), by simp [evτ]⟩)`.

Establish `hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker evτ`. Introduce `p hp`. Take `⟨q, rfl⟩` from `(hdiv p).mp hp`. Rewrite using `[RingHom.mem_ker, map_mul]`. Establish `: evτ m = 0` using `hτ`.

Rewrite using `[this, zero_mul]`. Take `⟨P, hP, hPc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := (MvPolynomial (Fin n) ℂ ⧸ J)) _ hker`. Establish `hP' : (P.comap (Ideal.Quotient.mk J)).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨x, hx⟩` from `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP'`. Establish `hmem : ∀ q, Ideal.Quotient.mk J q ∈ P → eval x q = 0`.

Introduce `q hq`. Establish `hq' : q ∈ P.comap (Ideal.Quotient.mk J)` using `hq`. Rewrite `hq'` using `[hx]`. Conclude with `(MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'`. Establish `hover : ∀ p : Polynomial (MvPolynomial (Fin d) ℂ), evτ p = 0 → Polynomial.aeval ℓ p ∈ P`.

Introduce `p hp`. Establish `: p ∈ (RingHom.ker evτ)` using `hp`. Rewrite `this` using `[← hPc]`. Conclude with `this`. Establish `hxZ : x ∈ zeroSet J` using `fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact P.zero_mem)`.

Use `⟨x, ⟨hxZ, ?_⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1` using `hover (Polynomial.C (X i - C (y i))) (by simp [evτ])`. Rewrite `h1` using `[Polynomial.aeval_C]`. Establish `h2` using `hmem (pullback A (X i - C (y i))) h1`.

Rewrite `h2` using `[FibreBound.eval_pullback]`. Simplify `h2` using `[sub_eq_zero]`. Establish `h1` using `hover (Polynomial.X - Polynomial.C (C τ)) (by simp [evτ])`. Rewrite `h1` using `[map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hℓmk]`. Establish `h3 : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C τ) = Ideal.Quotient.mk J (C τ)` using `algebraMap_C_eq J A τ`.

Rewrite `h1` using `[h3, ← map_sub]`. Establish `h2` using `hmem _ h1`. Simplify `h2` using `[sub_eq_zero]`.
-/
theorem proof : PrimitiveElementFibres.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) := hA.injective
  obtain ⟨c, m, D, Q, hmon, hdeg, hdiv, hD, ⟨a, b, hab⟩, hQ⟩ :=
    PrimitiveLinearForm.exists_primitive_data hinj (MvPolynomial.C : ℂ →+* (MvPolynomial (Fin d) ℂ))
      (fun j : Fin n => Ideal.Quotient.mk J (X j)) (adjoin_eq_top J A)
  set ℓ : (MvPolynomial (Fin n) ℂ ⧸ J) := ∑ j, algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C (c j)) * Ideal.Quotient.mk J (X j) with hℓ
  have hℓmk : ℓ = Ideal.Quotient.mk J (∑ j, C (c j) * X j) := by
    rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact algebraMap_C_eq J A (c j)

  have hev : ∀ y (x : Fin n → ℂ) (hx : x ∈ fibre J A y) (p : Polynomial (MvPolynomial (Fin d) ℂ)),
      evalAt J x hx.1 (Polynomial.aeval ℓ p) = (p.map (eval y)).eval (∑ j, c j * x j) := by
    intro y x hx p
    have h1 : (evalAt J x hx.1).comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = eval y :=
      RingHom.ext fun P => evalAt_projHom J A hx P
    have h2 : evalAt J x hx.1 ℓ = ∑ j, c j * x j := by
      rw [hℓmk]
      change eval x (∑ j, C (c j) * X j) = _
      simp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, Polynomial.eval_map]
  refine ⟨c, m, D, Q, hmon, hdeg, hD, fun y hy => ⟨?_, ?_, ?_⟩⟩
  ·
    have h := congrArg (Polynomial.map (eval y)) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h
    have hu : Polynomial.C (eval y D)⁻¹ * Polynomial.C (eval y D) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hy, Polynomial.C_1]
    exact ⟨Polynomial.C (eval y D)⁻¹ * a.map (eval y), Polynomial.C (eval y D)⁻¹ * b.map (eval y),
      by linear_combination Polynomial.C (eval y D)⁻¹ * h + hu⟩
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · have h := congrArg (evalAt J x hx.1) ((hdiv m).mpr dvd_rfl)
      rw [hev y x hx, map_zero] at h
      exact h
    · have h := congrArg (evalAt J x hx.1) (hQ j)
      have h3 : evalAt J x hx.1 (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) D) =
          eval y D := evalAt_projHom J A hx D
      have h4 : evalAt J x hx.1 (Ideal.Quotient.mk J (X j)) = x j := by simp [evalAt]
      rw [hev y x hx, map_mul, h3, h4] at h
      exact h
  ·
    intro τ hτ
    let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := (Polynomial.aeval ℓ).toRingHom.toAlgebra
    have : IsScalarTower (MvPolynomial (Fin d) ℂ) (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      IsScalarTower.of_algebraMap_eq fun r => (Polynomial.aeval_C ℓ r).symm
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.IsIntegral.of_finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
    have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ⟨fun s => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s).tower_top⟩
    let evτ : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (eval y))
    have hmax : (RingHom.ker evτ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨Polynomial.C (C z), by simp [evτ]⟩)
    have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker evτ := by
      intro p hp
      obtain ⟨q, rfl⟩ := (hdiv p).mp hp
      rw [RingHom.mem_ker, map_mul]
      have : evτ m = 0 := hτ
      rw [this, zero_mul]
    obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := (MvPolynomial (Fin n) ℂ ⧸ J)) _ hker
    have hP' : (P.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ P → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ P.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    have hover : ∀ p : Polynomial (MvPolynomial (Fin d) ℂ), evτ p = 0 → Polynomial.aeval ℓ p ∈ P := by
      intro p hp
      have : p ∈ (RingHom.ker evτ) := hp
      rw [← hPc] at this
      exact this
    have hxZ : x ∈ zeroSet J :=
      fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact P.zero_mem)
    refine ⟨x, ⟨hxZ, ?_⟩, ?_⟩
    · funext i
      have h1 := hover (Polynomial.C (X i - C (y i))) (by simp [evτ])
      rw [Polynomial.aeval_C] at h1
      have h2 := hmem (pullback A (X i - C (y i))) h1
      rw [FibreBound.eval_pullback] at h2
      simpa [sub_eq_zero] using h2
    · have h1 := hover (Polynomial.X - Polynomial.C (C τ)) (by simp [evτ])
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hℓmk] at h1
      have h3 : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C τ) = Ideal.Quotient.mk J (C τ) := algebraMap_C_eq J A τ
      rw [h3, ← map_sub] at h1
      have h2 := hmem _ h1
      simpa [sub_eq_zero] using h2

end PrimitiveElementFibres

end

end GroundTheory.Heights₂.Heights.ComplexSets
