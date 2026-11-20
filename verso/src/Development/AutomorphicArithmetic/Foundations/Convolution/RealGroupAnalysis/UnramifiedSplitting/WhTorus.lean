import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dL, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private lemma dL_mul {K : Type} [Field K] [NumberField K] {v : P K} (a d a' d' : (Kv v)ˣ) :
    dL a d * dL a' d' = dL (a * a') (d * d') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dL, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dL]`.
-/
private lemma dL_one {K : Type} [Field K] [NumberField K] {v : P K} : (dL (1 : (Kv v)ˣ) 1) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dL]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dL, nL, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private lemma dL_nL {K : Type} [Field K] [NumberField K] {v : P K} (a : (Kv v)ˣ) (b : Kv v) :
    dL a 1 * nL b = nL ((a : Kv v) * b) * dL a 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dL, nL, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Establish `hc' : c ∈ v.adicCompletionIntegers K` using `hc`. Establish `hn : -c ∈ v.adicCompletionIntegers K` using `neg_mem hc'`. Rewrite using `[GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]`. Establish `h1 : (1 : Kv v) ∈ Formalism.UG.Ov K v` using `one_mem _`. Establish `h0 : (0 : Kv v) ∈ Formalism.UG.Ov K v` using `zero_mem _`.

Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h1`. Conclude with `hc'`. Conclude with `h0`.

Conclude with `h1`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h1`. Conclude with `hn`. Conclude with `h0`.

Conclude with `h1`.
-/
private lemma nL_mem {K : Type} [Field K] [NumberField K] {v : P K} {c : Kv v} (hc : IsInt c) :
    nL c ∈ GlobalTheory.LFun.KGL v 2 := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : Kv v) ∈ Formalism.UG.Ov K v := one_mem _
  have h0 : (0 : Kv v) ∈ Formalism.UG.Ov K v := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

/- English proof (translation)
Introduce `h`. Establish `hu : Valued.v (ϖ : Kv v) < 1`. Establish `h' : Valued.v (ϖ : Kv v) = _` using `hϖ`. Rewrite using `[h']`. Conclude with `(by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1)` after adjusting the coercions.

Establish `hm : Valued.v (ϖ : Kv v) * Valued.v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hle : Valued.v (ϖ : Kv v) * Valued.v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) ≤ Valued.v (ϖ : Kv v) * 1` using `mul_le_mul_right h _`. Rewrite `hle` using `[hm, mul_one]`. Conclude with `absurd hu (not_lt.2 hle)`.
-/
private lemma not_int_inv {K : Type} [Field K] [NumberField K] {v : P K} {ϖ : (Kv v)ˣ} (hϖ : IsU ϖ) :
    ¬ IsInt ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) := by
  intro h
  have hu : Valued.v (ϖ : Kv v) < 1 := by
    have h' : Valued.v (ϖ : Kv v) = _ := hϖ
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1)
  have hm : Valued.v (ϖ : Kv v) * Valued.v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hle : Valued.v (ϖ : Kv v) * Valued.v ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) ≤ Valued.v (ϖ : Kv v) * 1 :=
    mul_le_mul_right h _
  rw [hm, mul_one] at hle
  exact absurd hu (not_lt.2 hle)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `not_int_inv hϖ (hχ.2.2 _ fun c hc => ?_)` and prove the remaining obligations. Establish `e1` using `hW.inv (dL ϖ⁻¹ 1) _ (nL_mem hc)`. Rewrite `e1` using `[dL_nL, hn]`. Establish `e2 : χ (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c) = 1` using `mul_right_cancel₀ h (by rw [e1, one_mul])`.

Rewrite `e2` using `[mul_comm]`. Then use the resulting hypothesis.
-/
private lemma W_zero {K : Type} [Field K] [NumberField K] {v : P K} {ϖ : (Kv v)ˣ} (hϖ : IsU ϖ)
    {χ : Kv v → ℂ} (hχ : Good χ) {B : Multiset ℂˣ} {W : GL (Fin 2) (Kv v) → ℂ} (hW : Eig v B W)
    (hn : ∀ b y, W (nL b * y) = χ b * W y) : W (dL ϖ⁻¹ 1) = 0 := by
  by_contra h
  refine not_int_inv hϖ (hχ.2.2 _ fun c hc => ?_)
  have e1 := hW.inv (dL ϖ⁻¹ 1) _ (nL_mem hc)
  rw [dL_nL, hn] at e1
  have e2 : χ (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c) = 1 := mul_right_cancel₀ h (by rw [e1, one_mul])
  rwa [mul_comm] at e2

/- English proof (translation)
Introduce `K _ _ v ϖ hϖ χ hχ α β W hW hn`. Take `⟨R, hcard, hRint, hR⟩` from `UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ`. Establish `hsum` using `fun g => (hR α β W hW g).1`. Establish `hcen` using `fun g => (hR α β W hW g).2`. Establish `hz` using `W_zero hϖ hχ hW hn`.

Establish `hint : ∀ c : Kv v, IsInt c → ∀ y, W (nL c * y) = W y` using `fun c hc y => by`. Rewrite using `[hn, hχ.2.1 c hc, one_mul]`. Establish `hϖint : IsInt (ϖ : Kv v)`. Establish `h' : Valued.v (ϖ : Kv v) = _` using `hϖ`. Use `show Valued.v (ϖ : Kv v) ≤ 1`.

Rewrite using `[h']`. Conclude with `(by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)` after adjusting the coercions. Establish `hq0 : q v ≠ 0`. Establish `: Ideal.absNorm v.asIdeal ≠ 0` using `fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `Nat.cast_ne_zero.2 this`.

Use `set s : ℂ := q v ^ (1 / 2 : ℂ) with hs`. Establish `hss : s * s = q v`. Rewrite using `[hs, ← Complex.cpow_add _ _ hq0]`. Evaluate the numerical expressions. Establish `hs0 : s ≠ 0` using `fun h => hq0 (by rw [← hss, h, zero_mul])`.

Establish `hconst : ∀ x : ℂ, ∑ _b ∈ R, x = q v * x` using `fun x => by`. Rewrite using `[Finset.sum_const, hcard, nsmul_eq_mul]`. Both sides reduce to the same expression. Establish `h1` using `hsum 1`. Establish `t1 : ∀ b ∈ R, W (1 * nL b * dL ϖ 1) = W (dL ϖ 1)` using `fun b hb => by`.

Rewrite using `[one_mul, hint b (hRint b hb)]`. Rewrite `h1` using `[Finset.sum_congr rfl t1, hconst, one_mul]`. Establish `t2 : W (dL 1 ϖ) = 0`. Use `hcen (dL ϖ⁻¹ 1)` as an intermediate fact. Rewrite `this` using `[dL_mul, inv_mul_cancel, one_mul, hz, mul_zero]`.

Conclude with `this`. Rewrite `h1` using `[t2, add_zero]`. Establish `h2` using `hsum (dL ϖ 1)`. Establish `t3 : ∀ b ∈ R, W (dL ϖ 1 * nL b * dL ϖ 1) = W (dL ϖ 1 * dL ϖ 1)` using `fun b hb => by`. Rewrite using `[dL_nL, mul_assoc, hint _ ?_]`.

Establish `hb' : (ϖ : Kv v) * b ∈ v.adicCompletionIntegers K` using `mul_mem (show (ϖ : Kv v) ∈ v.adicCompletionIntegers K from hϖint) (show b ∈ v.adicCompletionIntegers K from hRint b hb)`. Conclude with `hb'`. Rewrite `h2` using `[Finset.sum_congr rfl t3, hconst]`. Establish `t4 : W (dL ϖ 1 * dL 1 ϖ) = (α : ℂ) * β * W 1`. Use `hcen 1` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Rewrite using `[dL_mul, mul_one, one_mul]`. Conclude with `this`. Establish `t5 : W (dL ϖ 1 * dL ϖ 1) = (α : ℂ) * β * W (dL ϖ ϖ⁻¹)`. Use `hcen (dL ϖ ϖ⁻¹)` as an intermediate fact.

Rewrite `this` using `[dL_mul, inv_mul_cancel]`. Rewrite using `[dL_mul, mul_one]`. Conclude with `this`. Rewrite `h2` using `[t4, t5]`. Use `⟨h1.symm, ?_⟩` and prove the remaining obligations.

Establish `h3 : s * W (dL ϖ 1) = ((α : ℂ) + β) * W 1`. Use `mul_left_cancel₀ hs0 ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hss, ← mul_assoc]`. Conclude with `h1.symm`. Take the linear combination `(-1 : ℂ) * h2 + ((α : ℂ) + β) * h3`.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.whTorus :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (ϖ : (Kv v)ˣ), IsU ϖ → ∀ (χ : Kv v → ℂ), Good χ → ∀ (α β : ℂˣ) (W : GL (Fin 2) (Kv v) → ℂ), Eig v {α, β} W →
      (∀ b y, W (nL b * y) = χ b * W y) →
      q v * W (dL ϖ 1) = q v ^ (1 / 2 : ℂ) * ((α : ℂ) + β) * W 1 ∧
        (α : ℂ) * β * q v * W (dL ϖ ϖ⁻¹) = ((α : ℂ) ^ 2 + α * β + (β : ℂ) ^ 2) * W 1 := by
  intro K _ _ v ϖ hϖ χ hχ α β W hW hn
  obtain ⟨R, hcard, hRint, hR⟩ := UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ
  have hsum := fun g => (hR α β W hW g).1
  have hcen := fun g => (hR α β W hW g).2
  have hz := W_zero hϖ hχ hW hn
  have hint : ∀ c : Kv v, IsInt c → ∀ y, W (nL c * y) = W y := fun c hc y => by
    rw [hn, hχ.2.1 c hc, one_mul]
  have hϖint : IsInt (ϖ : Kv v) := by
    have h' : Valued.v (ϖ : Kv v) = _ := hϖ
    show Valued.v (ϖ : Kv v) ≤ 1
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  have hq0 : q v ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.cast_ne_zero.2 this
  set s : ℂ := q v ^ (1 / 2 : ℂ) with hs
  have hss : s * s = q v := by
    rw [hs, ← Complex.cpow_add _ _ hq0]
    norm_num
  have hs0 : s ≠ 0 := fun h => hq0 (by rw [← hss, h, zero_mul])
  have hconst : ∀ x : ℂ, ∑ _b ∈ R, x = q v * x := fun x => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rfl

  have h1 := hsum 1
  have t1 : ∀ b ∈ R, W (1 * nL b * dL ϖ 1) = W (dL ϖ 1) := fun b hb => by
    rw [one_mul, hint b (hRint b hb)]
  rw [Finset.sum_congr rfl t1, hconst, one_mul] at h1
  have t2 : W (dL 1 ϖ) = 0 := by
    have := hcen (dL ϖ⁻¹ 1)
    rw [dL_mul, inv_mul_cancel, one_mul, hz, mul_zero] at this
    exact this
  rw [t2, add_zero] at h1

  have h2 := hsum (dL ϖ 1)
  have t3 : ∀ b ∈ R, W (dL ϖ 1 * nL b * dL ϖ 1) = W (dL ϖ 1 * dL ϖ 1) := fun b hb => by
    rw [dL_nL, mul_assoc, hint _ ?_]
    have hb' : (ϖ : Kv v) * b ∈ v.adicCompletionIntegers K :=
      mul_mem (show (ϖ : Kv v) ∈ v.adicCompletionIntegers K from hϖint)
        (show b ∈ v.adicCompletionIntegers K from hRint b hb)
    exact hb'
  rw [Finset.sum_congr rfl t3, hconst] at h2
  have t4 : W (dL ϖ 1 * dL 1 ϖ) = (α : ℂ) * β * W 1 := by
    have := hcen 1
    rw [one_mul] at this
    rw [dL_mul, mul_one, one_mul]
    exact this
  have t5 : W (dL ϖ 1 * dL ϖ 1) = (α : ℂ) * β * W (dL ϖ ϖ⁻¹) := by
    have := hcen (dL ϖ ϖ⁻¹)
    rw [dL_mul, inv_mul_cancel] at this
    rw [dL_mul, mul_one]
    exact this
  rw [t4, t5] at h2
  refine ⟨h1.symm, ?_⟩
  have h3 : s * W (dL ϖ 1) = ((α : ℂ) + β) * W 1 := by
    refine mul_left_cancel₀ hs0 ?_
    rw [← mul_assoc, hss, ← mul_assoc]
    exact h1.symm
  linear_combination (-1 : ℂ) * h2 + ((α : ℂ) + β) * h3
