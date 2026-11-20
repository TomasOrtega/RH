import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Sd
open scoped Matrix

namespace UpperTheory.V.Af.Nf

variable {F : Type} [Field F] [NumberField F]

private def sInt (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletionIntegers F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, Subring.mem_iInf.2 fun v => by
    classical
    change Pi.single (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w (x : w.adicCompletion F) v ∈
      v.adicCompletionIntegers F
    by_cases hv : v = w
    · subst hv
      rw [Pi.single_eq_same]
      exact x.2
    · rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) _ _)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) _ _)

/- English proof (translation)
Proceed by induction on `c generalizing x with`. Consider the case `zero => exact x.2`. Consider the case `succ c ih`. Rewrite `hx` using `[pow_succ]`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) fun a b ha hb => ?_` and prove the remaining obligations.

Establish `h1 : Valued.v (b : w.adicCompletion F) < 1` using `(Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).1 hb`. Establish `h2 : Valued.v (b : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ)`. Generalize the expression as in `Valued.v (b : w.adicCompletion F) = t at h1`. Proceed by induction on `t using WithZero.expRecOn with`. Consider the case `zero => exact zero_le`.

Consider the case `exp n`. Rewrite `h1` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : WithZero.exp (-((c + 1 : ℕ) : ℤ)) = WithZero.exp (-(c : ℤ)) * WithZero.exp (-1 : ℤ)`.

Rewrite using `[← WithZero.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`.

Conclude with `(map_mul _ (a : w.adicCompletion F) b).le.trans (mul_le_mul' (ih a ha) h2)`. Conclude with `(Valuation.map_add_le _ ha hb)`.
-/
private theorem val_le (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) (x : w.adicCompletionIntegers F)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) :
    Valued.v (x : w.adicCompletion F) ≤ WithZero.exp (-(c : ℤ)) := by
  induction c generalizing x with
  | zero => exact x.2
  | succ c ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) fun a b ha hb => ?_
    · have h1 : Valued.v (b : w.adicCompletion F) < 1 :=
        (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).1 hb
      have h2 : Valued.v (b : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
        generalize Valued.v (b : w.adicCompletion F) = t at h1
        induction t using WithZero.expRecOn with
        | zero => exact zero_le
        | exp n =>
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
          rw [WithZero.exp_le_exp]
          omega
      have h3 : WithZero.exp (-((c + 1 : ℕ) : ℤ)) = WithZero.exp (-(c : ℤ)) * WithZero.exp (-1 : ℤ) := by
        rw [← WithZero.exp_add]
        congr 1
        push_cast
        ring
      rw [h3]
      exact (map_mul _ (a : w.adicCompletion F) b).le.trans (mul_le_mul' (ih a ha) h2)
    · exact (Valuation.map_add_le _ ha hb)

/- English proof (translation)
Establish `hM0 : (M : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h1 : Valued.v (M : w.adicCompletion F) = WithZero.exp (-(ordI w (Ideal.span {(M : 𝓞 F)}) : ℤ))`. Establish `: (M : w.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F M)` using `by simp`. Rewrite using `[this]`. Establish `h2` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (algebraMap (𝓞 F) F M)`.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hM0]`. Both sides reduce to the same expression. Establish `h0 : (M : w.adicCompletion F) ≠ 0` using `fun h => by`. Rewrite `h1` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero h1.symm`. Use `⟨⟨(M : w.adicCompletion F)⁻¹ * x, ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v ((M : w.adicCompletion F)⁻¹ * x) ≤ 1`. Rewrite using `[map_mul, map_inv₀, h1]`. Conclude with `(inv_mul_le_one₀ WithZero.exp_pos).2 (val_le w _ x hx)`.

Simplify using `[h0]`.
-/
private theorem nat_dvd (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : 1 ≤ M) (x : w.adicCompletionIntegers F)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ ordI w (Ideal.span {(M : 𝓞 F)})) :
    (M : w.adicCompletionIntegers F) ∣ x := by
  have hM0 : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : Valued.v (M : w.adicCompletion F) = WithZero.exp (-(ordI w (Ideal.span {(M : 𝓞 F)}) : ℤ)) := by
    have : (M : w.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F M) := by simp
    rw [this]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (algebraMap (𝓞 F) F M)
    refine h2.trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hM0]
    rfl
  have h0 : (M : w.adicCompletion F) ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  refine ⟨⟨(M : w.adicCompletion F)⁻¹ * x, ?_⟩, Subtype.ext ?_⟩
  · change Valued.v ((M : w.adicCompletion F)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, h1]
    exact (inv_mul_le_one₀ WithZero.exp_pos).2 (val_le w _ x hx)
  · simp [h0]

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
/- English proof (translation)
Introduce and unpack `M hM w _ ⟨k, hk, rfl⟩`. Use `⟨cornerGL 2 (sInt w) k, ?_, ?_⟩` and prove the remaining obligations. Use `funext fun j => ?_` and prove the remaining obligations. Establish `h0 : ![0, 1] ᵥ* (k.val.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w))) = ![0, 1]` using `hk`. Establish `h1` using `congrFun h0 j`.

Establish `h2 : k 1 j - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w`. Rewrite using `[← Ideal.Quotient.eq]`. Apply the tactic sequence `fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h1`. Take `⟨y, hy⟩` from `nat_dvd w hM _ h2`. Establish `h3 : (cornerGL 2 (sInt w) k) 1 j - (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j ∈ Ideal.span {(M : ↥(Ohat ℚ))}`.

Establish `h4 : (cornerGL 2 (sInt w) k) 1 j = (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j - sInt w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j) + sInt w (k 1 j)` using `rfl`. Rewrite using `[h4, sub_add_eq_add_sub, add_sub_assoc, add_sub_cancel_left, ← map_sub, hy, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`. Rewrite `h3` using `[← Ideal.Quotient.eq]`. Apply the tactic sequence `fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h3`.

Use extensionality with `i j : 2`. Express the relevant statement in the definitionally equal form `((1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) i j : Af ℚ) - sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) i j) + sLoc ℚ w _ = (1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j - sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) + sLoc ℚ w _`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `only [Matrix.one_apply_eq]`.

Both sides reduce to the same expression. Simplify using `only [Matrix.one_apply_ne h]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Af.Nf.kLocal :
    UpperTheory.V.Af.Nf.KLocal := by
  rintro M hM w _ ⟨k, hk, rfl⟩
  refine ⟨cornerGL 2 (sInt w) k, ?_, ?_⟩
  · refine funext fun j => ?_
    have h0 : ![0, 1] ᵥ* (k.val.map (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w))) = ![0, 1] := hk
    have h1 := congrFun h0 j
    have h2 : k 1 j - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j ∈
        IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w := by
      rw [← Ideal.Quotient.eq]
      fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h1
    obtain ⟨y, hy⟩ := nat_dvd w hM _ h2
    have h3 : (cornerGL 2 (sInt w) k) 1 j - (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j ∈ Ideal.span {(M : ↥(Ohat ℚ))} := by
      have h4 : (cornerGL 2 (sInt w) k) 1 j = (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j -
          sInt w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j) + sInt w (k 1 j) := rfl
      rw [h4, sub_add_eq_add_sub, add_sub_assoc, add_sub_cancel_left, ← map_sub, hy, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [← Ideal.Quotient.eq] at h3
    fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h3
  · ext i j : 2
    change ((1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) i j : Af ℚ) -
        sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) i j) + sLoc ℚ w _ =
      (1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j - sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) + sLoc ℚ w _
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.one_apply_ne h]
      rfl
