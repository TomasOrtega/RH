import Mathlib

noncomputable section

namespace PI.UnitaryGroupMassFormula.ProdUnitInert

/- English proof (translation)
Establish `h1` using `congrArg Complex.re hβ`. Establish `h2` using `congrArg Complex.im hβ`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2`. Establish `hre : β.re = 0`. Establish `hri : β.re * β.im = 0` using `by linarith`.

Break down `mul_eq_zero.mp hri with h | h` into its components or cases. Conclude with `h`. Rewrite `h1` using `[h]`. Establish `: (0 : ℝ) ≤ d` using `Nat.cast_nonneg d`. Use polynomial arithmetic with `[sq_nonneg β.re]`.

Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
-/
lemma conj_eq_neg_of_sq (d : ℕ) (β : ℂ) (hβ : β ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) β = -β := by
  have h1 := congrArg Complex.re hβ
  have h2 := congrArg Complex.im hβ
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hre : β.re = 0 := by
    have hri : β.re * β.im = 0 := by linarith
    rcases mul_eq_zero.mp hri with h | h
    · exact h
    · rw [h] at h1
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [sq_nonneg β.re]
  apply Complex.ext <;> simp [hre]

/- English proof (translation)
Rewrite `h` using `[map_add, map_mul, map_ratCast, map_ratCast, conj_eq_neg_of_sq d β hβ]`. Establish `hC : ((x ^ 2 + d * y ^ 2 : ℚ) : ℂ) = ((1 : ℚ) : ℂ)`. Use `push_cast`. Take the linear combination `h + (y : ℂ) ^ 2 * hβ`. Conclude with `hC` after adjusting the coercions.
-/
lemma conic_of_norm_one (d : ℕ) (β : ℂ) (hβ : β ^ 2 = -(d : ℂ)) (x y : ℚ)
    (h : ((x : ℂ) + y * β) * (starRingEnd ℂ) ((x : ℂ) + y * β) = 1) :
    x ^ 2 + d * y ^ 2 = 1 := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, conj_eq_neg_of_sq d β hβ] at h
  have hC : ((x ^ 2 + d * y ^ 2 : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by
    push_cast
    linear_combination h + (y : ℂ) ^ 2 * hβ
  exact_mod_cast hC

/- English proof (translation)
Set `v : Fin 2 → K` to `![1, b]`. Establish `hli : LinearIndependent ℚ v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def, mul_one] at hg`.

Establish `h1 : g 1 = 0`. Assume the negation of the conclusion as `h1`. Establish `hg1 : ((g 1 : ℚ) : K) ≠ 0` using `by exact_mod_cast h1`. Establish `hmul : ((g 1 : ℚ) : K) * b = -((g 0 : ℚ) : K)` using `by linear_combination hg`. Establish `hbq : b = ((-(g 0 / g 1) : ℚ) : K)`.

Rewrite using `[(eq_inv_mul_iff_mul_eq₀ hg1).mpr hmul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsq : (((-(g 0 / g 1)) ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K)`. Rewrite using `[Rat.cast_pow, ← hbq, hb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hq` using `Rat.cast_injective hsq`. Establish `hd' : (0 : ℚ) < d` using `by exact_mod_cast Nat.pos_of_ne_zero hd`. Use polynomial arithmetic with `[sq_nonneg (-(g 0 / g 1))]`.

Establish `h0 : g 0 = 0`. Rewrite `hg` using `[h1]`. Establish `: ((g 0 : ℚ) : K) = 0` using `by simpa using hg`. Conclude with `this` after adjusting the coercions. Introduce `i`.

Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank ℚ K` using `by simp [hK]`. Set `B` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`.

Establish `hB : ⇑B = v` using `coe_basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hsum` using `B.sum_repr w`. Rewrite `hsum` using `[hB, Fin.sum_univ_two]`. Use `⟨B.repr w 0, B.repr w 1, hsum.symm.trans ?_⟩` and prove the remaining obligations. Simplify using `[v, Rat.smul_def]`.
-/
lemma exists_rat_coords {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E)
    (hK : Module.finrank ℚ K = 2) (d : ℕ) (hd : d ≠ 0) (b : K)
    (hb : b ^ 2 = ((-(d : ℤ) : ℤ) : K)) (w : K) :
    ∃ x y : ℚ, w = (x : K) + (y : K) * b := by
  let v : Fin 2 → K := ![1, b]
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.smul_def, mul_one] at hg
    have h1 : g 1 = 0 := by
      by_contra h1
      have hg1 : ((g 1 : ℚ) : K) ≠ 0 := by exact_mod_cast h1
      have hmul : ((g 1 : ℚ) : K) * b = -((g 0 : ℚ) : K) := by linear_combination hg
      have hbq : b = ((-(g 0 / g 1) : ℚ) : K) := by
        rw [(eq_inv_mul_iff_mul_eq₀ hg1).mpr hmul]
        push_cast
        ring
      have hsq : (((-(g 0 / g 1)) ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K) := by
        rw [Rat.cast_pow, ← hbq, hb]
        push_cast
        ring
      have hq := Rat.cast_injective hsq
      have hd' : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      nlinarith [sq_nonneg (-(g 0 / g 1))]
    have h0 : g 0 = 0 := by
      rw [h1] at hg
      have : ((g 0 : ℚ) : K) = 0 := by simpa using hg
      exact_mod_cast this
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by simp [hK]
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum := B.sum_repr w
  rw [hB, Fin.sum_univ_two] at hsum
  refine ⟨B.repr w 0, B.repr w 1, hsum.symm.trans ?_⟩
  simp [v, Rat.smul_def]

/- English proof (translation)
Set `_ : Algebra K ℂ` to `(φ₀.comp (algebraMap K E)).toAlgebra`. Set `f : S → (E →ₐ[K] ℂ)` to `fun s => { toRingHom := emb s commutes' := fun a => by`. Simplify using `only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]`. Conclude with `hagree s a }`. Establish `hf : Function.Injective f`.

Introduce `s t hst`. Apply `hinj` to reduce the goal to its premises. Use extensionality with `e`. Conclude with `DFunLike.congr_fun hst e`. Establish `hbij : Function.Bijective f`.

Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨hf, by rw [AlgHom.card, hcard]⟩`. Establish `h1` using `Algebra.norm_eq_prod_embeddings (K := K) (E := ℂ) z`. Rewrite `h1` using `[RingHom.algebraMap_toAlgebra, RingHom.comp_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_emb_eq_norm {E : Type} [Field E] [NumberField E] (K : IntermediateField ℚ E)
    (φ₀ : E →+* ℂ) (S : Type) [Fintype S] (emb : S → E →+* ℂ) (hinj : Function.Injective emb)
    (hagree : ∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E))
    (hcard : Fintype.card S = Module.finrank K E) (z : E) :
    ∏ s, emb s z = φ₀ ((Algebra.norm K z : K) : E) := by
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  let f : S → (E →ₐ[K] ℂ) := fun s =>
    { toRingHom := emb s
      commutes' := fun a => by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        exact hagree s a }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext e
    exact DFunLike.congr_fun hst e
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, by rw [AlgHom.card, hcard]⟩
  have h1 := Algebra.norm_eq_prod_embeddings (K := K) (E := ℂ) z
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at h1
  calc ∏ s, emb s z = ∏ s, f s z := rfl
    _ = ∏ σ : E →ₐ[K] ℂ, σ z := Fintype.prod_bijective f hbij _ _ (fun _ => rfl)
    _ = _ := h1.symm

end PI.UnitaryGroupMassFormula.ProdUnitInert
