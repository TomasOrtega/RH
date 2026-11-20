import Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature
import Formalism.LocalToGlobal.ProjectiveLattices.SumEmbeddingsEq
import Formalism.LocalToGlobal.ProjectiveLattices.DatMat
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions ComplexConjugate Matrix Formalism.L2.Pj.DatLin
open scoped TensorProduct

local instance instStarDat (D : D7) : StarRing D.host.E := D.host.cmStar

attribute [local instance] Classical.propDecidable

/- English proof (translation)
The claim follows from `datInt_of Formalism.IndefR.Fin.factPrincipalDatum D j`.
-/
theorem datInt_holds (D : D7) (j : ℕ) : DatInt D j :=
  datInt_of Formalism.IndefR.Fin.factPrincipalDatum D j

/- English proof (translation)
The claim follows from `efW_unimod_of Formalism.IndefR.Fin.factPrincipalDatum D j hI`.
-/
theorem efW_unimod_holds (D : D7) (j : ℕ) (hI : DatInt D j) : Function.Bijective (efW D j hI) :=
  efW_unimod_of Formalism.IndefR.Fin.factPrincipalDatum D j hI

def cmTypeOfSqrt (D : D7) : Finset (D.host.E →+* ℂ) :=
  Finset.univ.filter (fun τ : D.host.E →+* ℂ => τ (rtE D : D.host.E) = D.host.φ₀ D.host.sqrtMinusD)

/- English proof (translation)
Simplify using `only [cmTypeOfSqrt, Finset.mem_filter, Finset.mem_univ, true_and]`. Both sides reduce to the same expression.
-/
theorem mem_cm_type_iff (D : D7) (τ : D.host.E →+* ℂ) :
    τ ∈ cmTypeOfSqrt D ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
  simp only [cmTypeOfSqrt, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/- English proof (translation)
The claim follows from `D.host.hyp.2.1.pos`.
-/
theorem d_pos (D : D7) : 0 < D.host.d := D.host.hyp.2.1.pos

/- English proof (translation)
Rewrite using `[← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast]`.
-/
theorem sq_emb (D : D7) (σ : D.host.E →+* ℂ) : (σ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
  rw [← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast]

/- English proof (translation)
Establish `h1` using `congrArg Complex.re h`. Establish `h2` using `congrArg Complex.im h`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2`. Establish `hd' : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `hre : z.re = 0`.

Assume the negation of the conclusion as `hne`. Establish `him : z.im = 0`. Establish `h3 : z.re * (2 * z.im) = 0` using `by linarith`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Conclude with `absurd h hne`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h1` using `[him]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Use `⟨Complex.ext (by simp [hre]) (by simp), hre, ?_⟩` and prove the remaining obligations. Introduce `him`.

Rewrite `h1` using `[hre, him]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem conj_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    conj z = -z ∧ z.re = 0 ∧ z.im ≠ 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : z.re = 0 := by
    by_contra hne
    have him : z.im = 0 := by
      have h3 : z.re * (2 * z.im) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hne
      · linarith
    rw [him] at h1
    nlinarith [mul_self_nonneg z.re]
  refine ⟨Complex.ext (by simp [hre]) (by simp), hre, ?_⟩
  intro him
  rw [hre, him] at h1
  linarith

/- English proof (translation)
Establish `h0` using `conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)`. Simplify using `only [mem_cm_type_iff, ComplexEmbedding.conjugate_coe_eq]`. Use `set s0 := D.host.φ₀ D.host.sqrtMinusD`. Establish `hs0 : s0 ≠ 0` using `fun h => h0.2.2 (by rw [h, Complex.zero_im])`. Establish `hroot : σ D.host.sqrtMinusD = s0 ∨ σ D.host.sqrtMinusD = -s0`.

Establish `h : (σ D.host.sqrtMinusD - s0) * (σ D.host.sqrtMinusD + s0) = 0`. Establish `e1` using `sq_emb D σ`. Establish `e2` using `sq_emb D D.host.φ₀`. Take the linear combination `e1 - e2`. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Use `left`. Take the linear combination `h`. Use `right`. Take the linear combination `h`. Prove the components needed by the constructor for the conclusion.

Introduce `h hc`. Rewrite `hc` using `[h, h0.1]`. Conclude with `hs0 (by linear_combination -hc / 2)`. Introduce `hc`. Break down `hroot with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (by rw [h, map_neg, h0.1, neg_neg]) hc`.
-/
theorem cm_type_mem_iff_conj_not_mem (D : D7) (σ : D.host.E →+* ℂ) :
    σ ∈ cmTypeOfSqrt D ↔ ComplexEmbedding.conjugate σ ∉ cmTypeOfSqrt D := by
  have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
  simp only [mem_cm_type_iff, ComplexEmbedding.conjugate_coe_eq]
  set s0 := D.host.φ₀ D.host.sqrtMinusD
  have hs0 : s0 ≠ 0 := fun h => h0.2.2 (by rw [h, Complex.zero_im])
  have hroot : σ D.host.sqrtMinusD = s0 ∨ σ D.host.sqrtMinusD = -s0 := by
    have h : (σ D.host.sqrtMinusD - s0) * (σ D.host.sqrtMinusD + s0) = 0 := by
      have e1 := sq_emb D σ
      have e2 := sq_emb D D.host.φ₀
      linear_combination e1 - e2
    rcases mul_eq_zero.1 h with h | h
    · left; linear_combination h
    · right; linear_combination h
  constructor
  · intro h hc
    rw [h, h0.1] at hc
    exact hs0 (by linear_combination -hc / 2)
  · intro hc
    rcases hroot with h | h
    · exact h
    · exact absurd (by rw [h, map_neg, h0.1, neg_neg]) hc

section Coord

variable (D : D7) (j : ℕ)

def thW : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] (cmTypeOfSqrt D → Fin (D.sp.W j).rank → ℂ) :=
  theta (D.sp.W j).frame (cmTypeOfSqrt D) (latW D j)

/- English proof (translation)
The claim follows from `theta_tmul _ _ _ x v`.
-/
theorem thW_tmul (x : ℝ) (v : latW D j) :
    thW D j (x ⊗ₜ v) = fun (τ : cmTypeOfSqrt D) i => (x : ℂ) * (τ : D.host.E →+* ℂ) ((D.sp.W j).frame.repr v i) :=
  theta_tmul _ _ _ x v

/- English proof (translation)
The claim follows from `theta_bijective _ _ (cm_type_mem_iff_conj_not_mem D) (latW_fin D j) (exists_smul_mem_latW D j)`.
-/
theorem thW_bijective : Function.Bijective (thW D j) :=
  theta_bijective _ _ (cm_type_mem_iff_conj_not_mem D) (latW_fin D j) (exists_smul_mem_latW D j)

attribute [irreducible] thW

def GW (τ : D.host.E →+* ℂ) : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ :=
  (D.sp.W j).gram.map τ

/- English proof (translation)
The claim follows from `NumberField.IsCMField.complexEmbedding_complexConj D.host.E τ z`.
-/
theorem emb_star (τ : D.host.E →+* ℂ) (z : D.host.E) : τ (star z) = conj (τ z) :=
  NumberField.IsCMField.complexEmbedding_complexConj D.host.E τ z

/- English proof (translation)
Rewrite using `[sesq_repr (D.sp.W j).hT (D.sp.W j).frame v w]`. Simplify using `only [map_sum, map_mul, emb_star, dotProduct, mulVec, GW, HSpace.gram, Matrix.map_apply, Pi.star_apply, Complex.star_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))` and prove the remaining obligations.
-/
theorem hT_emb (τ : D.host.E →+* ℂ) (v w : (D.sp.W j).V) :
    τ ((D.sp.W j).hT v w) = star (fun i => τ ((D.sp.W j).frame.repr v i)) ⬝ᵥ
      (GW D j τ *ᵥ fun i => τ ((D.sp.W j).frame.repr w i)) := by
  rw [sesq_repr (D.sp.W j).hT (D.sp.W j).frame v w]
  simp only [map_sum, map_mul, emb_star, dotProduct, mulVec, GW, HSpace.gram, Matrix.map_apply,
    Pi.star_apply, Complex.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Finset.mul_sum, Complex.ofReal_mul]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))` and prove the remaining obligations.
-/
theorem dot_smul_real {n : Type} [Fintype n] (G : Matrix n n ℂ) (a a' : ℝ) (u w : n → ℂ) :
    star (fun i => (a : ℂ) * u i) ⬝ᵥ (G *ᵥ fun i => (a' : ℂ) * w i) =
      ((a * a' : ℝ) : ℂ) * (star u ⬝ᵥ (G *ᵥ w)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal,
    Finset.mul_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x1 x2 h1 h2`. Rewrite using `[map_add, LinearMap.add_apply, h1, h2, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations.

Simplify using `only [map_add, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re]`. Apply the tactic sequence `try ring`. Consider the case `tmul a v`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add y1 y2 h1 h2`. Rewrite using `[map_add, h1, h2, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Simplify using `only [map_add, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re]`. Apply the tactic sequence `try ring`.

Consider the case `tmul a' w`. Rewrite using `[LinearMap.BilinForm.baseChange_tmul, thW_tmul, thW_tmul]`. Simplify using `only [dot_smul_real, ← hT_emb]`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul]`. Establish `hq : ((intForm (efQ D j) hI v w : ℤ) : ℝ) = ∑ τ ∈ cmTypeOfSqrt D, 2 * (τ (D.host.xi0 * (D.sp.W j).hT (v : (D.sp.W j).V) w)).re`.

Rewrite using `[← trace_eq_sum_psi (cmTypeOfSqrt D) (cm_type_mem_iff_conj_not_mem D)]`. Establish `h` using `congrArg (fun q : ℚ => (q : ℝ)) (intForm_cast (efQ D j) hI v w)`. Simplify using `only [Rat.cast_intCast] at h`. Conclude with `h`. Use `push_cast`.

Rewrite using `[hq, ← Finset.sum_coe_sort (cmTypeOfSqrt D), Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Establish `e : (ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0 * ((a : ℂ) * (a' : ℂ) * (τ : D.host.E →+* ℂ) ((D.sp.W j).hT (v : (D.sp.W j).V) w)) = (((ε : ℝ) * (a * a') : ℝ) : ℂ) * ((τ : D.host.E →+* ℂ) D.host.xi0 * (τ : D.host.E →+* ℂ) ((D.sp.W j).hT (v : (D.sp.W j).V) w))` using `by push_cast; ring`. Rewrite using `[e, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem efR_formula (ε : ℤ) (hI : DatInt D j) (x y : ℝ ⊗[ℤ] latW D j) :
    (ε • intForm (efQ D j) hI).baseChange ℝ x y =
      ∑ τ : cmTypeOfSqrt D, 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
        (star (thW D j x τ) ⬝ᵥ (GW D j τ *ᵥ thW D j y τ))).re := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x1 x2 h1 h2 =>
    rw [map_add, LinearMap.add_apply, h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    simp only [map_add, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re]
    try ring
  | tmul a v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y1 y2 h1 h2 =>
      rw [map_add, h1, h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      simp only [map_add, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re]
      try ring
    | tmul a' w =>
      rw [LinearMap.BilinForm.baseChange_tmul, thW_tmul, thW_tmul]
      simp only [dot_smul_real, ← hT_emb]
      rw [LinearMap.smul_apply, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
      have hq : ((intForm (efQ D j) hI v w : ℤ) : ℝ) =
          ∑ τ ∈ cmTypeOfSqrt D, 2 * (τ (D.host.xi0 * (D.sp.W j).hT (v : (D.sp.W j).V) w)).re := by
        rw [← trace_eq_sum_psi (cmTypeOfSqrt D) (cm_type_mem_iff_conj_not_mem D)]
        have h := congrArg (fun q : ℚ => (q : ℝ)) (intForm_cast (efQ D j) hI v w)
        simp only [Rat.cast_intCast] at h
        exact h
      push_cast
      rw [hq, ← Finset.sum_coe_sort (cmTypeOfSqrt D), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [map_mul]
      have e : (ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0 * ((a : ℂ) * (a' : ℂ) *
          (τ : D.host.E →+* ℂ) ((D.sp.W j).hT (v : (D.sp.W j).V) w)) =
          (((ε : ℝ) * (a * a') : ℝ) : ℂ) * ((τ : D.host.E →+* ℂ) D.host.xi0 *
          (τ : D.host.E →+* ℂ) ((D.sp.W j).hT (v : (D.sp.W j).V) w)) := by
        push_cast; ring
      rw [e, Complex.re_ofReal_mul]
      ring

end Coord

/- English proof (translation)
Simplify using `only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_mul_negI (c : ℂ) (ρ : ℝ) : (c * -(Complex.I * ρ)).re = ρ * c.im := by
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/- English proof (translation)
Establish `hs : s = (s.im : ℂ) * Complex.I` using `Complex.ext (by simp [hre]) (by simp)`. Generalize the expression as in `s.im = b at hs hb ⊢`. Substitute `hs` using the available equality. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hN0 : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`.

Establish `hb0 : (b : ℂ) ≠ 0` using `by exact_mod_cast hb`. Rewrite using `[div_eq_iff (mul_ne_zero hN0 (mul_ne_zero hb0 Complex.I_ne_zero))]`. Establish `e1 : ((((1 : ℝ) / ((n : ℝ) * b)) : ℝ) : ℂ) * ((n : ℂ) * (b : ℂ)) = 1`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (mul_ne_zero hnR.ne' hb), Complex.ofReal_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e1, Complex.I_mul_I, mul_one]`. Use `_ = _ := by ring`.
-/
theorem mass_ratio_recursive_bound (n : ℕ) (hn : 0 < n) (s : ℂ) (hre : s.re = 0) (hb : s.im ≠ 0) :
    -1 / ((n : ℂ) * s) = Complex.I * (((1 : ℝ) / ((n : ℝ) * s.im) : ℝ) : ℂ) := by
  have hs : s = (s.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
  generalize s.im = b at hs hb ⊢
  subst hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  rw [div_eq_iff (mul_ne_zero hN0 (mul_ne_zero hb0 Complex.I_ne_zero))]
  have e1 : ((((1 : ℝ) / ((n : ℝ) * b)) : ℝ) : ℂ) * ((n : ℂ) * (b : ℂ)) = 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, one_div,
      inv_mul_cancel₀ (mul_ne_zero hnR.ne' hb), Complex.ofReal_one]
  calc (-1 : ℂ) = (Complex.I * Complex.I) * (((((1 : ℝ) / ((n : ℝ) * b)) : ℝ) : ℂ) * ((n : ℂ) * (b : ℂ))) := by
        rw [e1, Complex.I_mul_I, mul_one]
    _ = _ := by ring

/- English proof (translation)
Establish `h0` using `conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)`. Establish `hτs : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD` using `(mem_cm_type_iff D τ).1 hτ`. Establish `hb : (D.host.φ₀ D.host.sqrtMinusD).im ≠ 0` using `h0.2.2`. Establish `hn : 0 < Ideal.absNorm D.host.ccK`. Use `normK_ne_zero D` as an intermediate fact.

Conclude with `Nat.pos_of_ne_zero (fun h => this (by rw [h, Nat.cast_zero]))`. Establish `hnR : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ)` using `by exact_mod_cast hn`. Establish `hxi : τ D.host.xi0 = Complex.I * (((1 : ℝ) / ((Ideal.absNorm D.host.ccK : ℝ) * (D.host.φ₀ D.host.sqrtMinusD).im) : ℝ) : ℂ)`. Simplify using `only [Host.xi0, map_div₀, map_neg, map_one, map_mul, map_natCast, hτs]`. Conclude with `mass_ratio_recursive_bound _ hn _ h0.2.1 hb`.

Rewrite using `[hxi]`. Establish `hI' : ∀ r : ℝ, (Complex.I * (r : ℂ)).im = r` using `fun r => by simp`. Distinguish the cases in `hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im`. Rewrite using `[if_pos hpos, Int.cast_one, one_mul, hI']`. Check the signs of the components of the expression.

Establish `hneg : (D.host.φ₀ D.host.sqrtMinusD).im < 0` using `lt_of_le_of_ne (not_lt.1 hpos) hb`. Rewrite using `[if_neg hpos, Int.cast_neg, Int.cast_one, neg_one_mul, Complex.neg_im, hI']`. Establish `: (1 : ℝ) / ((Ideal.absNorm D.host.ccK : ℝ) * (D.host.φ₀ D.host.sqrtMinusD).im) < 0` using `div_neg_of_pos_of_neg one_pos (mul_neg_of_pos_of_neg hnR hneg)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem xi0_embedding_im_pos (D : D7) (τ : D.host.E →+* ℂ) (hτ : τ ∈ cmTypeOfSqrt D) :
    0 < (((if 0 < (D.host.φ₀ D.host.sqrtMinusD).im then 1 else -1 : ℤ) : ℂ) * τ D.host.xi0).im := by
  have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
  have hτs : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := (mem_cm_type_iff D τ).1 hτ
  have hb : (D.host.φ₀ D.host.sqrtMinusD).im ≠ 0 := h0.2.2
  have hn : 0 < Ideal.absNorm D.host.ccK := by
    have := normK_ne_zero D
    exact Nat.pos_of_ne_zero (fun h => this (by rw [h, Nat.cast_zero]))
  have hnR : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by exact_mod_cast hn
  have hxi : τ D.host.xi0 = Complex.I * (((1 : ℝ) / ((Ideal.absNorm D.host.ccK : ℝ) *
      (D.host.φ₀ D.host.sqrtMinusD).im) : ℝ) : ℂ) := by
    simp only [Host.xi0, map_div₀, map_neg, map_one, map_mul, map_natCast, hτs]
    exact mass_ratio_recursive_bound _ hn _ h0.2.1 hb
  rw [hxi]
  have hI' : ∀ r : ℝ, (Complex.I * (r : ℂ)).im = r := fun r => by simp
  by_cases hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im
  · rw [if_pos hpos, Int.cast_one, one_mul, hI']
    positivity
  · have hneg : (D.host.φ₀ D.host.sqrtMinusD).im < 0 := lt_of_le_of_ne (not_lt.1 hpos) hb
    rw [if_neg hpos, Int.cast_neg, Int.cast_one, neg_one_mul, Complex.neg_im, hI']
    have : (1 : ℝ) / ((Ideal.absNorm D.host.ccK : ℝ) * (D.host.φ₀ D.host.sqrtMinusD).im) < 0 :=
      div_neg_of_pos_of_neg one_pos (mul_neg_of_pos_of_neg hnR hneg)
    linarith

def AW (D : D7) (j : ℕ) (a : 𝓞 D.host.E) :
    (cmTypeOfSqrt D → Fin (D.sp.W j).rank → ℂ) →ₗ[ℝ] (cmTypeOfSqrt D → Fin (D.sp.W j).rank → ℂ) :=
  blk (fun τ : cmTypeOfSqrt D => ((τ : D.host.E →+* ℂ) (a : D.host.E)) •
    (1 : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ))

/- English proof (translation)
Establish `h1 : ∀ m : latW D j, thW D j ((1 : ℝ) ⊗ₜ (a • m)) = AW D j a (thW D j ((1 : ℝ) ⊗ₜ m))`. Introduce `m`. Use function extensionality and compare the values at `τ i`. Rewrite using `[AW, blk_apply, thW_tmul, thW_tmul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul, Submodule.coe_smul]`.

Rewrite using `[← algebraMap_smul D.host.E a (m : (D.sp.W j).V), LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]`. Apply the tactic sequence `try rfl`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add z1 z2 h1' h2' => rw [map_add, map_add, h1', h2', map_add (thW D j), map_add (AW D j a)]`.

Consider the case `tmul x m`. Establish `e : x ⊗ₜ[ℤ] m = x • ((1 : ℝ) ⊗ₜ[ℤ] m)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e, LinearMap.map_smul, hA, LinearMap.map_smul, h1, LinearMap.map_smul, LinearMap.map_smul]`.
-/
theorem thW_AW (D : D7) (j : ℕ) (a : 𝓞 D.host.E) (A : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] ℝ ⊗[ℤ] latW D j)
    (hA : ∀ x : latW D j, A ((1 : ℝ) ⊗ₜ x) = (1 : ℝ) ⊗ₜ (a • x)) (z : ℝ ⊗[ℤ] latW D j) :
    thW D j (A z) = AW D j a (thW D j z) := by
  have h1 : ∀ m : latW D j, thW D j ((1 : ℝ) ⊗ₜ (a • m)) = AW D j a (thW D j ((1 : ℝ) ⊗ₜ m)) := by
    intro m
    funext τ i
    rw [AW, blk_apply, thW_tmul, thW_tmul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul, Submodule.coe_smul]
    rw [← algebraMap_smul D.host.E a (m : (D.sp.W j).V), LinearEquiv.map_smul, Finsupp.smul_apply,
      smul_eq_mul, map_mul]
    try rfl
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z1 z2 h1' h2' => rw [map_add, map_add, h1', h2', map_add (thW D j), map_add (AW D j a)]
  | tmul x m =>
    have e : x ⊗ₜ[ℤ] m = x • ((1 : ℝ) ⊗ₜ[ℤ] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul, hA, LinearMap.map_smul, h1, LinearMap.map_smul, LinearMap.map_smul]

/- English proof (translation)
Rewrite using `[AW, blk_comp, blk_comp]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem AW_comm (D : D7) (j : ℕ) (a : 𝓞 D.host.E)
    (K : cmTypeOfSqrt D → Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ) :
    blk K ∘ₗ AW D j a = AW D j a ∘ₗ blk K := by
  rw [AW, blk_comp, blk_comp]
  congr 1
  funext τ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[AW, trace_blk]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]`.
-/
theorem trace_AW (D : D7) (j : ℕ) (a : 𝓞 D.host.E) :
    LinearMap.trace ℝ _ (AW D j a) =
      ∑ τ : cmTypeOfSqrt D, 2 * (((τ : D.host.E →+* ℂ) (a : D.host.E)) * ((D.sp.W j).rank : ℂ)).re := by
  rw [AW, trace_blk]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]

/- English proof (translation)
Rewrite using `[AW, blk_comp, trace_blk]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]`.
-/
theorem trace_K_AW (D : D7) (j : ℕ) (a : 𝓞 D.host.E)
    (K : cmTypeOfSqrt D → Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ) :
    LinearMap.trace ℝ _ (blk K ∘ₗ AW D j a) =
      ∑ τ : cmTypeOfSqrt D, 2 * (((τ : D.host.E →+* ℂ) (a : D.host.E)) * (K τ).trace).re := by
  rw [AW, blk_comp, trace_blk]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[Finset.sum_coe_sort (cmTypeOfSqrt D) g]`. Both sides reduce to the same expression.
-/
theorem sum_filter_eq_sum_cm_type (D : D7) (g : (D.host.E →+* ℂ) → ℂ) :
    ∑ τ ∈ Finset.univ.filter (fun τ : D.host.E →+* ℂ => τ (rtE D : D.host.E) = D.host.φ₀ D.host.sqrtMinusD), g τ =
      ∑ τ : cmTypeOfSqrt D, g τ := by
  rw [Finset.sum_coe_sort (cmTypeOfSqrt D) g]
  rfl

/- English proof (translation)
Distinguish the cases in `h0 : u = 0`. Substitute `h0` using the available equality. Rewrite using `[Matrix.mulVec_zero, star_zero, zero_dotProduct, mul_zero, Complex.zero_re, mul_zero]`. Conclude with `⟨le_refl 0, fun h => absurd rfl h⟩`. Take `⟨ρ, hρ, hρe⟩` from `hK u h0`.

Rewrite using `[hρe, re_mul_negI]`. Establish `: 0 < 2 * (ρ * c.im)` using `by positivity`. Conclude with `⟨this.le, fun _ => this⟩`.
-/
theorem term_pos {n : Type} [Fintype n] (c : ℂ) (hc : 0 < c.im) (K G : Matrix n n ℂ)
    (hK : ∀ u : n → ℂ, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (G *ᵥ u) = -(Complex.I * ρ))
    (u : n → ℂ) :
    0 ≤ 2 * (c * (star (K *ᵥ u) ⬝ᵥ (G *ᵥ u))).re ∧ (u ≠ 0 → 0 < 2 * (c * (star (K *ᵥ u) ⬝ᵥ (G *ᵥ u))).re) := by
  by_cases h0 : u = 0
  · subst h0
    rw [Matrix.mulVec_zero, star_zero, zero_dotProduct, mul_zero, Complex.zero_re, mul_zero]
    exact ⟨le_refl 0, fun h => absurd rfl h⟩
  · obtain ⟨ρ, hρ, hρe⟩ := hK u h0
    rw [hρe, re_mul_negI]
    have : 0 < 2 * (ρ * c.im) := by positivity
    exact ⟨this.le, fun _ => this⟩

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Use `set ε : ℤ := if 0 < (D.host.φ₀ D.host.sqrtMinusD).im then 1 else -1 with hεdef`. Apply the tactic sequence `refine ⟨ε, by by_cases h : 0 < (D.host.φ₀ D.host.sqrtMinusD).im <;> simp [ε, h], ?_⟩`. Establish `hc : ∀ τ : cmTypeOfSqrt D, 0 < ((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0).im` using `fun τ => xi0_embedding_im_pos D τ τ.2`. Take `⟨θ, hθ⟩ : ∃ θ : (ℝ ⊗[ℤ] latW D j) ≃ₗ[ℝ] (cmTypeOfSqrt D → Fin (D.sp.W j).rank → ℂ), ∀ x, θ x = thW D j x` from `⟨LinearEquiv.ofBijective _ (thW_bijective D j), fun _ => rfl⟩`. Establish `hsig : ∀ τ : cmTypeOfSqrt D, ∃ K : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ, (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧ (∀ u w, star (K *ᵥ u) ⬝ᵥ (GW D j τ *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (GW D j τ *ᵥ w)) ∧ (∀ u, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (GW D j τ *ᵥ u) = -(Complex.I * ρ)) …`.

Introduce `τ`. Establish `h1` using `D.sp.W_sig j (τ : D.host.E →+* ℂ)`. Rewrite `h1` using `[D.sp.W_sigval j hj.1 hj.2]`. Take `⟨e, P, hP⟩` from `h1`. Conclude with `exists_cplx_str _ _ _ e P hP`.

Use `choose K hK1 hK2 hK3 hK4 using hsig`. Establish `hr : (D.sp.W j).rank = (D.R.sigW j).1 + (D.R.sigW j).2`. Rewrite using `[D.sp.W_rank j hj.1 hj.2]`. Use `D.R.m_add_three_le_k` as an intermediate fact. Simplify using `only [Ranks.sigW, Ranks.r]`.

Use linear arithmetic over natural numbers and integers. Take `⟨J, hJdef⟩ : ∃ J : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] ℝ ⊗[ℤ] latW D j, J = θ.symm.toLinearMap ∘ₗ blk K ∘ₗ θ.toLinearMap` from `⟨_, rfl⟩`. Establish `hJ : ∀ x, thW D j (J x) = blk K (thW D j x)`. Introduce `x`. Rewrite using `[← hθ, ← hθ, hJdef, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`.

Use `⟨J, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[hθ, hθ, hJ, hJ, map_neg]`. Use function extensionality and compare the values at `τ`.

Simplify using `only [blk_apply, hK1, Pi.neg_apply]`. Introduce `x y`. Rewrite using `[efR_formula, efR_formula]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[hJ, hJ, blk_apply, blk_apply, hK2]`.

Introduce `x hx`. Rewrite using `[efR_formula]`. Establish `hu : thW D j x ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[hθ, h0, map_zero]`. Take `⟨τ0, hτ0⟩` from `Function.ne_iff.1 hu`. Establish `hterm : ∀ τ : cmTypeOfSqrt D, 0 ≤ 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) * (star (thW D j (J x) τ) ⬝ᵥ (GW D j τ *ᵥ thW D j x τ))).re ∧ (thW D j x τ ≠ 0 → 0 < 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) * (star (thW D j (J x) τ) ⬝ᵥ (GW D j τ *ᵥ thW D j x τ))).re)`. Introduce `τ`.

Rewrite using `[hJ, blk_apply]`. Conclude with `term_pos _ (hc τ) (K τ) (GW D j τ) (hK3 τ) (thW D j x τ)`. Conclude with `Finset.sum_pos' (fun τ _ => (hterm τ).1) ⟨τ0, Finset.mem_univ _, (hterm τ0).2 hτ0⟩`. Introduce `a A t hA ht`. Establish `hA' : ∀ z, θ (A z) = AW D j a (θ z)` using `fun z => (hθ (A z)).trans ((thW_AW D j a A hA z).trans (congrArg (AW D j a) (hθ z).symm))`.

Establish `hJ' : ∀ z, θ (J z) = blk K (θ z)` using `fun z => (hθ (J z)).trans ((hJ z).trans (congrArg (blk K) (hθ z).symm))`. Establish `hconjA : θ.conj A = AW D j a`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[LinearEquiv.conj_apply_apply, hA', LinearEquiv.apply_symm_apply]`.

Establish `hconjJA : θ.conj (J ∘ₗ A) = blk K ∘ₗ AW D j a`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ', hA', LinearEquiv.apply_symm_apply, LinearMap.comp_apply]`. Establish `hcomm' : J ∘ₗ A = A ∘ₗ J`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `z`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hJ', hA', hA', hJ']`. Conclude with `LinearMap.congr_fun (AW_comm D j a K) (θ z)`.

Establish `htrA : LinearMap.trace ℝ _ A = LinearMap.trace ℝ _ (AW D j a)`. Rewrite using `[← hconjA, LinearMap.trace_conj']`. Establish `htrJA : LinearMap.trace ℝ _ (J ∘ₗ A) = LinearMap.trace ℝ _ (blk K ∘ₗ AW D j a)`. Rewrite using `[← hconjJA, LinearMap.trace_conj']`. Rewrite `ht` using `[sum_filter_eq_sum_cm_type D]`.

Substitute `ht` using the available equality. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hcomm'`. Rewrite using `[htrA, trace_AW, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations.

Rewrite using `[hr]`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[htrJA, trace_K_AW, Complex.im_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[hK4]`. Simplify using `only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem domFor_pm (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (hI : DatInt D j) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ DomFor D j (ε • intForm (efQ D j) hI) := by
  classical
  set ε : ℤ := if 0 < (D.host.φ₀ D.host.sqrtMinusD).im then 1 else -1 with hεdef
  refine ⟨ε, by by_cases h : 0 < (D.host.φ₀ D.host.sqrtMinusD).im <;> simp [ε, h], ?_⟩
  have hc : ∀ τ : cmTypeOfSqrt D, 0 < ((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0).im :=
    fun τ => xi0_embedding_im_pos D τ τ.2
  obtain ⟨θ, hθ⟩ : ∃ θ : (ℝ ⊗[ℤ] latW D j) ≃ₗ[ℝ] (cmTypeOfSqrt D → Fin (D.sp.W j).rank → ℂ),
      ∀ x, θ x = thW D j x := ⟨LinearEquiv.ofBijective _ (thW_bijective D j), fun _ => rfl⟩
  have hsig : ∀ τ : cmTypeOfSqrt D, ∃ K : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ,
      (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (GW D j τ *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (GW D j τ *ᵥ w)) ∧
      (∀ u, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (GW D j τ *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * (((D.R.sigW j).1 : ℂ) - (D.R.sigW j).2) := by
    intro τ
    have h1 := D.sp.W_sig j (τ : D.host.E →+* ℂ)
    rw [D.sp.W_sigval j hj.1 hj.2] at h1
    obtain ⟨e, P, hP⟩ := h1
    exact exists_cplx_str _ _ _ e P hP
  choose K hK1 hK2 hK3 hK4 using hsig
  have hr : (D.sp.W j).rank = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    rw [D.sp.W_rank j hj.1 hj.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.sigW, Ranks.r]
    omega
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] ℝ ⊗[ℤ] latW D j,
      J = θ.symm.toLinearMap ∘ₗ blk K ∘ₗ θ.toLinearMap := ⟨_, rfl⟩
  have hJ : ∀ x, thW D j (J x) = blk K (thW D j x) := by
    intro x
    rw [← hθ, ← hθ, hJdef, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    apply θ.injective
    rw [hθ, hθ, hJ, hJ, map_neg]
    funext τ
    simp only [blk_apply, hK1, Pi.neg_apply]
  ·
    intro x y
    rw [efR_formula, efR_formula]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hJ, hJ, blk_apply, blk_apply, hK2]
  ·
    intro x hx
    rw [efR_formula]
    have hu : thW D j x ≠ 0 := by
      intro h0
      apply hx
      apply θ.injective
      rw [hθ, h0, map_zero]
    obtain ⟨τ0, hτ0⟩ := Function.ne_iff.1 hu
    have hterm : ∀ τ : cmTypeOfSqrt D, 0 ≤ 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
          (star (thW D j (J x) τ) ⬝ᵥ (GW D j τ *ᵥ thW D j x τ))).re ∧
        (thW D j x τ ≠ 0 → 0 < 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
          (star (thW D j (J x) τ) ⬝ᵥ (GW D j τ *ᵥ thW D j x τ))).re) := by
      intro τ
      rw [hJ, blk_apply]
      exact term_pos _ (hc τ) (K τ) (GW D j τ) (hK3 τ) (thW D j x τ)
    exact Finset.sum_pos' (fun τ _ => (hterm τ).1) ⟨τ0, Finset.mem_univ _, (hterm τ0).2 hτ0⟩
  ·
    intro a A t hA ht
    have hA' : ∀ z, θ (A z) = AW D j a (θ z) := fun z =>
      (hθ (A z)).trans ((thW_AW D j a A hA z).trans (congrArg (AW D j a) (hθ z).symm))
    have hJ' : ∀ z, θ (J z) = blk K (θ z) := fun z =>
      (hθ (J z)).trans ((hJ z).trans (congrArg (blk K) (hθ z).symm))
    have hconjA : θ.conj A = AW D j a := by
      apply LinearMap.ext
      intro u
      rw [LinearEquiv.conj_apply_apply, hA', LinearEquiv.apply_symm_apply]
    have hconjJA : θ.conj (J ∘ₗ A) = blk K ∘ₗ AW D j a := by
      apply LinearMap.ext
      intro u
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ', hA', LinearEquiv.apply_symm_apply,
        LinearMap.comp_apply]
    have hcomm' : J ∘ₗ A = A ∘ₗ J := by
      apply LinearMap.ext
      intro z
      apply θ.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hJ', hA', hA', hJ']
      exact LinearMap.congr_fun (AW_comm D j a K) (θ z)
    have htrA : LinearMap.trace ℝ _ A = LinearMap.trace ℝ _ (AW D j a) := by
      rw [← hconjA, LinearMap.trace_conj']
    have htrJA : LinearMap.trace ℝ _ (J ∘ₗ A) = LinearMap.trace ℝ _ (blk K ∘ₗ AW D j a) := by
      rw [← hconjJA, LinearMap.trace_conj']
    rw [sum_filter_eq_sum_cm_type D] at ht
    subst ht
    refine ⟨?_, ?_, ?_⟩
    · exact hcomm'
    · rw [htrA, trace_AW, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [hr]
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.conj_re,
        Complex.conj_im]
      push_cast
      ring
    · rw [htrJA, trace_K_AW, Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [hK4]
      simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      ring

/- English proof (translation)
Take `⟨ε, hε, hd⟩` from `domFor_pm D j hj hI`. Unfold `DatDom efW sgnW`. Use `split_ifs with h`. Take `⟨hI', h'⟩` from `h`. Rewrite using `[one_smul]`.

Conclude with `h'`. Break down `hε with rfl | rfl` into its components or cases. Conclude with `absurd ⟨hI, by rwa [one_smul] at hd⟩ h`. Conclude with `hd`.
-/
theorem datDom_holds (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (hI : DatInt D j) : DatDom D j hI := by
  obtain ⟨ε, hε, hd⟩ := domFor_pm D j hj hI
  unfold DatDom efW sgnW
  split_ifs with h
  · obtain ⟨hI', h'⟩ := h
    rw [one_smul]
    exact h'
  · rcases hε with rfl | rfl
    · exact absurd ⟨hI, by rwa [one_smul] at hd⟩ h
    · exact hd

def datumW (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum (hostOfRecord D) :=
  datumOfRecord D j hj Formalism.IndefR.Fin.factPrincipalDatum (datDom_holds D j hj _)

end Formalism.L2.Pj
