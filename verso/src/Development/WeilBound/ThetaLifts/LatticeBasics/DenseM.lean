import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexOrder Kronecker

variable {n d : ℕ}

def hf (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  trace (xᵀ * A * y.map star * Cᵀ)

def cs (θ : Matrix (Fin n) (Fin n) ℂ) (θ' : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin d) ℂ where
  toFun x := Complex.I • (θ * x * θ'ᵀ)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' t x := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    rw [smul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']`.
-/
theorem map_star_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) ℂ) (y : Matrix (Fin b) (Fin c) ℂ) :
    (x * y).map star = x.map star * y.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, star_mul']`.
-/
private theorem map_star_smul_matrix {a b : ℕ} (c : ℂ) (M : Matrix (Fin a) (Fin b) ℂ) :
    (c • M).map star = star c • M.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, star_mul']

/- English proof (translation)
Rewrite using `[show cs θ θ' x = Complex.I • (θ * x * θ'ᵀ) from rfl, map_star_smul_matrix, map_star_mul, map_star_mul, Matrix.transpose_map, show star Complex.I = -Complex.I from Complex.conj_I]`.
-/
theorem star_cs (θ : Matrix (Fin n) (Fin n) ℂ) (θ' : Matrix (Fin d) (Fin d) ℂ) (x) :
    (cs θ θ' x).map star = (-Complex.I) • (θ.map star * x.map star * (θ'.map star)ᵀ) := by
  rw [show cs θ θ' x = Complex.I • (θ * x * θ'ᵀ) from rfl, map_star_smul_matrix, map_star_mul, map_star_mul,
    Matrix.transpose_map, show star Complex.I = -Complex.I from Complex.conj_I]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hbar : θ.map star * θ.map star = 1`. Rewrite using `[← map_star_mul, h1, Matrix.map_one _ (by simp) (by simp)]`. Establish `hcomm : θᵀ * M = M * θ.map star`. Combine the equalities or inequalities in the displayed calculation.

Establish `hH : (M * θ.map star).IsHermitian`. Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_mul, hM, ← hcomm]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply]`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_` and prove the remaining obligations. Establish `hy : θ *ᵥ star x ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Establish `h5 : θ *ᵥ (θ *ᵥ star x) = 0` using `by rw [h0, Matrix.mulVec_zero]`. Rewrite `h5` using `[Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Simplify using `using h5`. Establish `hs : star (θ *ᵥ star x) = θ.map star *ᵥ x`. Use extensionality with `i`.

Simplify using `[Matrix.mulVec, dotProduct, star_sum, star_mul']`. Establish `heq : (θ *ᵥ (θ *ᵥ star x)) ⬝ᵥ M *ᵥ star (θ *ᵥ star x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x`. Rewrite using `[Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, hs, Matrix.mulVec_mulVec]`. Establish `hpos` using `h3 _ hy`. Rewrite using `[Complex.pos_iff]`.

Use `⟨by rw [← heq]; exact hpos, ?_⟩` and prove the remaining obligations. Establish `him` using `hH.im_star_dotProduct_mulVec_self x`. Simplify using `only [RCLike.im_to_complex] at him`. Conclude with `him.symm`.
-/
theorem posDef_cartan {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (h : IsCartan M θ) : (M * θ.map star).PosDef := by
  obtain ⟨h1, h2, h3⟩ := h
  have hbar : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1, Matrix.map_one _ (by simp) (by simp)]
  have hcomm : θᵀ * M = M * θ.map star := by
    calc θᵀ * M = θᵀ * M * (θ.map star * θ.map star) := by rw [hbar, Matrix.mul_one]
      _ = (θᵀ * M * θ.map star) * θ.map star := by simp only [Matrix.mul_assoc]
      _ = M * θ.map star := by rw [h2]
  have hH : (M * θ.map star).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hM, ← hcomm]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hy : θ *ᵥ star x ≠ 0 := by
    intro h0
    apply hx
    have h5 : θ *ᵥ (θ *ᵥ star x) = 0 := by rw [h0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h5
    simpa using h5
  have hs : star (θ *ᵥ star x) = θ.map star *ᵥ x := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  have heq : (θ *ᵥ (θ *ᵥ star x)) ⬝ᵥ M *ᵥ star (θ *ᵥ star x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, hs, Matrix.mulVec_mulVec]
  have hpos := h3 _ hy
  rw [Complex.pos_iff]
  refine ⟨by rw [← heq]; exact hpos, ?_⟩
  have him := hH.im_star_dotProduct_mulVec_self x
  simp only [RCLike.im_to_complex] at him
  exact him.symm

variable {A θ : Matrix (Fin n) (Fin n) ℂ} {C θ' : Matrix (Fin d) (Fin d) ℂ}

/- English proof (translation)
Establish `e : θ'ᵀ * C * θ'.map star = C`. Use `h'.2.1` as an intermediate fact. Rewrite `this` using `[Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `smul_right_injective _ Complex.I_ne_zero this`. Establish `e' : (θ'.map star)ᵀ * Cᵀ * θ' = Cᵀ`.

Simplify `congrArg transpose e` using `only [transpose_mul, transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[hf, star_cs, hf]`. Simplify using `only [cs, LinearMap.coe_mk, AddHom.coe_mk, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, transpose_mul, transpose_transpose]`. Rewrite using `[neg_mul, Complex.I_mul_I, neg_neg, one_smul]`. Use `conv_rhs => rw [← h.2.1, ← e']`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hf_cs_cs (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ') (x y) :
    hf A C (cs θ θ' x) (cs θ θ' y) = hf A C x y := by
  have e : θ'ᵀ * C * θ'.map star = C := by
    have := h'.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have e' : (θ'.map star)ᵀ * Cᵀ * θ' = Cᵀ := by
    simpa only [transpose_mul, transpose_transpose, Matrix.mul_assoc] using congrArg transpose e
  rw [hf, star_cs, hf]
  simp only [cs, LinearMap.coe_mk, AddHom.coe_mk, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul,
    transpose_mul, transpose_transpose]
  rw [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  conv_rhs => rw [← h.2.1, ← e']
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Use `show Complex.I • (θ * (Complex.I • (θ * x * θ'ᵀ)) * θ'ᵀ) = -x`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]`. Establish `e1 : θ * (θ * x * θ'ᵀ) * θ'ᵀ = x`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h'.1, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[e1, neg_one_smul]`.
-/
theorem cs_cs (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ') (x) : cs θ θ' (cs θ θ' x) = -x := by
  show Complex.I • (θ * (Complex.I • (θ * x * θ'ᵀ)) * θ'ᵀ) = -x
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
  have e1 : θ * (θ * x * θ'ᵀ) * θ'ᵀ = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, h'.1, Matrix.transpose_one, Matrix.mul_one]
  rw [e1, neg_one_smul]

/- English proof (translation)
Unfold `hf`. Rewrite using `[Matrix.map_neg _ star_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]`.
-/
private theorem hf_neg_right_lattice_basics (u v : Matrix (Fin n) (Fin d) ℂ) : hf A C u (-v) = -hf A C u v := by
  unfold hf
  rw [Matrix.map_neg _ star_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem hf_cs (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ') (x y) :
    hf A C (cs θ θ' x) y = -hf A C x (cs θ θ' y) := by
  calc hf A C (cs θ θ' x) y = hf A C (cs θ θ' x) (cs θ θ' (cs θ θ' (-y))) := by rw [cs_cs h h', neg_neg]
    _ = hf A C x (cs θ θ' (-y)) := hf_cs_cs h h' x _
    _ = -hf A C x (cs θ θ' y) := by rw [map_neg, hf_neg_right_lattice_basics]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Fintype.sum_prod_type, Pi.star_apply, Matrix.map_apply, star_star]`. Conclude with `Finset.sum_comm`.
-/
private theorem trace_transpose_mul_eq_star_dotProduct (x W : Matrix (Fin n) (Fin d) ℂ) :
    trace (xᵀ * W) = star (fun p : Fin n × Fin d => x.map star p.1 p.2) ⬝ᵥ (fun p => W p.1 p.2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
    Fintype.sum_prod_type, Pi.star_apply, Matrix.map_apply, star_star]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨i, a⟩` from `p`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem kroneckerMap_mul_mulVec_eq_mul_mul_transpose (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ)
    (Z : Matrix (Fin n) (Fin d) ℂ) :
    Matrix.kroneckerMap (fun a b => a * b) P Q *ᵥ (fun p : Fin n × Fin d => Z p.1 p.2) =
      fun p => (P * Z * Qᵀ) p.1 p.2 := by
  funext p
  obtain ⟨i, a⟩ := p
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hK` using `(posDef_cartan hA h).kronecker (posDef_cartan hC h')`. Establish `key1 : hf A C x (cs θ θ' x) = -trace (xᵀ * (A * θ.map star * x.map star * (Complex.I • C * θ'.map star)ᵀ))`. Unfold `hf`. Rewrite using `[star_cs]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_assoc, neg_smul, Matrix.trace_neg, Matrix.mul_neg, Matrix.neg_mul]`.

Establish `hz : (fun p : Fin n × Fin d => x.map star p.1 p.2) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Use extensionality with `i a`. Use `congrFun h0 (i, a)` as an intermediate fact.

Simplify using `using this`. Establish `hpos` using `hK.re_dotProduct_pos hz`. Rewrite using `[key1, trace_transpose_mul_eq_star_dotProduct, ← kroneckerMap_mul_mulVec_eq_mul_mul_transpose (A * θ.map star) (Complex.I • C * θ'.map star) (x.map star)]`. Simplify using `only [RCLike.re_to_complex] at hpos`. Rewrite using `[Complex.neg_re]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hf_neg (hA : Aᴴ = A) (hC : (Complex.I • C)ᴴ = Complex.I • C) (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ')
    {x : Matrix (Fin n) (Fin d) ℂ} (hx : x ≠ 0) : (hf A C x (cs θ θ' x)).re < 0 := by
  have hK := (posDef_cartan hA h).kronecker (posDef_cartan hC h')
  have key1 : hf A C x (cs θ θ' x) =
      -trace (xᵀ * (A * θ.map star * x.map star * (Complex.I • C * θ'.map star)ᵀ)) := by
    unfold hf
    rw [star_cs]
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.mul_assoc, neg_smul, Matrix.trace_neg, Matrix.mul_neg, Matrix.neg_mul]
  have hz : (fun p : Fin n × Fin d => x.map star p.1 p.2) ≠ 0 := by
    intro h0
    apply hx
    ext i a
    have := congrFun h0 (i, a)
    simpa using this
  have hpos := hK.re_dotProduct_pos hz
  rw [key1, trace_transpose_mul_eq_star_dotProduct, ← kroneckerMap_mul_mulVec_eq_mul_mul_transpose (A * θ.map star) (Complex.I • C * θ'.map star) (x.map star)]
  simp only [RCLike.re_to_complex] at hpos
  rw [Complex.neg_re]
  linarith

end GlobalTheory.ThK.Dbl.Dense

end
