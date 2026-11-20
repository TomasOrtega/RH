import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo

open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace GlobalTheory.HermFrame

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

def form (H : Matrix n n ℂ) (v w : n → ℂ) : ℂ := v ⬝ᵥ H *ᵥ star w

def gnorm (H : Matrix n n ℂ) (v : n → ℂ) : ℝ := √(form H v v).re

/- English proof (translation)
Simplify using `[form, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem form_eq_sum (H : Matrix n n ℂ) (v w : n → ℂ) :
    form H v w = ∑ a, ∑ b, v a * H a b * conj (w b) := by
  simp [form, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[form_eq_sum, Pi.single_apply, apply_ite]`.
-/
theorem form_single [DecidableEq n] (H : Matrix n n ℂ) (a b : n) :
    form H (Pi.single a 1) (Pi.single b 1) = H a b := by
  simp [form_eq_sum, Pi.single_apply, apply_ite]

/- English proof (translation)
Rewrite using `[form, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]`.
-/
theorem form_eq_transpose (H : Matrix n n ℂ) (v w : n → ℂ) :
    form H v w = star w ⬝ᵥ Hᵀ *ᵥ v := by
  rw [form, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/- English proof (translation)
Simplify using `[form]`.
-/
theorem form_add_left (H : Matrix n n ℂ) (v v' w : n → ℂ) :
    form H (v + v') w = form H v w + form H v' w := by simp [form]

/- English proof (translation)
Simplify using `[form, mulVec_add]`.
-/
theorem form_add_right (H : Matrix n n ℂ) (v w w' : n → ℂ) :
    form H v (w + w') = form H v w + form H v w' := by simp [form, mulVec_add]

/- English proof (translation)
Simplify using `[form]`.
-/
theorem form_smul_left (H : Matrix n n ℂ) (c : ℂ) (v w : n → ℂ) :
    form H (c • v) w = c * form H v w := by simp [form]

/- English proof (translation)
Simplify using `[form, mulVec_smul]`.
-/
theorem form_smul_right (H : Matrix n n ℂ) (c : ℂ) (v w : n → ℂ) :
    form H v (c • w) = conj c * form H v w := by simp [form, mulVec_smul]

/- English proof (translation)
Simplify using `[form]`.
-/
theorem form_sub_left (H : Matrix n n ℂ) (v v' w : n → ℂ) :
    form H (v - v') w = form H v w - form H v' w := by simp [form]

/- English proof (translation)
Simplify using `[form, mulVec_sub]`.
-/
theorem form_sub_right (H : Matrix n n ℂ) (v w w' : n → ℂ) :
    form H v (w - w') = form H v w - form H v w' := by simp [form, mulVec_sub]

/- English proof (translation)
Simplify using `[form, add_mulVec]`.
-/
theorem form_add (H K : Matrix n n ℂ) (v w : n → ℂ) :
    form (H + K) v w = form H v w + form K v w := by simp [form, add_mulVec]

/- English proof (translation)
Simplify using `[form, smul_mulVec]`.
-/
theorem form_smul (c : ℂ) (H : Matrix n n ℂ) (v w : n → ℂ) :
    form (c • H) v w = c * form H v w := by simp [form, smul_mulVec]

/- English proof (translation)
Simplify using `only [form_eq_sum, map_sum, map_mul, conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hH.apply a b]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_form {H : Matrix n n ℂ} (hH : H.IsHermitian) (v w : n → ℂ) :
    conj (form H v w) = form H w v := by
  simp only [form_eq_sum, map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b]; simp; ring

/- English proof (translation)
Rewrite using `[form, star_mulVec, ← mulVec_transpose, ← vecMul_transpose, ← dotProduct_mulVec]`. Simplify using `only [mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem form_mulVec (K : Matrix n n ℂ) (A : Matrix n m ℂ) (B : Matrix n l ℂ) (u : m → ℂ)
    (w : l → ℂ) : form K (A *ᵥ u) (B *ᵥ w) = u ⬝ᵥ (Aᵀ * K * Bᴴᵀ) *ᵥ star w := by
  rw [form, star_mulVec, ← mulVec_transpose, ← vecMul_transpose, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h.isHermitian, fun v hv => ?_⟩` and prove the remaining obligations. Simplify `h.dotProduct_mulVec_pos (x := star v) (by simpa using hv)` using `[form]`. Introduce and unpack `⟨h, h'⟩`.

Use `PosDef.of_dotProduct_mulVec_pos h fun x hx => ?_` and prove the remaining obligations. Simplify `h' (star x) (by simpa using hx)` using `[form]`.
-/
theorem posDef_iff {H : Matrix n n ℂ} :
    H.PosDef ↔ H.IsHermitian ∧ ∀ v, v ≠ 0 → 0 < form H v v := by
  constructor
  · intro h
    refine ⟨h.isHermitian, fun v hv => ?_⟩
    simpa [form] using h.dotProduct_mulVec_pos (x := star v) (by simpa using hv)
  · rintro ⟨h, h'⟩
    refine PosDef.of_dotProduct_mulVec_pos h fun x hx => ?_
    simpa [form] using h' (star x) (by simpa using hx)

/- English proof (translation)
Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.transpose.nonneg`. Establish `h1 : ∀ v w, form H v w = inner ℂ (WithLp.toLp 2 (B *ᵥ w)) (WithLp.toLp 2 (B *ᵥ v))` using `fun v w => by`. Rewrite using `[form_eq_transpose, hB, EuclideanSpace.inner_toLp_toLp, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_comm, star_eq_conjTranspose]`. Use `⟨(WithLp.linearEquiv 2 ℂ (n → ℂ)).symm.toLinearMap ∘ₗ B.mulVecLin, h1, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[gnorm, h1, inner_self_eq_norm_sq_to_K]`.

Use `norm_cast`. Conclude with `Real.sqrt_sq (norm_nonneg _)`.
-/
theorem exists_root {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    ∃ R : (n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ n,
      (∀ v w, form H v w = inner ℂ (R w) (R v)) ∧ ∀ v, gnorm H v = ‖R v‖ := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.transpose.nonneg
  have h1 : ∀ v w, form H v w =
      inner ℂ (WithLp.toLp 2 (B *ᵥ w)) (WithLp.toLp 2 (B *ᵥ v)) := fun v w => by
    rw [form_eq_transpose, hB, EuclideanSpace.inner_toLp_toLp, star_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, dotProduct_comm, star_eq_conjTranspose]
  refine ⟨(WithLp.linearEquiv 2 ℂ (n → ℂ)).symm.toLinearMap ∘ₗ B.mulVecLin, h1, fun v => ?_⟩
  rw [gnorm, h1, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact Real.sqrt_sq (norm_nonneg _)

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem gnorm_nonneg (H : Matrix n n ℂ) (v : n → ℂ) : 0 ≤ gnorm H v := Real.sqrt_nonneg _

/- English proof (translation)
Take `⟨R, h1, h2⟩` from `exists_root hH`. Rewrite using `[h1, h2, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules.
-/
theorem form_self {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) :
    form H v v = ((gnorm H v ^ 2 : ℝ) : ℂ) := by
  obtain ⟨R, h1, h2⟩ := exists_root hH
  rw [h1, h2, inner_self_eq_norm_sq_to_K]; simp

/- English proof (translation)
Rewrite using `[form_self hH, ofReal_re]`.
-/
theorem gnorm_sq {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) :
    gnorm H v ^ 2 = (form H v v).re := by rw [form_self hH, ofReal_re]

/- English proof (translation)
Take `⟨R, -, h2⟩` from `exists_root hH`. Rewrite using `[h2, h2, map_smul, norm_smul]`.
-/
theorem gnorm_smul {H : Matrix n n ℂ} (hH : H.PosSemidef) (c : ℂ) (v : n → ℂ) :
    gnorm H (c • v) = ‖c‖ * gnorm H v := by
  obtain ⟨R, -, h2⟩ := exists_root hH
  rw [h2, h2, map_smul, norm_smul]

/- English proof (translation)
Take `⟨R, -, h2⟩` from `exists_root hH`. Rewrite using `[h2, h2, h2, map_add]`. Conclude with `norm_add_le _ _`.
-/
theorem gnorm_add_le {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    gnorm H (v + w) ≤ gnorm H v + gnorm H w := by
  obtain ⟨R, -, h2⟩ := exists_root hH
  rw [h2, h2, h2, map_add]; exact norm_add_le _ _

/- English proof (translation)
Take `⟨R, h1, h2⟩` from `exists_root hH`. Rewrite using `[h1, h2, h2, mul_comm]`. Conclude with `norm_inner_le_norm _ _`.
-/
theorem norm_form_le {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    ‖form H v w‖ ≤ gnorm H v * gnorm H w := by
  obtain ⟨R, h1, h2⟩ := exists_root hH
  rw [h1, h2, h2, mul_comm]; exact norm_inner_le_norm _ _

/- English proof (translation)
Simplify using `only [gnorm_sq hH, form_add_left, form_add_right, form_sub_left, form_sub_right, add_re, sub_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gnorm_parallelogram {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    gnorm H (v + w) ^ 2 + gnorm H (v - w) ^ 2 = 2 * (gnorm H v ^ 2 + gnorm H w ^ 2) := by
  simp only [gnorm_sq hH, form_add_left, form_add_right, form_sub_left, form_sub_right, add_re,
    sub_re]
  ring

/- English proof (translation)
Simplify using `[gnorm, form]`.
-/
@[simp] theorem gnorm_zero (H : Matrix n n ℂ) : gnorm H 0 = 0 := by simp [gnorm, form]

/- English proof (translation)
The claim follows from `Real.sqrt_pos.2 (Complex.lt_def.1 ((posDef_iff.1 hH).2 v hv)).1`.
-/
theorem gnorm_pos {H : Matrix n n ℂ} (hH : H.PosDef) {v : n → ℂ} (hv : v ≠ 0) : 0 < gnorm H v :=
  Real.sqrt_pos.2 (Complex.lt_def.1 ((posDef_iff.1 hH).2 v hv)).1

def adj [DecidableEq m] (H : Matrix m m ℂ) (K : Matrix n n ℂ) (T : Matrix n m ℂ) : Matrix m n ℂ :=
  Hᵀ⁻¹ * Tᴴ * Kᵀ

/- English proof (translation)
Establish `hu' : IsUnit Hᵀ.det` using `by rwa [det_transpose]`. Rewrite using `[← conj_form hH, ← conj_form hK, form_eq_transpose, form_eq_transpose, adj, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.one_mul, ← mulVec_mulVec, dotProduct_mulVec (star v), star_mulVec]`.
-/
theorem form_adj [DecidableEq m] {H : Matrix m m ℂ} {K : Matrix n n ℂ} (hH : H.IsHermitian)
    (hu : IsUnit H.det) (hK : K.IsHermitian) (T : Matrix n m ℂ) (v : m → ℂ) (w : n → ℂ) :
    form K (T *ᵥ v) w = form H v (adj H K T *ᵥ w) := by
  have hu' : IsUnit Hᵀ.det := by rwa [det_transpose]
  rw [← conj_form hH, ← conj_form hK, form_eq_transpose, form_eq_transpose, adj, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.one_mul,
    ← mulVec_mulVec, dotProduct_mulVec (star v), star_mulVec]

def opNorm (H : Matrix m m ℂ) (K : Matrix n n ℂ) (T : Matrix n m ℂ) : ℝ :=
  sInf {C | 0 ≤ C ∧ ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v}

section OpNorm

variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}

/- English proof (translation)
Take `⟨R, -, h2⟩` from `exists_root hH.posSemidef`. Take `⟨S, -, h3⟩` from `exists_root hK`. Establish `hR : LinearMap.ker R = ⊥` using `LinearMap.ker_eq_bot'.2 fun v hv => by`. Assume the negation of the conclusion as `h`. Use `gnorm_pos hH h` as an intermediate fact.

Rewrite `this` using `[h2, hv, norm_zero]`. Conclude with `lt_irrefl _ this`. Take `⟨g, hg⟩` from `R.exists_leftInverse_of_injective hR`. Set `A` to `LinearMap.toContinuousLinearMap (S ∘ₗ T.mulVecLin ∘ₗ g)`. Use `⟨‖A‖, norm_nonneg _, fun v => ?_⟩` and prove the remaining obligations.

Establish `hv : g (R v) = v` using `by simpa using LinearMap.congr_fun hg v`. Use `A.le_opNorm (R v)` as an intermediate fact. Rewrite using `[h2, h3]`. Simplify `this` using `[A, hv]`.
-/
theorem exists_bound (hH : H.PosDef) (hK : K.PosSemidef) (T : Matrix n m ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v := by
  obtain ⟨R, -, h2⟩ := exists_root hH.posSemidef
  obtain ⟨S, -, h3⟩ := exists_root hK
  have hR : LinearMap.ker R = ⊥ := LinearMap.ker_eq_bot'.2 fun v hv => by
    by_contra h
    have := gnorm_pos hH h
    rw [h2, hv, norm_zero] at this
    exact lt_irrefl _ this
  obtain ⟨g, hg⟩ := R.exists_leftInverse_of_injective hR
  let A := LinearMap.toContinuousLinearMap (S ∘ₗ T.mulVecLin ∘ₗ g)
  refine ⟨‖A‖, norm_nonneg _, fun v => ?_⟩
  have hv : g (R v) = v := by simpa using LinearMap.congr_fun hg v
  have := A.le_opNorm (R v)
  rw [h2, h3]
  simpa [A, hv] using this

/- English proof (translation)
The claim follows from `Real.sInf_nonneg fun _ h => h.1`.
-/
theorem opNorm_nonneg (H : Matrix m m ℂ) (K : Matrix n n ℂ) (T : Matrix n m ℂ) :
    0 ≤ opNorm H K T := Real.sInf_nonneg fun _ h => h.1

/- English proof (translation)
The claim follows from `csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, h⟩`.
-/
theorem opNorm_le_of_bound {T : Matrix n m ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v) : opNorm H K T ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, h⟩

/- English proof (translation)
Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Establish `hp` using `gnorm_pos hH hv`. Rewrite using `[← div_le_iff₀ hp]`. Conclude with `le_csInf (exists_bound hH hK T) fun C hC => (div_le_iff₀ hp).2 (hC.2 v)`.
-/
theorem gnorm_mulVec_le (hH : H.PosDef) (hK : K.PosSemidef) (T : Matrix n m ℂ) (v : m → ℂ) :
    gnorm K (T *ᵥ v) ≤ opNorm H K T * gnorm H v := by
  by_cases hv : v = 0
  · simp [hv]
  · have hp := gnorm_pos hH hv
    rw [← div_le_iff₀ hp]
    exact le_csInf (exists_bound hH hK T) fun C hC => (div_le_iff₀ hp).2 (hC.2 v)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨(opNorm_nonneg H K T).trans h, fun v => (gnorm_mulVec_le hH hK T v).trans (mul_le_mul_of_nonneg_right h (gnorm_nonneg _ _))⟩, fun h => opNorm_le_of_bound h.1 h.2⟩`.
-/
theorem opNorm_le_iff (hH : H.PosDef) (hK : K.PosSemidef) {T : Matrix n m ℂ} {C : ℝ} :
    opNorm H K T ≤ C ↔ 0 ≤ C ∧ ∀ v, gnorm K (T *ᵥ v) ≤ C * gnorm H v :=
  ⟨fun h => ⟨(opNorm_nonneg H K T).trans h, fun v => (gnorm_mulVec_le hH hK T v).trans
    (mul_le_mul_of_nonneg_right h (gnorm_nonneg _ _))⟩, fun h => opNorm_le_of_bound h.1 h.2⟩

/- English proof (translation)
The claim follows from `le_antisymm (opNorm_le_of_bound le_rfl fun v => by simp) (opNorm_nonneg _ _ _)`.
-/
@[simp] theorem opNorm_zero (H : Matrix m m ℂ) (K : Matrix n n ℂ) : opNorm H K 0 = 0 :=
  le_antisymm (opNorm_le_of_bound le_rfl fun v => by simp) (opNorm_nonneg _ _ _)

/- English proof (translation)
The claim follows from `opNorm_le_of_bound (add_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _)) fun v => by rw [add_mulVec, add_mul] exact (gnorm_add_le hK _ _).trans (add_le_add (gnorm_mulVec_le hH hK S v) (gnorm_mulVec_le hH hK T v))`.
-/
theorem opNorm_add_le (hH : H.PosDef) (hK : K.PosSemidef) (S T : Matrix n m ℂ) :
    opNorm H K (S + T) ≤ opNorm H K S + opNorm H K T :=
  opNorm_le_of_bound (add_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _)) fun v => by
    rw [add_mulVec, add_mul]
    exact (gnorm_add_le hK _ _).trans
      (add_le_add (gnorm_mulVec_le hH hK S v) (gnorm_mulVec_le hH hK T v))

/- English proof (translation)
The claim follows from `opNorm_le_of_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _ _ _)) fun v => by rw [smul_mulVec, gnorm_smul hK, mul_assoc] exact mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hK T v) (norm_nonneg _)`.
-/
theorem opNorm_smul_le (hH : H.PosDef) (hK : K.PosSemidef) (c : ℂ) (T : Matrix n m ℂ) :
    opNorm H K (c • T) ≤ ‖c‖ * opNorm H K T :=
  opNorm_le_of_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _ _ _)) fun v => by
    rw [smul_mulVec, gnorm_smul hK, mul_assoc]
    exact mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hK T v) (norm_nonneg _)

/- English proof (translation)
The claim follows from `opNorm_le_of_bound (mul_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _)) fun v => by rw [← mulVec_mulVec, mul_assoc] exact (gnorm_mulVec_le hK hL S _).trans (mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hK.posSemidef T v) (opNorm_nonneg _ _ _))`.
-/
theorem opNorm_mul_le (hH : H.PosDef) (hK : K.PosDef) (hL : L.PosSemidef) (S : Matrix l n ℂ)
    (T : Matrix n m ℂ) : opNorm H L (S * T) ≤ opNorm K L S * opNorm H K T :=
  opNorm_le_of_bound (mul_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _)) fun v => by
    rw [← mulVec_mulVec, mul_assoc]
    exact (gnorm_mulVec_le hK hL S _).trans
      (mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hK.posSemidef T v) (opNorm_nonneg _ _ _))

/- English proof (translation)
Establish `h1 : ∀ ε : ℝ, 0 < ε → x ≤ 2 * c * (a + ε) * (b + ε)` using `fun ε hε => by`. Establish `ha' : 0 < a + ε` using `by linarith`. Establish `hb' : 0 < b + ε` using `by linarith`. Use `(h ((b + ε) / (a + ε)) (by positivity)).trans ?_` and prove the remaining obligations. Establish `e1 : (b + ε) / (a + ε) * a ^ 2 ≤ (a + ε) * (b + ε)`.

Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ ha']`. Establish `: a ^ 2 ≤ (a + ε) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : b ^ 2 / ((b + ε) / (a + ε)) ≤ (a + ε) * (b + ε)`. Rewrite using `[div_div_eq_mul_div, div_le_iff₀ hb']`.

Establish `: b ^ 2 ≤ (b + ε) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : Filter.Tendsto (fun ε : ℝ => 2 * c * (a + ε) * (b + ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * c * (a + 0) * (b + 0)))` using `(Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds`. Simplify using `using ge_of_tendsto h2 (eventually_nhdsWithin_of_forall h1)`.
-/
theorem le_two_mul_of_forall_scale {x c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ s, 0 < s → x ≤ c * (s * a ^ 2 + b ^ 2 / s)) : x ≤ 2 * c * a * b := by
  have h1 : ∀ ε : ℝ, 0 < ε → x ≤ 2 * c * (a + ε) * (b + ε) := fun ε hε => by
    have ha' : 0 < a + ε := by linarith
    have hb' : 0 < b + ε := by linarith
    refine (h ((b + ε) / (a + ε)) (by positivity)).trans ?_
    have e1 : (b + ε) / (a + ε) * a ^ 2 ≤ (a + ε) * (b + ε) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha']
      have : a ^ 2 ≤ (a + ε) ^ 2 := by nlinarith
      nlinarith
    have e2 : b ^ 2 / ((b + ε) / (a + ε)) ≤ (a + ε) * (b + ε) := by
      rw [div_div_eq_mul_div, div_le_iff₀ hb']
      have : b ^ 2 ≤ (b + ε) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have h2 : Filter.Tendsto (fun ε : ℝ => 2 * c * (a + ε) * (b + ε)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * c * (a + 0) * (b + 0))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  simpa using ge_of_tendsto h2 (eventually_nhdsWithin_of_forall h1)

/- English proof (translation)
Establish `h1 : ∀ v w, (form H (T *ᵥ v) w).re ≤ c / 2 * (gnorm H v ^ 2 + gnorm H w ^ 2)`. Introduce `v w`. Establish `e : (form H (T *ᵥ w) v).re = (form H (T *ᵥ v) w).re`. Rewrite using `[hT w v, ← conj_form hH.isHermitian, conj_re]`. Establish `a1` using `(re_le_norm _).trans (h (v + w))`.

Establish `a2` using `(abs_le.1 ((abs_re_le_norm _).trans (h (v - w)))).1`. Establish `a3` using `gnorm_parallelogram hH v w`. Simplify using `only [mulVec_add, mulVec_sub, form_add_left, form_add_right, form_sub_left, form_sub_right, add_re, sub_re] at a1 a2`. Establish `a4 : c * gnorm H (v + w) ^ 2 + c * gnorm H (v - w) ^ 2 = 2 * c * (gnorm H v ^ 2 + gnorm H w ^ 2)` using `by rw [← mul_add, a3]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `opNorm_le_of_bound hc fun v => ?_` and prove the remaining obligations. Establish `h2 : (form H (T *ᵥ v) (T *ᵥ v)).re ≤ 2 * (c / 2) * gnorm H v * gnorm H (T *ᵥ v)`. Use `le_two_mul_of_forall_scale (by linarith) (gnorm_nonneg _ _) (gnorm_nonneg _ _) fun s hs => ?_` and prove the remaining obligations. Establish `hq : 0 < √s` using `Real.sqrt_pos.2 hs`. Use `h1 ((√s : ℂ) • v) (((√s)⁻¹ : ℝ) • T *ᵥ v)` as an intermediate fact.

Rewrite `this` using `[← Complex.coe_smul, mulVec_smul, form_smul_left, form_smul_right, gnorm_smul hH, gnorm_smul hH, conj_ofReal, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hq.ne', ofReal_one, one_mul, norm_real, norm_real, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, inv_po …`. Rewrite using `[div_eq_inv_mul _ s]` and apply the resulting hypothesis. Rewrite `h2` using `[← gnorm_sq hH]`. Break down `(gnorm_nonneg H (T *ᵥ v)).eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`.

Conclude with `mul_nonneg hc (gnorm_nonneg _ _)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem opNorm_le_of_selfAdjoint (hH : H.PosSemidef) {T : Matrix m m ℂ}
    (hT : ∀ v w, form H (T *ᵥ v) w = form H v (T *ᵥ w)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, ‖form H (T *ᵥ v) v‖ ≤ c * gnorm H v ^ 2) : opNorm H H T ≤ c := by
  have h1 : ∀ v w, (form H (T *ᵥ v) w).re ≤ c / 2 * (gnorm H v ^ 2 + gnorm H w ^ 2) := by
    intro v w
    have e : (form H (T *ᵥ w) v).re = (form H (T *ᵥ v) w).re := by
      rw [hT w v, ← conj_form hH.isHermitian, conj_re]
    have a1 := (re_le_norm _).trans (h (v + w))
    have a2 := (abs_le.1 ((abs_re_le_norm _).trans (h (v - w)))).1
    have a3 := gnorm_parallelogram hH v w
    simp only [mulVec_add, mulVec_sub, form_add_left, form_add_right, form_sub_left,
      form_sub_right, add_re, sub_re] at a1 a2
    have a4 : c * gnorm H (v + w) ^ 2 + c * gnorm H (v - w) ^ 2 =
      2 * c * (gnorm H v ^ 2 + gnorm H w ^ 2) := by rw [← mul_add, a3]; ring
    linarith
  refine opNorm_le_of_bound hc fun v => ?_
  have h2 : (form H (T *ᵥ v) (T *ᵥ v)).re ≤ 2 * (c / 2) * gnorm H v * gnorm H (T *ᵥ v) := by
    refine le_two_mul_of_forall_scale (by linarith) (gnorm_nonneg _ _) (gnorm_nonneg _ _)
      fun s hs => ?_
    have hq : 0 < √s := Real.sqrt_pos.2 hs
    have := h1 ((√s : ℂ) • v) (((√s)⁻¹ : ℝ) • T *ᵥ v)
    rw [← Complex.coe_smul, mulVec_smul, form_smul_left, form_smul_right, gnorm_smul hH,
      gnorm_smul hH, conj_ofReal, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hq.ne', ofReal_one,
      one_mul, norm_real, norm_real, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hs.le] at this
    rwa [div_eq_inv_mul _ s]
  rw [← gnorm_sq hH] at h2
  rcases (gnorm_nonneg H (T *ᵥ v)).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hc (gnorm_nonneg _ _)
  · nlinarith

/- English proof (translation)
Use `(norm_form_le hH.posSemidef _ _).trans ?_` and prove the remaining obligations. Rewrite using `[sq, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (gnorm_mulVec_le hH hH.posSemidef T v) (gnorm_nonneg _ _)`.
-/
theorem norm_form_mulVec_le (hH : H.PosDef) (T : Matrix m m ℂ) (v : m → ℂ) :
    ‖form H (T *ᵥ v) v‖ ≤ opNorm H H T * gnorm H v ^ 2 := by
  refine (norm_form_le hH.posSemidef _ _).trans ?_
  rw [sq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (gnorm_mulVec_le hH hH.posSemidef T v) (gnorm_nonneg _ _)

end OpNorm

section Sesq

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsSesq (F : V → V → M) : Prop where

  add_left : ∀ x x' y, F (x + x') y = F x y + F x' y

  smul_left : ∀ (c : ℂ) x y, F (c • x) y = c • F x y

  add_right : ∀ x y y', F x (y + y') = F x y + F x y'

  smul_right : ∀ (c : ℂ) x y, F x (c • y) = conj c • F x y

/- English proof (translation)
Assemble the required witnesses or components as `⟨form_add_left H, form_smul_left H, form_add_right H, form_smul_right H⟩`.
-/
theorem isSesq_form (H : Matrix n n ℂ) : IsSesq (form H) :=
  ⟨form_add_left H, form_smul_left H, form_add_right H, form_smul_right H⟩

/- English proof (translation)
Establish `h : ∀ v : V, -v = (-1 : ℂ) • v` using `fun v => by simp`. Simplify using `only [sub_eq_add_neg, h, hF.add_left, hF.add_right, hF.smul_left, hF.smul_right, conj_I, map_neg, map_one]`. Apply the tactic sequence `match_scalars <;> (ring_nf; try simp only [I_sq, I_pow_three]; try ring_nf)`.
-/
theorem IsSesq.polarisation {F : V → V → M} (hF : IsSesq F) (x y : V) :
    F x y = (1 / 4 : ℂ) • ((F (x + y) (x + y) + (-1 : ℂ) • F (x - y) (x - y)) +
      (I • F (x + I • y) (x + I • y) + (-I) • F (x - I • y) (x - I • y))) := by
  have h : ∀ v : V, -v = (-1 : ℂ) • v := fun v => by simp
  simp only [sub_eq_add_neg, h, hF.add_left, hF.add_right, hF.smul_left, hF.smul_right, conj_I,
    map_neg, map_one]
  match_scalars <;> (ring_nf; try simp only [I_sq, I_pow_three]; try ring_nf)

end Sesq

/- English proof (translation)
Establish `hH'` using `hH.posSemidef`. Establish `h1 : ∀ x, opNorm H H (F x x) ≤ C * gnorm G x ^ 2` using `fun x => opNorm_le_of_selfAdjoint hH' (hs x) (by positivity) (h x)`. Establish `h2 : ∀ (c : ℂ) x, ‖c‖ = 1 → opNorm H H (c • F x x) ≤ C * gnorm G x ^ 2` using `fun c x hc => (opNorm_smul_le hH hH' c _).trans (by rw [hc, one_mul]; exact h1 x)`. Establish `h3 : ∀ x y, opNorm H H (F x y) ≤ C * (gnorm G x ^ 2 + gnorm G y ^ 2)` using `fun x y => by`. Rewrite using `[hF.polarisation x y]`.

Use `(opNorm_smul_le hH hH' _ _).trans ?_` and prove the remaining obligations. Establish `a` using `(opNorm_add_le hH hH' _ _).trans (add_le_add ((opNorm_add_le hH hH' _ _).trans (add_le_add (h1 (x + y)) (h2 (-1) (x - y) (by simp)))) ((opNorm_add_le hH hH' _ _).trans (add_le_add (h2 I (x + I • y) (by simp)) (h2 (-I) (x - I • y) (by simp)))))`. Establish `b1` using `gnorm_parallelogram hG x y`. Establish `b2` using `gnorm_parallelogram hG x (I • y)`. Rewrite `b2` using `[gnorm_smul hG I, norm_I, one_mul]`.

Rewrite `a` using `[← mul_add, ← mul_add, b1, b2]`. Establish `: ‖(1 / 4 : ℂ)‖ = 1 / 4` using `by simp`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_two_mul_of_forall_scale hC (gnorm_nonneg _ _) (gnorm_nonneg _ _) fun s hs => ?_` and prove the remaining obligations.

Establish `hq : 0 < √s` using `Real.sqrt_pos.2 hs`. Use `h3 ((√s : ℂ) • ξ) ((((√s)⁻¹ : ℝ) : ℂ) • η)` as an intermediate fact. Rewrite `this` using `[hF.smul_left, hF.smul_right, gnorm_smul hG, gnorm_smul hG, conj_ofReal, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hq.ne', ofReal_one, one_smul, norm_real, norm_real, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, inv_pow, Real.sq_sqrt hs.le]`. Rewrite using `[div_eq_inv_mul _ s]` and apply the resulting hypothesis.
-/
theorem opNorm_le_of_diagonal {H : Matrix n n ℂ} {G : Matrix m m ℂ} (hH : H.PosDef)
    (hG : G.PosSemidef) {F : (m → ℂ) → (m → ℂ) → Matrix n n ℂ} (hF : IsSesq F)
    (hs : ∀ ξ v w, form H (F ξ ξ *ᵥ v) w = form H v (F ξ ξ *ᵥ w)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ v, ‖form H (F ξ ξ *ᵥ v) v‖ ≤ C * gnorm G ξ ^ 2 * gnorm H v ^ 2) (ξ η : m → ℂ) :
    opNorm H H (F ξ η) ≤ 2 * C * gnorm G ξ * gnorm G η := by
  have hH' := hH.posSemidef
  have h1 : ∀ x, opNorm H H (F x x) ≤ C * gnorm G x ^ 2 := fun x =>
    opNorm_le_of_selfAdjoint hH' (hs x) (by positivity) (h x)
  have h2 : ∀ (c : ℂ) x, ‖c‖ = 1 → opNorm H H (c • F x x) ≤ C * gnorm G x ^ 2 := fun c x hc =>
    (opNorm_smul_le hH hH' c _).trans (by rw [hc, one_mul]; exact h1 x)
  have h3 : ∀ x y, opNorm H H (F x y) ≤ C * (gnorm G x ^ 2 + gnorm G y ^ 2) := fun x y => by
    rw [hF.polarisation x y]
    refine (opNorm_smul_le hH hH' _ _).trans ?_
    have a := (opNorm_add_le hH hH' _ _).trans (add_le_add
      ((opNorm_add_le hH hH' _ _).trans (add_le_add (h1 (x + y)) (h2 (-1) (x - y) (by simp))))
      ((opNorm_add_le hH hH' _ _).trans (add_le_add (h2 I (x + I • y) (by simp))
        (h2 (-I) (x - I • y) (by simp)))))
    have b1 := gnorm_parallelogram hG x y
    have b2 := gnorm_parallelogram hG x (I • y)
    rw [gnorm_smul hG I, norm_I, one_mul] at b2
    rw [← mul_add, ← mul_add, b1, b2] at a
    have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [this]; linarith
  refine le_two_mul_of_forall_scale hC (gnorm_nonneg _ _) (gnorm_nonneg _ _) fun s hs => ?_
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  have := h3 ((√s : ℂ) • ξ) ((((√s)⁻¹ : ℝ) : ℂ) • η)
  rw [hF.smul_left, hF.smul_right, gnorm_smul hG,
    gnorm_smul hG, conj_ofReal, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hq.ne', ofReal_one,
    one_smul, norm_real, norm_real, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, inv_pow, Real.sq_sqrt hs.le] at this
  rwa [div_eq_inv_mul _ s]

section Blocks

variable [DecidableEq m] [DecidableEq l]

def subGram (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m m ℂ := H.toBlocks₁₁

def quotGram (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix l l ℂ :=
  H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂

def orthCoeff (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m l ℂ := H.toBlocks₁₁ᵀ⁻¹ * H.toBlocks₂₁ᵀ

variable (m l) in

def incl : Matrix (m ⊕ l) m ℂ := fromRows 1 0

variable (m l) in

def quotMap : Matrix l (m ⊕ l) ℂ := fromCols 0 1

def orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix (m ⊕ l) l ℂ := fromRows (-orthCoeff H) 1

def orthProj (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m (m ⊕ l) ℂ := fromCols 1 (orthCoeff H)

def blockSS (H T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m m ℂ := orthProj H * T * incl m l

def blockSQ (H T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix m l ℂ := orthProj H * T * orthLift H

def blockQS (T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix l m ℂ := quotMap m l * T * incl m l

def blockQQ (H T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix l l ℂ := quotMap m l * T * orthLift H

variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks T]`. Simplify using `[blockQS, quotMap, incl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]`.
-/
theorem blockQS_eq (T : Matrix (m ⊕ l) (m ⊕ l) ℂ) : blockQS T = T.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockQS, quotMap, incl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

/- English proof (translation)
Simplify using `[orthProj, incl, fromCols_mul_fromRows]`.
-/
theorem orthProj_mul_incl (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : orthProj H * incl m l = 1 := by
  simp [orthProj, incl, fromCols_mul_fromRows]

/- English proof (translation)
Simplify using `[orthProj, orthLift, fromCols_mul_fromRows]`.
-/
theorem orthProj_mul_orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : orthProj H * orthLift H = 0 := by
  simp [orthProj, orthLift, fromCols_mul_fromRows]

/- English proof (translation)
Simplify using `[quotMap, incl, fromCols_mul_fromRows]`.
-/
theorem quotMap_mul_incl : quotMap m l * incl m l = 0 := by
  simp [quotMap, incl, fromCols_mul_fromRows]

/- English proof (translation)
Simplify using `[quotMap, orthLift, fromCols_mul_fromRows]`.
-/
theorem quotMap_mul_orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : quotMap m l * orthLift H = 1 := by
  simp [quotMap, orthLift, fromCols_mul_fromRows]

/- English proof (translation)
Rewrite using `[quotMap, orthLift, incl, orthProj, fromRows_mul_fromCols, fromRows_mul_fromCols, fromBlocks_add, ← fromBlocks_one]`. Simplify using the standard rewrite rules.
-/
theorem incl_mul_orthProj_add (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    incl m l * orthProj H + orthLift H * quotMap m l = 1 := by
  rw [quotMap, orthLift, incl, orthProj, fromRows_mul_fromCols, fromRows_mul_fromCols,
    fromBlocks_add, ← fromBlocks_one]
  simp

/- English proof (translation)
Rewrite using `[form_mulVec, form]`. Use `congr 2`. Use `conv_lhs => rw [← fromBlocks_toBlocks H]`. Simplify using `[incl, subGram, transpose_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows]`.
-/
theorem form_incl (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (u u' : m → ℂ) :
    form H (incl m l *ᵥ u) (incl m l *ᵥ u') = form (subGram H) u u' := by
  rw [form_mulVec, form]
  congr 2
  conv_lhs => rw [← fromBlocks_toBlocks H]
  simp [incl, subGram, transpose_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

/- English proof (translation)
Establish `h : (orthLift H)ᵀ = fromCols (-(H.toBlocks₂₁ * H.toBlocks₁₁⁻¹)) 1`. Simplify using `[orthLift, orthCoeff, transpose_fromRows, transpose_nonsing_inv]`. Rewrite using `[h]`. Use `conv_lhs => rhs`. Rewrite using `[← fromBlocks_toBlocks H]`.

Rewrite using `[fromCols_mul_fromBlocks]`. Use `congr 1`. Rewrite using `[Matrix.neg_mul, nonsing_inv_mul_cancel_right H.toBlocks₁₁ _ hu]`. Simplify using the standard rewrite rules. Rewrite using `[quotGram]`.

Simplify using `[sub_eq_neg_add]`.
-/
theorem orthLift_transpose_mul (hu : IsUnit (subGram H).det) :
    (orthLift H)ᵀ * H = fromCols 0 (quotGram H) := by
  have h : (orthLift H)ᵀ = fromCols (-(H.toBlocks₂₁ * H.toBlocks₁₁⁻¹)) 1 := by
    simp [orthLift, orthCoeff, transpose_fromRows, transpose_nonsing_inv]
  rw [h]
  conv_lhs => rhs; rw [← fromBlocks_toBlocks H]
  rw [fromCols_mul_fromBlocks]
  congr 1
  · rw [Matrix.neg_mul, nonsing_inv_mul_cancel_right H.toBlocks₁₁ _ hu]; simp
  · rw [quotGram]; simp [sub_eq_neg_add]

/- English proof (translation)
Rewrite using `[form_mulVec, orthLift_transpose_mul hu]`. Simplify using `[incl, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols, fromCols_mul_fromRows]`.
-/
theorem form_orthLift_incl (hu : IsUnit (subGram H).det) (q : l → ℂ) (u : m → ℂ) :
    form H (orthLift H *ᵥ q) (incl m l *ᵥ u) = 0 := by
  rw [form_mulVec, orthLift_transpose_mul hu]
  simp [incl, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    fromCols_mul_fromRows]

/- English proof (translation)
Rewrite using `[form_mulVec, orthLift_transpose_mul hu, form]`. Simplify using `[orthLift, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols, fromCols_mul_fromRows]`.
-/
theorem form_orthLift (hu : IsUnit (subGram H).det) (q q' : l → ℂ) :
    form H (orthLift H *ᵥ q) (orthLift H *ᵥ q') = form (quotGram H) q q' := by
  rw [form_mulVec, orthLift_transpose_mul hu, form]
  simp [orthLift, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    fromCols_mul_fromRows]

/- English proof (translation)
Use `letI : Invertible H.toBlocks₁₁ := invertibleOfIsUnitDet _ hu`. Use `conv_lhs => rw [← fromBlocks_toBlocks H]`. Rewrite using `[det_fromBlocks₁₁, invOf_eq_nonsing_inv]`. Both sides reduce to the same expression.
-/
theorem det_eq_det_subGram_mul (hu : IsUnit (subGram H).det) :
    H.det = (subGram H).det * (quotGram H).det := by
  letI : Invertible H.toBlocks₁₁ := invertibleOfIsUnitDet _ hu
  conv_lhs => rw [← fromBlocks_toBlocks H]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]; rfl

/- English proof (translation)
The claim follows from `isUnit_of_mul_isUnit_right (det_eq_det_subGram_mul hu ▸ h)`.
-/
theorem isUnit_det_quotGram (h : IsUnit H.det) (hu : IsUnit (subGram H).det) :
    IsUnit (quotGram H).det := isUnit_of_mul_isUnit_right (det_eq_det_subGram_mul hu ▸ h)

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] in

/- English proof (translation)
The claim follows from `h.submatrix Sum.inl`.
-/
theorem isHermitian_subGram (h : H.IsHermitian) : (subGram H).IsHermitian := h.submatrix Sum.inl

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] in

/- English proof (translation)
Use extensionality with `i j`. Conclude with `h.apply _ _`.
-/
theorem conjTranspose_toBlocks₁₂ (h : H.IsHermitian) : H.toBlocks₁₂ᴴ = H.toBlocks₂₁ := by
  ext i j; exact h.apply _ _

omit [Fintype l] [DecidableEq l] in

/- English proof (translation)
Establish `h1 : H.toBlocks₁₁.IsHermitian` using `isHermitian_subGram h`. Establish `h2 : H.toBlocks₂₂.IsHermitian` using `h.submatrix Sum.inr`. Rewrite using `[quotGram, ← conjTranspose_toBlocks₁₂ h]`. Use `h2.sub ?_` and prove the remaining obligations. Rewrite using `[IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h1.inv.eq, Matrix.mul_assoc]`.
-/
theorem isHermitian_quotGram (h : H.IsHermitian) : (quotGram H).IsHermitian := by
  have h1 : H.toBlocks₁₁.IsHermitian := isHermitian_subGram h
  have h2 : H.toBlocks₂₂.IsHermitian := h.submatrix Sum.inr
  rw [quotGram, ← conjTranspose_toBlocks₁₂ h]
  refine h2.sub ?_
  rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h1.inv.eq,
    Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq l] in

/- English proof (translation)
The claim follows from `h.submatrix Sum.inl_injective`.
-/
theorem posDef_subGram (h : H.PosDef) : (subGram H).PosDef :=
  h.submatrix Sum.inl_injective

/- English proof (translation)
Establish `hu : IsUnit (subGram H).det` using `(isUnit_iff_isUnit_det _).1 (posDef_subGram h).isUnit`. Use `posDef_iff.2 ⟨isHermitian_quotGram h.isHermitian, fun q hq => ?_⟩` and prove the remaining obligations. Rewrite using `[← form_orthLift hu]`. Use `(posDef_iff.1 h).2 _ fun h0 => hq ?_` and prove the remaining obligations. Rewrite using `[← one_mulVec q, ← quotMap_mul_orthLift H, ← mulVec_mulVec, h0, mulVec_zero]`.
-/
theorem posDef_quotGram (h : H.PosDef) : (quotGram H).PosDef := by
  have hu : IsUnit (subGram H).det := (isUnit_iff_isUnit_det _).1 (posDef_subGram h).isUnit
  refine posDef_iff.2 ⟨isHermitian_quotGram h.isHermitian, fun q hq => ?_⟩
  rw [← form_orthLift hu]
  refine (posDef_iff.1 h).2 _ fun h0 => hq ?_
  rw [← one_mulVec q, ← quotMap_mul_orthLift H, ← mulVec_mulVec, h0, mulVec_zero]

end Blocks

section FinFrame

variable {N : ℕ}

def splitFin {k : ℕ} (hk : k ≤ N) : Fin k ⊕ Fin (N - k) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

def adapt {k : ℕ} (hk : k ≤ N) (T : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin k ⊕ Fin (N - k)) (Fin k ⊕ Fin (N - k)) ℂ :=
  T.submatrix (splitFin hk) (splitFin hk)

def firstGram {k : ℕ} (hk : k ≤ N) (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  H.submatrix (Fin.castLE hk) (Fin.castLE hk)

def lastGram {k : ℕ} (hk : k ≤ N) (H : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin (N - k)) (Fin (N - k)) ℂ := quotGram (adapt hk H)

def stepGram (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Matrix (Fin i ⊕ Unit) (Fin i ⊕ Unit) ℂ :=
  H.submatrix (Sum.elim (Fin.castLE i.2.le) fun _ => i) (Sum.elim (Fin.castLE i.2.le) fun _ => i)

def gradedGram (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : Matrix Unit Unit ℂ :=
  quotGram (stepGram H i)

/- English proof (translation)
Establish `h` using `det_eq_det_subGram_mul (H := stepGram H i) hu`. Rewrite `h` using `[det_unique (quotGram _)]`. Rewrite using `[← det_submatrix_equiv_self ((Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv)]`. Use `Eq.trans ?_ h` and prove the remaining obligations. Use `congr 1`.

Apply the tactic sequence `ext (a | a) (b | b) <;> rfl`.
-/
theorem det_firstGram_succ (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hu : IsUnit (firstGram i.2.le H).det) :
    (firstGram (k := i + 1) i.2 H).det = (firstGram i.2.le H).det * gradedGram H i () () := by
  have h := det_eq_det_subGram_mul (H := stepGram H i) hu
  rw [det_unique (quotGram _)] at h
  rw [← det_submatrix_equiv_self
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv)]
  refine Eq.trans ?_ h
  congr 1
  ext (a | a) (b | b) <;> rfl

/- English proof (translation)
Use `posDef_quotGram (h.submatrix ?_)` and prove the remaining obligations. Introduce and unpack `(a | a) (b | b) hab`. Conclude with `congrArg _ (Fin.castLE_injective i.2.le hab)`. Conclude with `absurd (congrArg Fin.val hab) a.2.ne`. Conclude with `absurd (congrArg Fin.val hab) b.2.ne'`.

Both sides reduce to the same expression.
-/
theorem posDef_gradedGram {H : Matrix (Fin N) (Fin N) ℂ} (h : H.PosDef) (i : Fin N) :
    (gradedGram H i).PosDef := by
  refine posDef_quotGram (h.submatrix ?_)
  rintro (a | a) (b | b) hab
  · exact congrArg _ (Fin.castLE_injective i.2.le hab)
  · exact absurd (congrArg Fin.val hab) a.2.ne
  · exact absurd (congrArg Fin.val hab) b.2.ne'
  · rfl

end FinFrame

/- English proof (translation)
Simplify using `[form_eq_sum]`.
-/
example : form (1 : Matrix Unit Unit ℂ) (fun _ => I) (fun _ => 1) = I := by simp [form_eq_sum]

/- English proof (translation)
Simplify using `[quotGram, mul_apply]`. Evaluate the numerical expressions.
-/
example : quotGram (fromBlocks (1 : Matrix Unit Unit ℂ) (of fun _ _ => I) (of fun _ _ => -I)
    (of fun _ _ => 3) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) () () = 2 := by
  simp [quotGram, mul_apply]; norm_num

/- English proof (translation)
Establish `h : ∀ v : Unit → ℂ, gnorm 1 (((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) *ᵥ v) = 2 * gnorm 1 v` using `fun v => by rw [smul_mulVec, one_mulVec, gnorm_smul PosSemidef.one]; simp`. Simplify using `only [opNorm_le_iff PosDef.one PosSemidef.one, h]`. Use `⟨⟨by norm_num, fun v => le_rfl⟩, fun h' => ?_⟩` and prove the remaining obligations. Use `gnorm_pos (H := (1 : Matrix Unit Unit ℂ)) PosDef.one (v := fun _ => 1) (fun h0 => one_ne_zero (congrFun h0 ()))` as an intermediate fact. Combine the linear relations using `[h'.2 fun _ => 1]`.
-/
example : opNorm (1 : Matrix Unit Unit ℂ) 1 ((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) ≤ 2 ∧
    ¬ opNorm (1 : Matrix Unit Unit ℂ) 1 ((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) ≤ 1 := by
  have h : ∀ v : Unit → ℂ, gnorm 1 (((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) *ᵥ v) = 2 * gnorm 1 v :=
    fun v => by rw [smul_mulVec, one_mulVec, gnorm_smul PosSemidef.one]; simp
  simp only [opNorm_le_iff PosDef.one PosSemidef.one, h]
  refine ⟨⟨by norm_num, fun v => le_rfl⟩, fun h' => ?_⟩
  have := gnorm_pos (H := (1 : Matrix Unit Unit ℂ)) PosDef.one (v := fun _ => 1)
    (fun h0 => one_ne_zero (congrFun h0 ()))
  linarith [h'.2 fun _ => 1]

end GlobalTheory.HermFrame
