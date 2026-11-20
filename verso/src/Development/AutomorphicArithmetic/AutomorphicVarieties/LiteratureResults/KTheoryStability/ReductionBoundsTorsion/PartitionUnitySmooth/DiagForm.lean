import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hadam

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm

/- English proof (translation)
Establish `hH` using `hh.1`. Establish `key` using `hH.conjStarAlgAut_star_eigenvectorUnitary`. Rewrite `key` using `[Unitary.conjStarAlgAut_apply]`. Simplify using `only [Unitary.coe_star, star_star, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose] at key`. Establish `hpos` using `hh.eigenvalues_pos`.

Use `⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal (fun i => ((Real.sqrt (hH.eigenvalues i))⁻¹ : ℂ)), ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, diagonal_conjTranspose]`. Establish `e : ∀ (D E V : Matrix (Fin N) (Fin N) ℂ), (D * Vᴴ * h * (V * E)) = D * (Vᴴ * h * V) * E`. Introduce `D E V`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[e, key, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hi` using `hpos i`. Establish `hs : (0:ℝ) < Real.sqrt (hH.eigenvalues i)` using `Real.sqrt_pos.mpr hi`.

Establish `hsq : Real.sqrt (hH.eigenvalues i) * Real.sqrt (hH.eigenvalues i) = hH.eigenvalues i` using `Real.mul_self_sqrt hi.le`. Simplify using `only [Pi.star_apply, Function.comp_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]`. Establish `hr : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1`. Establish `hs2 : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i` using `Real.sq_sqrt hi.le`. Clear the denominators using the available nonvanishing facts.

Combine the linear relations using `[hs2, hsq]`. Establish `hc` using `congrArg (fun x : ℝ => (x : ℂ)) hr`. Simplify using `using hc`.
-/
theorem exT {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (hh : h.PosDef) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, Tᴴ * h * T = 1 := by
  have hH := hh.1
  have key := hH.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at key
  simp only [Unitary.coe_star, star_star, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose] at key
  have hpos := hh.eigenvalues_pos
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal (fun i => ((Real.sqrt (hH.eigenvalues i))⁻¹ : ℂ)), ?_⟩
  rw [conjTranspose_mul, diagonal_conjTranspose]
  have e : ∀ (D E V : Matrix (Fin N) (Fin N) ℂ), (D * Vᴴ * h * (V * E)) = D * (Vᴴ * h * V) * E := by
    intro D E V
    simp only [Matrix.mul_assoc]
  rw [e, key, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have hi := hpos i
  have hs : (0:ℝ) < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.mpr hi
  have hsq : Real.sqrt (hH.eigenvalues i) * Real.sqrt (hH.eigenvalues i) = hH.eigenvalues i := Real.mul_self_sqrt hi.le
  simp only [Pi.star_apply, Function.comp_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hr : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    have hs2 : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt hi.le
    field_simp
    linarith [hs2, hsq]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

/- English proof (translation)
Simplify using `only [mul_apply, dotProduct, mulVec, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_form {N : ℕ} (A M : Matrix (Fin N) (Fin N) ℂ) (a : Fin N) :
    (Aᴴ * M * A) a a = star (fun i => A i a) ⬝ᵥ (M *ᵥ fun i => A i a) := by
  simp only [mul_apply, dotProduct, mulVec, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Take `⟨T, hT⟩` from `exT h hh`. Establish `quad : ∀ (B M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ), star v ⬝ᵥ (Bᴴ * M * B) *ᵥ v = star (B *ᵥ v) ⬝ᵥ M *ᵥ (B *ᵥ v)`. Introduce `B M v`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Establish `hk' : (Tᴴ * k * T).PosSemidef` using `hk.conjTranspose_mul_mul_same T`.

Establish `hev : ∀ i, hk'.1.eigenvalues i ≤ c`. Introduce `i`. Rewrite using `[hk'.1.eigenvalues_eq]`. Establish `hv` using `hle (T *ᵥ (hk'.1.eigenvectorBasis i).ofLp)`. Rewrite `hv` using `[← quad T k, ← quad T h, hT, one_mulVec]`.

Establish `hn : star (hk'.1.eigenvectorBasis i).ofLp ⬝ᵥ (hk'.1.eigenvectorBasis i).ofLp = 1`. Use `(hk'.1.eigenvectorBasis).orthonormal.1 i` as an intermediate fact. Rewrite using `[dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, this]`. Simplify using the standard rewrite rules. Rewrite `hv` using `[hn]`.

Simplify using `using hv`. Establish `hprod : (Tᴴ * k * T).det.re ≤ c ^ N`. Rewrite using `[hk'.1.det_eq_prod_eigenvalues]`. Use `erw [← Complex.ofReal_prod, Complex.ofReal_re]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e : ∀ X : ℂ, star T.det * X * T.det = (Complex.normSq T.det : ℂ) * X`. Introduce `X`. Rewrite using `[← Complex.mul_conj, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd1` using `congrArg Matrix.det hT`.

Rewrite `hd1` using `[det_mul, det_mul, det_conjTranspose, det_one, e]`. Rewrite `hprod` using `[det_mul, det_mul, det_conjTranspose, e, Complex.re_ofReal_mul]`. Establish `hre` using `congrArg Complex.re hd1`. Rewrite `hre` using `[Complex.re_ofReal_mul, Complex.one_re]`. Establish `hnd : 0 < Complex.normSq T.det`.

Use `lt_of_le_of_ne (Complex.normSq_nonneg _) fun h0 => ?_` and prove the remaining obligations. Rewrite `hre` using `[← h0, zero_mul]`. Conclude with `zero_ne_one hre`. Use `le_of_mul_le_mul_left ?_ hnd` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_left_comm, hre, mul_one]`.
-/
theorem detMono {N : ℕ} (h k : Matrix (Fin N) (Fin N) ℂ) (hh : h.PosDef) (hk : k.PosSemidef) (c : ℝ)
    (hc : 0 < c) (hle : ∀ x : Fin N → ℂ, (star x ⬝ᵥ (k *ᵥ x)).re ≤ c * (star x ⬝ᵥ (h *ᵥ x)).re) :
    k.det.re ≤ c ^ N * h.det.re := by
  obtain ⟨T, hT⟩ := exT h hh
  have quad : ∀ (B M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ),
      star v ⬝ᵥ (Bᴴ * M * B) *ᵥ v = star (B *ᵥ v) ⬝ᵥ M *ᵥ (B *ᵥ v) := by
    intro B M v
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hk' : (Tᴴ * k * T).PosSemidef := hk.conjTranspose_mul_mul_same T
  have hev : ∀ i, hk'.1.eigenvalues i ≤ c := by
    intro i
    rw [hk'.1.eigenvalues_eq]
    have hv := hle (T *ᵥ (hk'.1.eigenvectorBasis i).ofLp)
    rw [← quad T k, ← quad T h, hT, one_mulVec] at hv
    have hn : star (hk'.1.eigenvectorBasis i).ofLp ⬝ᵥ (hk'.1.eigenvectorBasis i).ofLp = 1 := by
      have := (hk'.1.eigenvectorBasis).orthonormal.1 i
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, this]
      simp
    rw [hn] at hv
    simpa using hv
  have hprod : (Tᴴ * k * T).det.re ≤ c ^ N := by
    rw [hk'.1.det_eq_prod_eigenvalues]
    erw [← Complex.ofReal_prod, Complex.ofReal_re]
    calc ∏ i, hk'.1.eigenvalues i ≤ ∏ _i : Fin N, c :=
          Finset.prod_le_prod (fun i _ => hk'.eigenvalues_nonneg i) (fun i _ => hev i)
      _ = c ^ N := by simp
  have e : ∀ X : ℂ, star T.det * X * T.det = (Complex.normSq T.det : ℂ) * X := by
    intro X
    rw [← Complex.mul_conj, Complex.star_def]
    ring
  have hd1 := congrArg Matrix.det hT
  rw [det_mul, det_mul, det_conjTranspose, det_one, e] at hd1
  rw [det_mul, det_mul, det_conjTranspose, e, Complex.re_ofReal_mul] at hprod
  have hre := congrArg Complex.re hd1
  rw [Complex.re_ofReal_mul, Complex.one_re] at hre
  have hnd : 0 < Complex.normSq T.det := by
    refine lt_of_le_of_ne (Complex.normSq_nonneg _) fun h0 => ?_
    rw [← h0, zero_mul] at hre
    exact zero_ne_one hre
  refine le_of_mul_le_mul_left ?_ hnd
  calc Complex.normSq T.det * k.det.re ≤ c ^ N := hprod
    _ = Complex.normSq T.det * (c ^ N * h.det.re) := by
      rw [mul_left_comm, hre, mul_one]

/- English proof (translation)
The claim follows from `|Ak⁻¹ * K - Ah⁻¹ * H| ≤ 3 * δ * (Ah⁻¹ * H) := by have hAk : 0 < Ak := by nlinarith have e : Ak⁻¹ * K - Ah⁻¹ * H = (Ah * (K - H) + H * (Ah - Ak)) / (Ak * Ah) := by field_simp ring have e2 : 3 * δ * (Ah⁻¹ * H) = 3 * δ * H * Ak / (Ak * Ah) := by field_simp rw [e, e2, abs_div, abs_of …`.
-/
theorem lipAlg (δ Ah Ak H K : ℝ) (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4) (hAh : 0 < Ah) (h1 : (1 - δ) * Ah ≤ Ak)
    (h2 : Ak ≤ (1 + δ) * Ah) (hH : 0 ≤ H) (hK : |K - H| ≤ δ * H) :
    |Ak⁻¹ * K - Ah⁻¹ * H| ≤ 3 * δ * (Ah⁻¹ * H) := by
  have hAk : 0 < Ak := by nlinarith
  have e : Ak⁻¹ * K - Ah⁻¹ * H = (Ah * (K - H) + H * (Ah - Ak)) / (Ak * Ah) := by
    field_simp
    ring
  have e2 : 3 * δ * (Ah⁻¹ * H) = 3 * δ * H * Ak / (Ak * Ah) := by
    field_simp
  rw [e, e2, abs_div, abs_of_pos (mul_pos hAk hAh)]
  apply div_le_div_of_nonneg_right _ (mul_pos hAk hAh).le
  have hd : |Ah - Ak| ≤ δ * Ah := by
    rw [abs_le]
    constructor <;> nlinarith
  have h3 : 0 ≤ 3 * Ak - 2 * Ah := by nlinarith
  calc |Ah * (K - H) + H * (Ah - Ak)| ≤ |Ah * (K - H)| + |H * (Ah - Ak)| := abs_add_le _ _
    _ = Ah * |K - H| + H * |Ah - Ak| := by rw [abs_mul, abs_mul, abs_of_pos hAh, abs_of_nonneg hH]
    _ ≤ Ah * (δ * H) + H * (δ * Ah) := by gcongr
    _ ≤ 3 * δ * H * Ak := by nlinarith [mul_nonneg (mul_nonneg hδ hH) h3]

end PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm
