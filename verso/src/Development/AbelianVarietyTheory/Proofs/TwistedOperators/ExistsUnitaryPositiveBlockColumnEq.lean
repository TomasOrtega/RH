import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.Twist.Boost

/- English proof (translation)
Simplify using `only [conjTranspose_add, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec, star_star, hcs, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, v …`. Establish `hs2 : star (2 : ℂ) = 2` using `by simp`. Rewrite using `[hs2]`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]`.

Take the linear combination `(2 * c * ((e i + v i) * (star (e j) + star (v j))) - 2 * ((e i + v i) * star (e j)) - 2 * (e i * (star (e j) + star (v j)))) * hc`.
-/
theorem reflectionBoost_matrix_conjTranspose_mul_self {n : ℕ} (e v : Fin n → ℂ) (t c : ℂ) (hee : star e ⬝ᵥ e = 1) (hvv : star v ⬝ᵥ v = 1)
    (hev : star e ⬝ᵥ v = t) (hve : star v ⬝ᵥ e = t) (hc : c * (1 + t) = 1) (hcs : star c = c) :
    (1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e))ᴴ *
      (1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e)) = 1 := by
  simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec,
    star_star, hcs, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul, star_add, add_dotProduct, dotProduct_add,
    hee, hvv, hev, hve]
  have hs2 : star (2 : ℂ) = 2 := by simp
  rw [hs2]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
  linear_combination (2 * c * ((e i + v i) * (star (e j) + star (v j))) - 2 * ((e i + v i) * star (e j)) - 2 * (e i * (star (e j) + star (v j)))) * hc

/- English proof (translation)
Use `set t : ℝ := ‖u z‖ with ht`. Establish `t0 : 0 ≤ t` using `norm_nonneg _`. Use `set φ : ℂ := if u z = 0 then 1 else u z / (t : ℂ) with hφdef`. Establish `hφ : star φ * φ = 1`. Distinguish the cases in `h : u z = 0`.

Simplify using `[hφdef, h]`. Establish `htn : (t : ℂ) ≠ 0` using `by simp [ht, h]`. Simplify using `only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[div_mul_div_comm, Complex.conj_mul', ← ht]`. Clear the denominators using the available nonvanishing facts.

Establish `hφt : star φ * u z = (t : ℂ)`. Distinguish the cases in `h : u z = 0`. Simplify using `[hφdef, h, ht]`. Establish `htn : (t : ℂ) ≠ 0` using `by simp [ht, h]`. Simplify using `only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]`.

Rewrite using `[div_mul_eq_mul_div, Complex.conj_mul', ← ht]`. Clear the denominators using the available nonvanishing facts. Establish `hφ' : (starRingEnd ℂ) φ * φ = 1` using `by rw [← Complex.star_def]; exact hφ`. Establish `hφt' : (starRingEnd ℂ) φ * u z = (t : ℂ)` using `by rw [← Complex.star_def]; exact hφt`. Use `set e : Fin m → ℂ := Pi.single z 1 with he`.

Use `set v : Fin m → ℂ := fun i => star φ * u i with hv`. Establish `hee : star e ⬝ᵥ e = 1` using `by simp [he, dotProduct, Pi.single_apply]`. Establish `hvv : star v ⬝ᵥ v = 1`. Establish `: ∀ i, star (v i) * v i = ((‖u i‖ ^ 2 : ℝ) : ℂ)`. Introduce `i`.

Simplify using `only [hv, star_mul, star_star]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [dotProduct, Pi.star_apply, this]`. Rewrite using `[← Complex.ofReal_sum, hn]`. Simplify using the standard rewrite rules.

Establish `hev : star e ⬝ᵥ v = (t : ℂ)`. Simplify using `[he, dotProduct, Pi.single_apply, hv, hφt, hφt']`. Establish `hve : star v ⬝ᵥ e = (t : ℂ)`. Simplify using `only [he, dotProduct, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [hv]`.

Rewrite using `[hφt]`. Simplify using the standard rewrite rules. Use `set c : ℂ := ((1 / (1 + t) : ℝ) : ℂ) with hcdef`. Establish `hc : c * (1 + (t : ℂ)) = 1`. Establish `: (1 + t) ≠ 0` using `by positivity`.

Establish `h2 : (1 + (t : ℂ)) ≠ 0` using `by exact_mod_cast this`. Simplify using `only [hcdef]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hcs : star c = c` using `by simp [hcdef]`.

Use `set T : Matrix (Fin m) (Fin m) ℂ := 1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e) with hT`. Establish `hTu : Tᴴ * T = 1` using `reflectionBoost_matrix_conjTranspose_mul_self e v t c hee hvv hev hve hc hcs`. Use `set d : Fin m → ℂ := fun i => if i = z then φ else 1 with hd`. Use `set k : Matrix (Fin m) (Fin m) ℂ := T * diagonal d with hk`. Establish `hdd : (diagonal d)ᴴ * diagonal d = 1`.

Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = z`. Simplify using `[hd, h, hφ, hφ']`.

Simplify using `[hd, h]`. Establish `hku : kᴴ * k = 1`. Rewrite using `[hk, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ, hTu, Matrix.one_mul, hdd]`. Establish `hTe : ∀ i j, T i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j - c * ((e i + v i) * star (e j + v j)) + 2 * (v i * star (e j))`. Introduce `i j`.

Simplify using `[hT, vecMulVec_apply]`. Establish `hvneg : ∀ i, ε i = false → v i = 0` using `fun i hi => by simp [hv, hneg i hi]`. Establish `heneg : ∀ i, ε i = false → e i = 0` using `fun i hi => by`. Establish `: i ≠ z` using `by rintro rfl; simp [hz] at hi`. Simplify using `[he, Pi.single_apply, this]`.

Establish `hT0 : ∀ i j, ε i ≠ ε j → T i j = 0`. Introduce `i j hij`. Establish `hne : i ≠ j` using `by rintro rfl; exact hij rfl`. Rewrite using `[hTe, one_apply_ne hne]`. Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j`.

Simplify using `[hi, hj] at hij`. Simplify using `[hvneg i hi, heneg i hi]`. Simplify using `[hvneg j hj, heneg j hj]`. Simplify using `[hi, hj] at hij`. Establish `hcomm : Jm ε * k = k * Jm ε`.

Use extensionality with `i j`. Simplify using `only [hk, Jm, diagonal_mul, mul_diagonal]`. Distinguish the cases in `hij : ε i = ε j`. Rewrite using `[hij]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hT0 i j hij]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨k, ?_, hku, ?_⟩` and prove the remaining obligations. Use `show Formalism.REAL.inUJ ε k`. Unfold `Formalism.REAL.inUJ`.

Rewrite using `[Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hku, Matrix.one_mul]`. Introduce `i`. Establish `hez : e z = 1` using `by simp [he]`. Establish `hvz : v z = (t : ℂ)` using `by simp [hv, hφt, hφt']`. Establish `hTz : T i z = v i`.

Rewrite using `[hTe, hez, hvz]`. Rewrite using `[show star ((1 : ℂ) + (t : ℂ)) = 1 + (t : ℂ) by simp, star_one, mul_one]`. Establish `: c * ((e i + v i) * (1 + (t : ℂ))) = e i + v i` using `by rw [mul_comm (e i + v i), ← mul_assoc, hc, one_mul]`. Rewrite using `[this]`. Distinguish the cases in `h : i = z`.

Substitute `h` using the available equality. Simplify using `[he]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[he, Pi.single_apply, h, one_apply_ne h]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hk, mul_diagonal, hTz, hd, if_true, hv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_unitary_col (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ) (hz : ε z = true)
    (hneg : ∀ i, ε i = false → u i = 0) (hn : ∑ i, ‖u i‖ ^ 2 = 1) :
    ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := by
  set t : ℝ := ‖u z‖ with ht
  have t0 : 0 ≤ t := norm_nonneg _
  set φ : ℂ := if u z = 0 then 1 else u z / (t : ℂ) with hφdef
  have hφ : star φ * φ = 1 := by
    by_cases h : u z = 0
    · simp [hφdef, h]
    · have htn : (t : ℂ) ≠ 0 := by simp [ht, h]
      simp only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_div_comm, Complex.conj_mul', ← ht]
      field_simp
  have hφt : star φ * u z = (t : ℂ) := by
    by_cases h : u z = 0
    · simp [hφdef, h, ht]
    · have htn : (t : ℂ) ≠ 0 := by simp [ht, h]
      simp only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_eq_mul_div, Complex.conj_mul', ← ht]
      field_simp
  have hφ' : (starRingEnd ℂ) φ * φ = 1 := by rw [← Complex.star_def]; exact hφ
  have hφt' : (starRingEnd ℂ) φ * u z = (t : ℂ) := by rw [← Complex.star_def]; exact hφt
  set e : Fin m → ℂ := Pi.single z 1 with he
  set v : Fin m → ℂ := fun i => star φ * u i with hv
  have hee : star e ⬝ᵥ e = 1 := by simp [he, dotProduct, Pi.single_apply]
  have hvv : star v ⬝ᵥ v = 1 := by
    have : ∀ i, star (v i) * v i = ((‖u i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      simp only [hv, star_mul, star_star]
      calc star (u i) * φ * (star φ * u i) = (star φ * φ) * (star (u i) * u i) := by ring
        _ = _ := by rw [hφ, one_mul, Complex.star_def, Complex.conj_mul']; push_cast; ring
    simp only [dotProduct, Pi.star_apply, this]
    rw [← Complex.ofReal_sum, hn]; simp
  have hev : star e ⬝ᵥ v = (t : ℂ) := by
    simp [he, dotProduct, Pi.single_apply, hv, hφt, hφt']
  have hve : star v ⬝ᵥ e = (t : ℂ) := by
    simp only [he, dotProduct, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hv]
    rw [hφt]; simp
  set c : ℂ := ((1 / (1 + t) : ℝ) : ℂ) with hcdef
  have hc : c * (1 + (t : ℂ)) = 1 := by
    have : (1 + t) ≠ 0 := by positivity
    have h2 : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast this
    simp only [hcdef]; push_cast; field_simp
  have hcs : star c = c := by simp [hcdef]
  set T : Matrix (Fin m) (Fin m) ℂ := 1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e) with hT
  have hTu : Tᴴ * T = 1 := reflectionBoost_matrix_conjTranspose_mul_self e v t c hee hvv hev hve hc hcs
  set d : Fin m → ℂ := fun i => if i = z then φ else 1 with hd
  set k : Matrix (Fin m) (Fin m) ℂ := T * diagonal d with hk
  have hdd : (diagonal d)ᴴ * diagonal d = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    by_cases h : i = z
    · simp [hd, h, hφ, hφ']
    · simp [hd, h]
  have hku : kᴴ * k = 1 := by
    rw [hk, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ, hTu, Matrix.one_mul, hdd]
  have hTe : ∀ i j, T i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j - c * ((e i + v i) * star (e j + v j)) + 2 * (v i * star (e j)) := by
    intro i j; simp [hT, vecMulVec_apply]
  have hvneg : ∀ i, ε i = false → v i = 0 := fun i hi => by simp [hv, hneg i hi]
  have heneg : ∀ i, ε i = false → e i = 0 := fun i hi => by
    have : i ≠ z := by rintro rfl; simp [hz] at hi
    simp [he, Pi.single_apply, this]
  have hT0 : ∀ i j, ε i ≠ ε j → T i j = 0 := by
    intro i j hij
    have hne : i ≠ j := by rintro rfl; exact hij rfl
    rw [hTe, one_apply_ne hne]
    cases hi : ε i <;> cases hj : ε j
    · simp [hi, hj] at hij
    · simp [hvneg i hi, heneg i hi]
    · simp [hvneg j hj, heneg j hj]
    · simp [hi, hj] at hij
  have hcomm : Jm ε * k = k * Jm ε := by
    ext i j
    simp only [hk, Jm, diagonal_mul, mul_diagonal]
    by_cases hij : ε i = ε j
    · rw [hij]; ring
    · rw [hT0 i j hij]; ring
  refine ⟨k, ?_, hku, ?_⟩
  · show Formalism.REAL.inUJ ε k
    unfold Formalism.REAL.inUJ
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hku, Matrix.one_mul]
  · intro i
    have hez : e z = 1 := by simp [he]
    have hvz : v z = (t : ℂ) := by simp [hv, hφt, hφt']
    have hTz : T i z = v i := by
      rw [hTe, hez, hvz]
      rw [show star ((1 : ℂ) + (t : ℂ)) = 1 + (t : ℂ) by simp, star_one, mul_one]
      have : c * ((e i + v i) * (1 + (t : ℂ))) = e i + v i := by rw [mul_comm (e i + v i), ← mul_assoc, hc, one_mul]
      rw [this]
      by_cases h : i = z
      · subst h; simp [he]; ring
      · simp [he, Pi.single_apply, h, one_apply_ne h]; ring
    simp only [hk, mul_diagonal, hTz, hd, if_true, hv]
    calc star φ * u i * φ = (star φ * φ) * u i := by ring
      _ = u i := by rw [hφ, one_mul]

end GlobalTheory.Twist.Boost

end
