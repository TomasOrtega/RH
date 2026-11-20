import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.SettingConstruction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Rewrite using `[Measure.smul_apply, h.conc, smul_zero]`. Use `left := fun a ha => by rw [Measure.map_smul, h.left a ha]`. Use `right := fun a ha => by rw [Measure.map_smul, h.right a ha]`. Use `finite_compact := fun K hK => by`. Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`.

Conclude with `ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)`. Use `ne_zero := by`. Introduce `h0`. Apply `h.ne_zero` to reduce the goal to its premises. Establish `h1 : (c • μ) Set.univ = 0` using `by rw [h0]; rfl`.

Rewrite `h1` using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `absurd (by exact_mod_cast h2 : c = 0) hc.ne'`. Conclude with `Measure.measure_univ_eq_zero.mp h2`.
-/
theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) where
  conc := by
    rw [Measure.smul_apply, h.conc, smul_zero]
  left := fun a ha => by rw [Measure.map_smul, h.left a ha]
  right := fun a ha => by rw [Measure.map_smul, h.right a ha]
  finite_compact := fun K hK => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2

section forms
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_add, dotProduct_add]`.
-/
lemma herm_add_left (u u' w : ι → ℂ) : herm H (u + u') w = herm H u w + herm H u' w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_sub, dotProduct_sub]`.
-/
lemma herm_sub_left (u u' w : ι → ℂ) : herm H (u - u') w = herm H u w - herm H u' w := by
  simp [herm, Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_smul, dotProduct_smul]`.
-/
lemma herm_smul_left (c : ℂ) (u w : ι → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[herm, add_dotProduct]`.
-/
lemma herm_add_right (u w w' : ι → ℂ) : herm H u (w + w') = herm H u w + herm H u w' := by
  simp [herm, add_dotProduct]

/- English proof (translation)
Simplify using `[herm, sub_dotProduct]`.
-/
lemma herm_sub_right (u w w' : ι → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by
  simp [herm, sub_dotProduct]

/- English proof (translation)
Simplify using `[herm, smul_dotProduct]`.
-/
lemma herm_smul_right (c : ℂ) (u w : ι → ℂ) : herm H u (c • w) = star c * herm H u w := by
  simp [herm, smul_dotProduct]

/- English proof (translation)
Simplify using `only [herm]`. Rewrite using `[Matrix.star_dotProduct, star_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]`.
-/
lemma herm_symm (hH : Hᴴ = H) (u w : ι → ℂ) : star (herm H u w) = herm H w u := by
  simp only [herm]
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]

/- English proof (translation)
Simplify using `only [herm]`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
lemma herm_mulVec (g : Matrix ι ι ℂ) (x y : ι → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm (gᴴ * H * g) x y := by
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

variable [DecidableEq ι]

/- English proof (translation)
Simplify using `[herm, dotProduct, Matrix.mulVec, Pi.single_apply]`.
-/
lemma herm_single (i j : ι) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  simp [herm, dotProduct, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i j`. Use `h (Pi.single j 1) (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[herm_mulVec, herm_single, herm_single]`. Then use the resulting hypothesis.
-/
lemma unitary_of_form (g : Matrix ι ι ℂ) (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : gᴴ * H * g = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rwa [herm_mulVec, herm_single, herm_single] at this

/- English proof (translation)
Rewrite using `[herm_mulVec, h]`.
-/
lemma form_of_unitary {g : Matrix ι ι ℂ} (h : gᴴ * H * g = H) (x y : ι → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  rw [herm_mulVec, h]

def rk (d : ι → ℂ) (θ β : ℂ) : Matrix ι ι ℂ := θ • (1 : Matrix ι ι ℂ) + β • (vecMulVec d (star d) * H)

/- English proof (translation)
Establish `key : ∀ v : ι → ℂ, Matrix.vecMulVec d (star d) *ᵥ v = (star d ⬝ᵥ v) • d`. Introduce `v`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`.

Rewrite using `[rk, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, key, Matrix.one_mulVec, smul_smul]`. Both sides reduce to the same expression.
-/
lemma rk_mulVec (d : ι → ℂ) (θ β : ℂ) (x : ι → ℂ) : rk H d θ β *ᵥ x = θ • x + (β * herm H x d) • d := by
  have key : ∀ v : ι → ℂ, Matrix.vecMulVec d (star d) *ᵥ v = (star d ⬝ᵥ v) • d := by
    intro v; funext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [rk, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, key,
    Matrix.one_mulVec, smul_smul]
  rfl

/- English proof (translation)
Use `set p := herm H u v with hp_def`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcc, s, hs0, hsp⟩ : ∃ c : ℂ, c * star c = 1 ∧ ∃ s : ℝ, 0 ≤ s ∧ star c * p = s := by`. Distinguish the cases in `hp : p = 0`. Conclude with `⟨1, by simp, 0, le_rfl, by simp [hp]⟩`. Establish `hn : (‖p‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr hp`.

Establish `hpp : p * star p = (‖p‖ : ℂ) ^ 2`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsn : star (‖p‖ : ℂ) = (‖p‖ : ℂ)` using `Complex.conj_ofReal _`.

Use `⟨p / ‖p‖, ?_, ‖p‖, norm_nonneg _, ?_⟩` and prove the remaining obligations. Rewrite using `[star_div₀, hsn, div_mul_div_comm, hpp, ← sq, div_self (pow_ne_zero 2 hn)]`. Rewrite using `[star_div₀, hsn, div_mul_eq_mul_div, mul_comm, hpp, sq, mul_div_assoc, div_self hn, mul_one]`. Establish `hs_star : star (s : ℂ) = s` using `Complex.conj_ofReal s`. Establish `hsp' : c * star p = s`.

Use `congrArg star hsp` as an intermediate fact. Rewrite `this` using `[star_mul', star_star, hs_star]`. Take the linear combination `this`. Establish `hvu : herm H v u = star p` using `(herm_symm H hH u v).symm`. Use `set d := u - c • v with hd`.

Establish `hσ : (0 : ℝ) < t + s` using `by linarith`. Use `set σ : ℂ := ((t + s : ℝ) : ℂ) with hσ_def`. Establish `hσ0 : σ ≠ 0` using `by rw [hσ_def]; exact_mod_cast hσ.ne'`. Establish `hud : herm H u d = -σ`. Rewrite using `[hd, herm_sub_right, herm_smul_right, hu, hsp, hσ_def]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hdd : herm H d d = -2 * σ`. Simplify using `only [hd, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hu, hv, hvu, hσ_def]`. Use `push_cast`.

Take the linear combination `(-1 : ℂ) * hsp - hsp' - (t : ℂ) * hcc`. Establish `hdy : ∀ y, herm H d y = star (herm H y d)` using `fun y => (herm_symm H hH y d).symm`. Use `⟨rk H d (star c) (star c * σ⁻¹), ?_, ?_⟩` and prove the remaining obligations. Apply `unitary_of_form` to reduce the goal to its premises. Introduce `x y`.

Rewrite using `[rk_mulVec, rk_mulVec]`. Simplify using `only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hdy x, hdy y, hdd]`. Establish `hsσ : star σ⁻¹ = σ⁻¹` using `by rw [star_inv₀, hσ_def, Complex.star_def, Complex.conj_ofReal]`. Establish `hβ : σ⁻¹ * σ = 1` using `inv_mul_cancel₀ hσ0`. Simplify using `only [star_mul', star_star, hsσ, hdy d]`.

Take the linear combination `(herm H x y) * hcc - 2 * herm H x d * star (herm H y d) * c * star c * σ⁻¹ * hβ`. Rewrite using `[rk_mulVec, hud]`. Establish `hβ : σ⁻¹ * σ = 1` using `inv_mul_cancel₀ hσ0`. Use function extensionality and compare the values at `i`. Simplify using `only [hd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`.

Take the linear combination `v i * hcc - star c * (u i - c * v i) * hβ`.
-/
lemma transitive (hH : Hᴴ = H) (u v : ι → ℂ) (t : ℝ) (ht : 0 < t) (hu : herm H u u = -(t : ℂ)) (hv : herm H v v = -(t : ℂ)) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v := by
  set p := herm H u v with hp_def
  obtain ⟨c, hcc, s, hs0, hsp⟩ : ∃ c : ℂ, c * star c = 1 ∧ ∃ s : ℝ, 0 ≤ s ∧ star c * p = s := by
    by_cases hp : p = 0
    · exact ⟨1, by simp, 0, le_rfl, by simp [hp]⟩
    · have hn : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hp
      have hpp : p * star p = (‖p‖ : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hsn : star (‖p‖ : ℂ) = (‖p‖ : ℂ) := Complex.conj_ofReal _
      refine ⟨p / ‖p‖, ?_, ‖p‖, norm_nonneg _, ?_⟩
      · rw [star_div₀, hsn, div_mul_div_comm, hpp, ← sq, div_self (pow_ne_zero 2 hn)]
      · rw [star_div₀, hsn, div_mul_eq_mul_div, mul_comm, hpp, sq, mul_div_assoc, div_self hn, mul_one]
  have hs_star : star (s : ℂ) = s := Complex.conj_ofReal s
  have hsp' : c * star p = s := by
    have := congrArg star hsp
    rw [star_mul', star_star, hs_star] at this
    linear_combination this
  have hvu : herm H v u = star p := (herm_symm H hH u v).symm
  set d := u - c • v with hd
  have hσ : (0 : ℝ) < t + s := by linarith
  set σ : ℂ := ((t + s : ℝ) : ℂ) with hσ_def
  have hσ0 : σ ≠ 0 := by rw [hσ_def]; exact_mod_cast hσ.ne'
  have hud : herm H u d = -σ := by
    rw [hd, herm_sub_right, herm_smul_right, hu, hsp, hσ_def]; push_cast; ring
  have hdd : herm H d d = -2 * σ := by
    simp only [hd, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hu, hv, hvu, hσ_def]
    push_cast
    linear_combination (-1 : ℂ) * hsp - hsp' - (t : ℂ) * hcc
  have hdy : ∀ y, herm H d y = star (herm H y d) := fun y => (herm_symm H hH y d).symm
  refine ⟨rk H d (star c) (star c * σ⁻¹), ?_, ?_⟩
  · apply unitary_of_form
    intro x y
    rw [rk_mulVec, rk_mulVec]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hdy x, hdy y, hdd]
    have hsσ : star σ⁻¹ = σ⁻¹ := by rw [star_inv₀, hσ_def, Complex.star_def, Complex.conj_ofReal]
    have hβ : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0
    simp only [star_mul', star_star, hsσ, hdy d]
    linear_combination (herm H x y) * hcc - 2 * herm H x d * star (herm H y d) * c * star c * σ⁻¹ * hβ
  · rw [rk_mulVec, hud]
    have hβ : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0
    funext i
    simp only [hd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination v i * hcc - star c * (u i - c * v i) * hβ

end forms

section hb
variable (k : ℕ)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp_all [eq_comm]`.
-/
lemma Hb_herm : (Hb k)ᴴ = Hb k := by
  ext i j
  simp only [Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all [eq_comm]

/- English proof (translation)
Simplify using `only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]`. Simplify using the standard rewrite rules.
-/
lemma herm_Hb_right (x : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) x (Pi.single i 1) = (if i = Fin.last k then -1 else 1) * x i := by
  simp only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

/- English proof (translation)
Simplify using `only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]`. Simplify using `[mul_comm]`.
-/
lemma herm_Hb_left (y : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) (Pi.single i 1) y = (if i = Fin.last k then -1 else 1) * star (y i) := by
  simp only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp [mul_comm]

def nu (w s : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  1 + vecMulVec ((star w - 1) • Pi.single 0 1 + s • Pi.single (Fin.last k) 1) (Pi.single 0 1) +
    vecMulVec (s • Pi.single 0 1 + (w - 1) • Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1)

/- English proof (translation)
Establish `key : ∀ (a : Fin (k + 1) → ℂ) (j : Fin (k + 1)), Matrix.vecMulVec a (Pi.single j 1) *ᵥ x = x j • a`. Introduce `a j`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.single_apply, mul_comm]`. Rewrite using `[nu, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, key]`.
-/
lemma nu_mulVec (w s : ℂ) (x : Fin (k + 1) → ℂ) :
    nu k w s *ᵥ x = x + x 0 • ((star w - 1) • Pi.single 0 1 + s • Pi.single (Fin.last k) 1) +
      x (Fin.last k) • (s • Pi.single 0 1 + (w - 1) • Pi.single (Fin.last k) 1) := by
  have key : ∀ (a : Fin (k + 1) → ℂ) (j : Fin (k + 1)), Matrix.vecMulVec a (Pi.single j 1) *ᵥ x = x j • a := by
    intro a j; funext i
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.single_apply, mul_comm]
  rw [nu, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, key]

/- English proof (translation)
Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `hL0 : Fin.last k ≠ (0 : Fin (k + 1))` using `fun h => h0L h.symm`. Apply `unitary_of_form` to reduce the goal to its premises. Introduce `x y`. Rewrite using `[nu_mulVec, nu_mulVec]`. Simplify using `only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_Hb_right, herm_Hb_left, herm_single]`.

Simplify using `only [Hb, Matrix.diagonal_apply, h0L, hL0, if_true, if_false, star_add, star_sub, star_mul', star_one, star_star, hs]`. Take the linear combination `(star (y (Fin.last k)) * x (Fin.last k) - star (y 0) * x 0) * hw`.
-/
lemma nu_unitary (hk : 1 ≤ k) (w s : ℂ) (hs : star s = s) (hw : s * s = w * star w - 1) :
    (nu k w s)ᴴ * Hb k * nu k w s = Hb k := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hL0 : Fin.last k ≠ (0 : Fin (k + 1)) := fun h => h0L h.symm
  apply unitary_of_form
  intro x y
  rw [nu_mulVec, nu_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_Hb_right, herm_Hb_left, herm_single]
  simp only [Hb, Matrix.diagonal_apply, h0L, hL0, if_true, if_false, star_add, star_sub, star_mul', star_one, star_star, hs]
  linear_combination (star (y (Fin.last k)) * x (Fin.last k) - star (y 0) * x 0) * hw

/- English proof (translation)
Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[herm_Hb_right, nu_mulVec]`. Simplify using `[Pi.single_apply, h0L, h0L.symm]`.
-/
lemma nu_last (hk : 1 ≤ k) (w s : ℂ) : herm (Hb k) (nu k w s *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -w := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [herm_Hb_right, nu_mulVec]
  simp [Pi.single_apply, h0L, h0L.symm]

/- English proof (translation)
Simplify using `[nu, Matrix.add_apply, Matrix.vecMulVec_apply]`.
-/
lemma nu_apply (w s : ℂ) (i j : Fin (k + 1)) :
    nu k w s i j = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j +
      ((star w - 1) * (Pi.single 0 1 : Fin (k + 1) → ℂ) i + s * (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) i) *
        (Pi.single 0 1 : Fin (k + 1) → ℂ) j +
      (s * (Pi.single 0 1 : Fin (k + 1) → ℂ) i + (w - 1) * (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) i) *
        (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) j := by
  simp [nu, Matrix.add_apply, Matrix.vecMulVec_apply]

open scoped ContDiff in
/- English proof (translation)
Establish `h0L : (0 : Fin (k + 1)) ≠ Fin.last k`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Use `set eL : Fin (k + 1) → ℂ := Pi.single (Fin.last k) 1 with heL`. Establish `hLL : herm (Hb k) eL eL = -1`. Rewrite using `[heL, herm_single]`. Simplify using `[Hb]`. Establish `hsT : 0 < Real.sqrt T` using `Real.sqrt_pos.mpr hT`.

Establish `hsT' : 0 < Real.sqrt T'` using `Real.sqrt_pos.mpr hT'`. Establish `hva : herm (Hb k) ((Real.sqrt T : ℂ) • eL) ((Real.sqrt T : ℂ) • eL) = -(T : ℂ)`. Rewrite using `[herm_smul_left, herm_smul_right, hLL, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvb : herm (Hb k) ((Real.sqrt T' : ℂ) • eL) ((Real.sqrt T' : ℂ) • eL) = -(T' : ℂ)`.

Rewrite using `[herm_smul_left, herm_smul_right, hLL, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hT'.le]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ga, hga, hgau⟩` from `transitive (Hb k) (Hb_herm k) _ a T hT hva ha`. Take `⟨h, hh, hhb⟩` from `transitive (Hb k) (Hb_herm k) b _ T' hT' hb hvb`. Use `set c : ℝ := Real.sqrt T * Real.sqrt T' with hc_def`.

Establish `hc : 0 < c` using `mul_pos hsT hsT'`. Establish `hcc : c * c = T * T'`. Rewrite using `[hc_def]`. Use polynomial arithmetic with `[Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]`. Use `set w : ℂ → ℂ := fun ζ => -ζ / (c : ℂ) with hw_def`.

Use `set s : ℂ → ℂ := fun ζ => ((Real.sqrt (‖w ζ‖ ^ 2 - 1) : ℝ) : ℂ) with hs_def`. Establish `hc0 : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hq : ∀ ζ : ℂ, T * T' < Complex.normSq ζ → 0 < ‖w ζ‖ ^ 2 - 1`. Introduce `ζ hζ`. Establish `e : ‖w ζ‖ ^ 2 = Complex.normSq ζ / (c * c)`.

Rewrite using `[← Complex.normSq_eq_norm_sq, hw_def]`. Simplify using `only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_ofReal]`. Rewrite using `[e, hcc, sub_pos, one_lt_div (mul_pos hT hT')]`. Conclude with `hζ`. Establish `hwC : ContDiff ℝ ∞ w` using `contDiff_id.neg.div_const _`.

Establish `hsC : ContDiffOn ℝ ∞ s {ζ : ℂ | T * T' < Complex.normSq ζ}`. Introduce `ζ hζ`. Establish `h1 : ContDiffAt ℝ ∞ (fun ζ => ‖w ζ‖ ^ 2 - 1) ζ` using `(((contDiff_norm_sq ℝ).comp hwC).contDiffAt).sub contDiffAt_const`. Conclude with `(Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (h1.sqrt (hq ζ hζ).ne')).contDiffWithinAt`. Establish `hsR : ∀ ζ, star (s ζ) = s ζ` using `fun ζ => Complex.conj_ofReal _`.

Establish `hsw : ∀ ζ : ℂ, T * T' < Complex.normSq ζ → s ζ * s ζ = w ζ * star (w ζ) - 1`. Introduce `ζ hζ`. Rewrite using `[hs_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (hq ζ hζ).le, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun ζ => ga * nu k (w ζ) (s ζ) * h, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Establish `hN : ∀ l m, ContDiffOn ℝ ∞ (fun ζ => nu k (w ζ) (s ζ) l m) {ζ : ℂ | T * T' < Complex.normSq ζ}`. Introduce `l m`. Simplify using `only [nu_apply]`.

Establish `hw'` using `hwC.contDiffOn (s := {ζ : ℂ | T * T' < Complex.normSq ζ})`. Establish `hws : ContDiffOn ℝ ∞ (fun ζ => star (w ζ)) {ζ : ℂ | T * T' < Complex.normSq ζ}` using `(Complex.conjCLE.contDiff.comp hwC).contDiffOn`. Conclude with `((contDiffOn_const.add ((((hws.sub contDiffOn_const).mul contDiffOn_const).add (hsC.mul contDiffOn_const)).mul contDiffOn_const)).add (((hsC.mul contDiffOn_const).add ((hw'.sub contDiffOn_const).mul contDiffOn_const)).mul contDiffOn_const))`. Simplify using `only [Matrix.mul_apply]`. Use `ContDiffOn.sum (fun m _ => ?_)` and prove the remaining obligations.

Use `ContDiffOn.mul ?_ contDiffOn_const` and prove the remaining obligations. Use `ContDiffOn.sum (fun l _ => ?_)` and prove the remaining obligations. Conclude with `contDiffOn_const.mul (hN l m)`. Introduce `ζ hζ beta_reduce`. Establish `hN` using `nu_unitary k hk (w ζ) (s ζ) (hsR ζ) (hsw ζ hζ)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hb k := by rw [hga, hN, hh]`.

Rewrite using `[← hgau, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hhb, form_of_unitary (Hb k) hga, Matrix.mulVec_smul, herm_smul_left, herm_smul_right, nu_last k hk, Complex.star_def, Complex.conj_ofReal]`. Establish `hT0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hsT.ne'`. Establish `hT0' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hsT'.ne'`. Simplify using `only [hw_def, hc_def]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
lemma section_core (hk : 1 ≤ k) (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) :
    ∃ μ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
      (∀ i j, ContDiffOn ℝ ∞ (fun ζ => μ ζ i j) {ζ : ℂ | T * T' < Complex.normSq ζ}) ∧
      ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
        (μ ζ)ᴴ * Hb k * μ ζ = Hb k ∧ herm (Hb k) (μ ζ *ᵥ b) a = ζ := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  set eL : Fin (k + 1) → ℂ := Pi.single (Fin.last k) 1 with heL
  have hLL : herm (Hb k) eL eL = -1 := by
    rw [heL, herm_single]; simp [Hb]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsT' : 0 < Real.sqrt T' := Real.sqrt_pos.mpr hT'
  have hva : herm (Hb k) ((Real.sqrt T : ℂ) • eL) ((Real.sqrt T : ℂ) • eL) = -(T : ℂ) := by
    rw [herm_smul_left, herm_smul_right, hLL, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]; ring
  have hvb : herm (Hb k) ((Real.sqrt T' : ℂ) • eL) ((Real.sqrt T' : ℂ) • eL) = -(T' : ℂ) := by
    rw [herm_smul_left, herm_smul_right, hLL, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hT'.le]; ring
  obtain ⟨ga, hga, hgau⟩ := transitive (Hb k) (Hb_herm k) _ a T hT hva ha
  obtain ⟨h, hh, hhb⟩ := transitive (Hb k) (Hb_herm k) b _ T' hT' hb hvb
  set c : ℝ := Real.sqrt T * Real.sqrt T' with hc_def
  have hc : 0 < c := mul_pos hsT hsT'
  have hcc : c * c = T * T' := by
    rw [hc_def]; nlinarith [Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]
  set w : ℂ → ℂ := fun ζ => -ζ / (c : ℂ) with hw_def
  set s : ℂ → ℂ := fun ζ => ((Real.sqrt (‖w ζ‖ ^ 2 - 1) : ℝ) : ℂ) with hs_def
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hq : ∀ ζ : ℂ, T * T' < Complex.normSq ζ → 0 < ‖w ζ‖ ^ 2 - 1 := by
    intro ζ hζ
    have e : ‖w ζ‖ ^ 2 = Complex.normSq ζ / (c * c) := by
      rw [← Complex.normSq_eq_norm_sq, hw_def]
      simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_ofReal]
    rw [e, hcc, sub_pos, one_lt_div (mul_pos hT hT')]
    exact hζ
  have hwC : ContDiff ℝ ∞ w := contDiff_id.neg.div_const _
  have hsC : ContDiffOn ℝ ∞ s {ζ : ℂ | T * T' < Complex.normSq ζ} := by
    intro ζ hζ
    have h1 : ContDiffAt ℝ ∞ (fun ζ => ‖w ζ‖ ^ 2 - 1) ζ :=
      (((contDiff_norm_sq ℝ).comp hwC).contDiffAt).sub contDiffAt_const
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (h1.sqrt (hq ζ hζ).ne')).contDiffWithinAt
  have hsR : ∀ ζ, star (s ζ) = s ζ := fun ζ => Complex.conj_ofReal _
  have hsw : ∀ ζ : ℂ, T * T' < Complex.normSq ζ → s ζ * s ζ = w ζ * star (w ζ) - 1 := by
    intro ζ hζ
    rw [hs_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (hq ζ hζ).le, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  refine ⟨fun ζ => ga * nu k (w ζ) (s ζ) * h, ?_, ?_⟩
  · intro i j
    have hN : ∀ l m, ContDiffOn ℝ ∞ (fun ζ => nu k (w ζ) (s ζ) l m) {ζ : ℂ | T * T' < Complex.normSq ζ} := by
      intro l m
      simp only [nu_apply]
      have hw' := hwC.contDiffOn (s := {ζ : ℂ | T * T' < Complex.normSq ζ})
      have hws : ContDiffOn ℝ ∞ (fun ζ => star (w ζ)) {ζ : ℂ | T * T' < Complex.normSq ζ} :=
        (Complex.conjCLE.contDiff.comp hwC).contDiffOn
      exact ((contDiffOn_const.add ((((hws.sub contDiffOn_const).mul contDiffOn_const).add
        (hsC.mul contDiffOn_const)).mul contDiffOn_const)).add
        (((hsC.mul contDiffOn_const).add ((hw'.sub contDiffOn_const).mul contDiffOn_const)).mul contDiffOn_const))
    simp only [Matrix.mul_apply]
    refine ContDiffOn.sum (fun m _ => ?_)
    refine ContDiffOn.mul ?_ contDiffOn_const
    refine ContDiffOn.sum (fun l _ => ?_)
    exact contDiffOn_const.mul (hN l m)
  · intro ζ hζ
    beta_reduce
    have hN := nu_unitary k hk (w ζ) (s ζ) (hsR ζ) (hsw ζ hζ)
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc hᴴ * ((nu k (w ζ) (s ζ))ᴴ * gaᴴ) * Hb k * (ga * nu k (w ζ) (s ζ) * h)
          = hᴴ * ((nu k (w ζ) (s ζ))ᴴ * (gaᴴ * Hb k * ga) * nu k (w ζ) (s ζ)) * h := by
            simp only [Matrix.mul_assoc]
        _ = Hb k := by rw [hga, hN, hh]
    · rw [← hgau, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hhb, form_of_unitary (Hb k) hga,
        Matrix.mulVec_smul, herm_smul_left, herm_smul_right, nu_last k hk, Complex.star_def, Complex.conj_ofReal]
      have hT0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsT.ne'
      have hT0' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsT'.ne'
      simp only [hw_def, hc_def]
      push_cast
      field_simp

end hb

section mid
variable (k r : ℕ)

/- English proof (translation)
Use `symm`. Use `Fintype.sum_of_injective (wI k r) ?_ (fun j => f (wI k r j)) f ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `a b hab`. Use `congrArg Fin.val hab` as an intermediate fact. Simplify using `only [wI] at this`.

Use `ext`. Use linear arithmetic over natural numbers and integers. Introduce `c hc`. Apply `hf` to reduce the goal to its premises. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hc ⟨⟨c.val - r, by omega⟩, by ext; simp only [wI]; omega⟩`.
-/
lemma sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  symm
  refine Fintype.sum_of_injective (wI k r) ?_ (fun j => f (wI k r j)) f ?_ (fun _ => rfl)
  · intro a b hab
    have := congrArg Fin.val hab
    simp only [wI] at this
    ext; omega
  · intro c hc
    apply hf
    by_contra hcon
    push_neg at hcon
    exact hc ⟨⟨c.val - r, by omega⟩, by ext; simp only [wI]; omega⟩

/- English proof (translation)
Simplify using `only [Hpk, Hb, wI, Matrix.diagonal_apply, Fin.ext_iff, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | (norm_num; done) | (norm_num; intro h; exfalso; omega) | (intro h; exfalso; omega)`.
-/
lemma Hpk_mid (a b : Fin (k + 1)) : Hpk k r (wI k r a) (wI k r b) = Hb k a b := by
  simp only [Hpk, Hb, wI, Matrix.diagonal_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega) | (norm_num; done) | (norm_num; intro h; exfalso; omega) | (intro h; exfalso; omega)

/- English proof (translation)
Simplify using `only [herm, dotProduct, Matrix.mulVec, wbPart, Pi.star_apply]`. Rewrite using `[sum_mid k r _ ?_]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[sum_mid k r _ ?_]`.

Simplify using `only [Hpk_mid]`. Introduce `j hj`. Simplify using `[hz j hj]`. Introduce `i hi`. Simplify using `[hz' i hi]`.
-/
lemma herm_mid (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) z z' = herm (Hb k) (wbPart k r z) (wbPart k r z') := by
  simp only [herm, dotProduct, Matrix.mulVec, wbPart, Pi.star_apply]
  rw [sum_mid k r _ ?_]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [sum_mid k r _ ?_]
    · simp only [Hpk_mid]
    · intro j hj; simp [hz j hj]
  · intro i hi; simp [hz' i hi]

/- English proof (translation)
Establish `e` using `herm_mid k r z z hz hz`. Establish `hx` using `herm_symm (Hb k) (Hb_herm k) (wbPart k r z) (wbPart k r z)`. Simplify using `only [Tz]`. Rewrite using `[e]`. Simplify using `only [Complex.ofReal_neg, neg_neg]`.

Conclude with `(Complex.conj_eq_iff_re.mp hx).symm`.
-/
lemma herm_self (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hb k) (wbPart k r z) (wbPart k r z) = -((Tz k r z : ℝ) : ℂ) := by
  have e := herm_mid k r z z hz hz
  have hx := herm_symm (Hb k) (Hb_herm k) (wbPart k r z) (wbPart k r z)
  simp only [Tz]
  rw [e]
  simp only [Complex.ofReal_neg, neg_neg]
  exact (Complex.conj_eq_iff_re.mp hx).symm

end mid

/- English proof (translation)
Introduce `k r z z' hk hz hz' hT hT'`. Take `⟨μ, h1, h2⟩` from `section_core k hk (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') hT hT' (herm_self k r z hz) (herm_self k r z' hz')`. Conclude with `⟨μ, h1, h2⟩`.
-/
theorem sectionExists : Formalism.QuantumDeterminants.SectionExists := by
  intro k r z z' hk hz hz' hT hT'
  obtain ⟨μ, h1, h2⟩ := section_core k hk (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') hT hT'
    (herm_self k r z hz) (herm_self k r z' hz')
  exact ⟨μ, h1, h2⟩

end Formalism.FourierDecayAlt.P.SettingConstruction

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Introduce `hCC hGN k r Wp Wq _ _ _ _ D A hA`. Conclude with `hCC k r Wp Wq D A (hGN k r D.μG A D.haarG hA)`.
-/
theorem crude_integrability_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCIntCrude := by
  intro hCC hGN k r Wp Wq _ _ _ _ D A hA
  exact hCC k r Wp Wq D A (hGN k r D.μG A D.haarG hA)

/- English proof (translation)
Introduce `k r`. Prove the components needed by the constructor for the conclusion. Introduce `i hi`. Simplify using `only [bvec]`. Rewrite using `[Pi.single_apply, if_neg]`.

Introduce `h`. Substitute `h` using the available equality. Simplify using `[wI] at hi`. Simplify using `only [Tz, bvec]`. Rewrite using `[SettingConstruction.herm_single]`.

Simplify using `[Hpk, wI]`.
-/
theorem base_vector_exists : Formalism.FourierDecayAlt.B2.ZExists := by
  intro k r
  constructor
  · intro i hi
    simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro h; subst h; simp [wI] at hi
  · simp only [Tz, bvec]
    rw [SettingConstruction.herm_single]
    simp [Hpk, wI]

/- English proof (translation)
Set `f : ContDiffBump (1 : ℝ)` to `⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩`. Use `⟨f.normed MeasureTheory.volume, f.contDiff_normed, ?_, f.integral_normed⟩` and prove the remaining obligations. Rewrite using `[f.tsupport_normed_eq]`. Introduce `x hx`. Rewrite `hx` using `[Metric.mem_closedBall, Real.dist_eq]`.

Express the relevant statement in the definitionally equal form `|x - 1| ≤ 1 / 4 at hx`. Use `abs_le.mp hx` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.
-/
theorem character_exists_alt : Formalism.FourierDecayAlt.B2.ChiExists := by
  let f : ContDiffBump (1 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨f.normed MeasureTheory.volume, f.contDiff_normed, ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  change |x - 1| ≤ 1 / 4 at hx
  have := abs_le.mp hx
  constructor <;> linarith [this.1, this.2]

/- English proof (translation)
Introduce `hG hW hN hS hχ hI hZ`. Establish `hE : RealPlaceDataExists`. Introduce `k r Wp Wq _ _ _ _ z z' p1 p2 hk hz hz' hT hT' hrep hrep' hu hu' hcn hcn'`. Take `⟨μG, hμG⟩` from `hG k r`. Take `⟨μW, hμW⟩` from `hW k r z hz hT`.

Take `⟨μN, hμN⟩` from `hN k r`. Take `⟨μW', hμW'⟩` from `hW k r z' hz' hT'`. Take `⟨μsec, hsec⟩` from `hS k r z z' hk hz hz' hT hT'`. Take `⟨χ, hχ1, hχ2, hχ3⟩` from `hχ`. Establish `md : IsMeasData k r z z' μsec μG μW μN μW'` using `⟨hk, hz, hz', hT, hT', hμG, hμW, hμN, hμW', hsec⟩`.

Take `⟨c, ⟨hc0, hcF⟩, -⟩` from `hI k r z z' μsec μG μW μN μW' md`. Conclude with `⟨⟨z, z', p1, p2, c • μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT', hrep, hrep', hu, hu', hcn, hcn', SettingConstruction.haar_smul hμG c hc0, hμW, hμN, hμW', hsec, hχ1, hχ2, hχ3⟩, rfl, rfl, rfl, rfl, hcF⟩`. Use `⟨hE, ?_⟩` and prove the remaining obligations. Introduce `k r hk`. Take `⟨hzm, hzT⟩` from `hZ k r`.

Establish `hrep : IsCRepOn (UWset k r (bvec (wI k r (Fin.last k)))) (fun _ : Mat k r => (1 : ℂ →L[ℂ] ℂ))`. Use `⟨rfl, fun a _ b _ => ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules. Establish `hT : 0 < Tz k r (bvec (wI k r (Fin.last k)))` using `by rw [hzT]; norm_num`.

Take `⟨D, -, -, -, -, hD⟩` from `hE k r ℂ ℂ _ _ (fun _ => 1) (fun _ => 1) hk hzm hzm hT hT hrep hrep (fun _ _ v => by simp) (fun _ _ v => by simp) continuousOn_const continuousOn_const`. Conclude with `⟨D, hD⟩`.
-/
theorem setting_exists_of_parts : Formalism.FourierDecayAlt.B2.AssembleExists := by
  intro hG hW hN hS hχ hI hZ
  have hE : RealPlaceDataExists := by
    intro k r Wp Wq _ _ _ _ z z' p1 p2 hk hz hz' hT hT' hrep hrep' hu hu' hcn hcn'
    obtain ⟨μG, hμG⟩ := hG k r
    obtain ⟨μW, hμW⟩ := hW k r z hz hT
    obtain ⟨μN, hμN⟩ := hN k r
    obtain ⟨μW', hμW'⟩ := hW k r z' hz' hT'
    obtain ⟨μsec, hsec⟩ := hS k r z z' hk hz hz' hT hT'
    obtain ⟨χ, hχ1, hχ2, hχ3⟩ := hχ
    have md : IsMeasData k r z z' μsec μG μW μN μW' := ⟨hk, hz, hz', hT, hT', hμG, hμW, hμN, hμW', hsec⟩
    obtain ⟨c, ⟨hc0, hcF⟩, -⟩ := hI k r z z' μsec μG μW μN μW' md
    exact ⟨⟨z, z', p1, p2, c • μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT', hrep, hrep', hu, hu', hcn, hcn',
      SettingConstruction.haar_smul hμG c hc0, hμW, hμN, hμW', hsec, hχ1, hχ2, hχ3⟩, rfl, rfl, rfl, rfl, hcF⟩
  refine ⟨hE, ?_⟩
  intro k r hk
  obtain ⟨hzm, hzT⟩ := hZ k r
  have hrep : IsCRepOn (UWset k r (bvec (wI k r (Fin.last k)))) (fun _ : Mat k r => (1 : ℂ →L[ℂ] ℂ)) := by
    refine ⟨rfl, fun a _ b _ => ?_⟩
    ext; simp
  have hT : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by rw [hzT]; norm_num
  obtain ⟨D, -, -, -, -, hD⟩ := hE k r ℂ ℂ _ _ (fun _ => 1) (fun _ => 1) hk hzm hzm hT hT hrep hrep
    (fun _ _ v => by simp) (fun _ _ v => by simp) continuousOn_const continuousOn_const
  exact ⟨D, hD⟩

/- English proof (translation)
Conclude with `setting_exists_of_parts hG hW hN SettingConstruction.sectionExists character_exists_alt hI base_vector_exists`.
-/
theorem SettingConstruction.setting_exists_of_haar_normalisation (hG : HaarGExists) (hW : HaarWExists) (hN : HaarNExists) (hI : IntNorm) :
    RealPlaceDataExists ∧ RealPlaceDataNonempty := by
  exact setting_exists_of_parts hG hW hN SettingConstruction.sectionExists character_exists_alt hI base_vector_exists

end Formalism.FourierDecayAlt.P
