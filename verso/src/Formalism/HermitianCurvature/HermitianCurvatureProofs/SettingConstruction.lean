import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.SettingConstruction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
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
Simplify using the standard rewrite rules.
-/
lemma herm_add_left (u u' w : ι → ℂ) : herm H (u + u') w = herm H u w + herm H u' w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_sub_left (u u' w : ι → ℂ) : herm H (u - u') w = herm H u w - herm H u' w := by
  simp [herm, Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_smul_left (c : ℂ) (u w : ι → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_add_right (u w w' : ι → ℂ) : herm H u (w + w') = herm H u w + herm H u w' := by
  simp [herm, add_dotProduct]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_sub_right (u w w' : ι → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by
  simp [herm, sub_dotProduct]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_smul_right (c : ℂ) (u w : ι → ℂ) : herm H u (c • w) = star c * herm H u w := by
  simp [herm, smul_dotProduct]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma herm_symm (hH : Hᴴ = H) (u w : ι → ℂ) : star (herm H u w) = herm H w u := by
  simp only [herm]
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma herm_mulVec (g : Matrix ι ι ℂ) (x y : ι → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm (gᴴ * H * g) x y := by
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

variable [DecidableEq ι]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_single (i j : ι) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  simp [herm, dotProduct, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
lemma unitary_of_form (g : Matrix ι ι ℂ) (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : gᴴ * H * g = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rwa [herm_mulVec, herm_single, herm_single] at this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma form_of_unitary {g : Matrix ι ι ℂ} (h : gᴴ * H * g = H) (x y : ι → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  rw [herm_mulVec, h]

def rk (d : ι → ℂ) (θ β : ℂ) : Matrix ι ι ℂ := θ • (1 : Matrix ι ι ℂ) + β • (vecMulVec d (star d) * H)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma Hb_herm : (Hb k)ᴴ = Hb k := by
  ext i j
  simp only [Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all [eq_comm]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma herm_Hb_right (x : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) x (Pi.single i 1) = (if i = Fin.last k then -1 else 1) * x i := by
  simp only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma nu_mulVec (w s : ℂ) (x : Fin (k + 1) → ℂ) :
    nu k w s *ᵥ x = x + x 0 • ((star w - 1) • Pi.single 0 1 + s • Pi.single (Fin.last k) 1) +
      x (Fin.last k) • (s • Pi.single 0 1 + (w - 1) • Pi.single (Fin.last k) 1) := by
  have key : ∀ (a : Fin (k + 1) → ℂ) (j : Fin (k + 1)), Matrix.vecMulVec a (Pi.single j 1) *ᵥ x = x j • a := by
    intro a j; funext i
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.single_apply, mul_comm]
  rw [nu, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, key]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma nu_last (hk : 1 ≤ k) (w s : ℂ) : herm (Hb k) (nu k w s *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -w := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [herm_Hb_right, nu_mulVec]
  simp [Pi.single_apply, h0L, h0L.symm]

/- English proof (translation)
Simplify using the standard rewrite rules.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
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
Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Assume the negation of the conclusion and derive a contradiction.

A detailed English derivation is pending.
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
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma Hpk_mid (a b : Fin (k + 1)) : Hpk k r (wI k r a) (wI k r b) = Hb k a b := by
  simp only [Hpk, Hb, wI, Matrix.diagonal_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega) | (norm_num; done) | (norm_num; intro h; exfalso; omega) | (intro h; exfalso; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
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
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem crude_integrability_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCIntCrude := by
  intro hCC hGN k r Wp Wq _ _ _ _ D A hA
  exact hCC k r Wp Wq D A (hGN k r D.μG A D.haarG hA)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
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
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
A detailed English derivation is pending.
-/
theorem SettingConstruction.setting_exists_of_haar_normalisation (hG : HaarGExists) (hW : HaarWExists) (hN : HaarNExists) (hI : IntNorm) :
    RealPlaceDataExists ∧ RealPlaceDataNonempty := by
  exact setting_exists_of_parts hG hW hN SettingConstruction.sectionExists character_exists_alt hI base_vector_exists

end Formalism.FourierDecayAlt.P
