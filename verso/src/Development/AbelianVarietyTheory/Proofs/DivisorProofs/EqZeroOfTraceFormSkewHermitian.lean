import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.TraceSkew

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toAlgHom.toRingHom

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma map_cc_mul {r : ℕ} (A B : Matrix (Fin r) (Fin r) E) :
    (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := ccHom E)

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
lemma exists_ne_zero_cc_eq_neg : ∃ β : E, β ≠ 0 ∧ cc β = -β := by
  by_contra h
  push_neg at h
  apply IsCMField.complexConj_ne_one E
  refine AlgEquiv.ext fun x => ?_
  have h1 : cc (x - cc x) = -(x - cc x) := by
    simp only [cc, map_sub, IsCMField.complexConj_apply_apply]; ring
  have h2 := h (x - cc x)
  have h3 : x - cc x = 0 := by
    by_contra hne
    exact h2 hne h1
  have : cc x = x := by linear_combination -h3
  simpa [cc] using this

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_eq_dot {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma form_skew_of_matrix {r : ℕ} (G Y : Matrix (Fin r) (Fin r) E)
    (h : Yᵀ * G + G * Y.map cc = 0) (u w : Fin r → E) :
    herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0 := by
  have hc : (fun b => cc ((Y *ᵥ w) b)) = Y.map cc *ᵥ (fun b => cc (w b)) := by
    funext b
    simp [mulVec, dotProduct, cc, map_sum, map_mul]
  rw [herm_eq_dot, herm_eq_dot, hc, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, h, zero_mulVec, dotProduct_zero]

end GlobalTheory.TraceSkew

namespace GlobalTheory.TraceSkew

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. By extensionality, compare the relevant components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem traceForm_nondegenerate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ Y : Matrix (Fin r) (Fin r) E, Y.trace = 0 → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace = 0) → X = 0 := by
  intro E _ _ _ r G X hG hdet htr _hX hY
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    ext i
    exact i.elim0
  have hr : (r : E) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGTu : IsUnit Gᵀ.det := by rw [det_transpose]; exact hGu
  set Q : Matrix (Fin r) (Fin r) E := (Gᵀ)⁻¹ with hQdef
  have hQT : Qᵀ * G = 1 := by
    rw [hQdef, transpose_nonsing_inv, transpose_transpose]
    exact nonsing_inv_mul G hGu
  have hQG : Q * Gᵀ = 1 := nonsing_inv_mul _ hGTu
  have hGmap : Gᵀ.map cc = G := by
    ext a b
    simp only [map_apply, transpose_apply]
    exact hG b a
  have hQmap : G * Q.map cc = 1 := by
    have h1 : Q.map cc * G = 1 := by
      rw [← hGmap, ← map_cc_mul, hQG]
      ext a b
      simp only [map_apply, one_apply]
      split_ifs <;> simp [cc]
    exact mul_eq_one_comm.mp h1

  have hskew : ∀ K : Matrix (Fin r) (Fin r) E, Kᵀ + K.map cc = 0 →
      (Q * K)ᵀ * G + G * (Q * K).map cc = 0 := by
    intro K hK
    rw [transpose_mul, map_cc_mul, Matrix.mul_assoc, hQT, Matrix.mul_one, ← Matrix.mul_assoc,
      hQmap, Matrix.one_mul]
    exact hK

  have htrskew : ∀ Y : Matrix (Fin r) (Fin r) E, Yᵀ * G + G * Y.map cc = 0 →
      cc Y.trace = -Y.trace := by
    intro Y hY'
    have h0 : G * Y.map cc = -(Yᵀ * G) := eq_neg_of_add_eq_zero_right hY'
    have h1 : Y.map cc = -(G⁻¹ * (Yᵀ * G)) := by
      calc Y.map cc = G⁻¹ * (G * Y.map cc) := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul G hGu, Matrix.one_mul]
        _ = -(G⁻¹ * (Yᵀ * G)) := by rw [h0, Matrix.mul_neg]
    have h2 : (Y.map cc).trace = cc Y.trace := by
      simp [trace, cc, map_sum]
    rw [← h2, h1, trace_neg, trace_mul_comm, Matrix.mul_assoc, mul_nonsing_inv G hGu,
      Matrix.mul_one, trace_transpose]

  have hXY : ∀ Y : Matrix (Fin r) (Fin r) E, Yᵀ * G + G * Y.map cc = 0 → (X * Y).trace = 0 := by
    intro Y hY'
    set c : E := Y.trace / r with hcdef
    have hc : cc c = -c := by
      have : cc (r : E) = r := map_natCast (ccHom E) r
      rw [hcdef, show cc (Y.trace / r) = cc Y.trace / cc (r : E) from map_div₀ (ccHom E) _ _,
        this, htrskew Y hY', neg_div]
    have hmap1 : (c • (1 : Matrix (Fin r) (Fin r) E)).map cc = -(c • 1) := by
      ext a b
      simp only [map_apply, Matrix.smul_apply, one_apply, Matrix.neg_apply, smul_eq_mul]
      by_cases hab : a = b
      · simp only [hab, if_true, mul_one]; exact hc
      · simp [hab, cc]
    have hmapY : (Y - c • (1 : Matrix (Fin r) (Fin r) E)).map cc = Y.map cc - (c • (1 : Matrix (Fin r) (Fin r) E)).map cc := by
      ext a b
      simp [cc]
    have hs : (Y - c • (1 : Matrix (Fin r) (Fin r) E))ᵀ * G + G * (Y - c • (1 : Matrix (Fin r) (Fin r) E)).map cc = 0 := by
      rw [hmapY, hmap1, transpose_sub, transpose_smul, transpose_one, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, ← hY']
      abel
    have ht : (Y - c • (1 : Matrix (Fin r) (Fin r) E)).trace = 0 := by
      rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, hcdef,
        div_mul_cancel₀ _ hr, sub_self]
    have h := hY (Y - c • (1 : Matrix (Fin r) (Fin r) E)) ht (form_skew_of_matrix G _ hs)
    rw [Matrix.mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_one, trace_smul, htr,
      smul_zero, sub_zero] at h
    exact h

  obtain ⟨β, hβ0, hβ⟩ := exists_ne_zero_cc_eq_neg (E := E)
  have hβ' : IsCMField.complexConj E β = -β := hβ
  have hall : ∀ K : Matrix (Fin r) (Fin r) E, (X * Q * K).trace = 0 := by
    intro K
    let A : Matrix (Fin r) (Fin r) E := of fun i j => (K i j - cc (K j i)) / 2
    let B : Matrix (Fin r) (Fin r) E := of fun i j => (K i j + cc (K j i)) / (2 * β)
    have hA : Aᵀ + A.map cc = 0 := by
      ext i j
      simp only [A, Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.zero_apply, cc, map_sub,
        map_div₀, map_ofNat, IsCMField.complexConj_apply_apply]
      ring
    have hB : Bᵀ + B.map cc = 0 := by
      ext i j
      simp only [B, Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.zero_apply, cc, map_add,
        map_div₀, map_mul, map_ofNat, IsCMField.complexConj_apply_apply, hβ']
      field_simp
      ring
    have hK : K = A + β • B := by
      ext i j
      simp only [A, B, Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      field_simp
      ring
    rw [Matrix.mul_assoc, hK, Matrix.mul_add, Matrix.mul_add, trace_add, Matrix.mul_smul,
      Matrix.mul_smul, trace_smul, hXY _ (hskew A hA), hXY _ (hskew B hB), smul_zero, add_zero]
  have hXQ : X * Q = 0 := by
    rw [ext_iff_trace_mul_right]
    intro K
    rw [hall K, Matrix.zero_mul, trace_zero]
  calc X = X * Q * Gᵀ := by rw [Matrix.mul_assoc, hQG, Matrix.mul_one]
    _ = 0 := by rw [hXQ, Matrix.zero_mul]

end GlobalTheory.TraceSkew
