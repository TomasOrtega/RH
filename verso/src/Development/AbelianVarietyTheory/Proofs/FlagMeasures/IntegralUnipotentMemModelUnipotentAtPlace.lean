import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, Matrix.conjTranspose_apply, hτ]`.
-/
theorem map_cT_of_conj {E : Type} [Field E] (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x))
    {a b : Type} (M : Matrix a b E) : (cT σ M).map τ = (M.map τ)ᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, hτ]

/- English proof (translation)
Introduce `hV γ hγ w`. Take `⟨hCM, -, hJ, -, -, hD, -, hM, hs, hAd⟩` from `hV`. Take `⟨⟨hU, ⟨ν, hν, hγe⟩, hX⟩, -⟩` from `hγ`. Use `set τ := w.embedding with hτdef`. Establish `hτ : ∀ x, τ ((σ : E →+* E) x) = star (τ x)` using `fun x => hCM.2.2.2 τ x`.

Use `set B := A w with hBdef`. Use `set G := γ.map τ with hGdef`. Use `set H := Hpk k r with hHdef`. Use `set Ew := (eOf P).map τ with hEwdef`. Establish `hJw : Bᴴ * H * B = J.map τ` using `hM w`.

Establish `hdet : B.det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det hJw`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Establish `h2 : τ J.det = (J.map τ).det` using `by rw [RingHom.map_det]; rfl`.

Conclude with `hJ.2 ((map_eq_zero τ).1 (h2.trans h1.symm))`. Establish `hBu : IsUnit B.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hBB : B * B⁻¹ = 1` using `Matrix.mul_nonsing_inv B hBu`. Establish `hBiB : B⁻¹ * B = 1` using `Matrix.nonsing_inv_mul B hBu`. Establish `hGU : Gᴴ * J.map τ * G = J.map τ`.

Establish `h1` using `congrArg (fun M => M.map τ) hU`. Simplify using `only [IsUn, Matrix.map_mul, map_cT_of_conj _ τ hτ] at h1`. Conclude with `h1`. Use `set S : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => (s a : ℂ) * bvec (eI k r a) i with hSdef`. Establish `hAE : B * Ew = S`.

Use extensionality with `i a`. Establish `h1` using `congrFun (hAd w a).1 i`. Simplify `h1` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, Ew, eOf, S]`. Establish `hgM : gM A γ w = B * G * B⁻¹` using `rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show (gM A γ w)ᴴ * H * gM A γ w = H`. Rewrite using `[hgM]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (B⁻¹)ᴴ * (Bᴴ * H * B) * B⁻¹ := by rw [hJw, hGU]`.

Use `_ = (B * B⁻¹)ᴴ * H * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = H := by rw [hBB]; simp`. Establish `hGE : G * Ew = Ew * ν.map τ` using `by show γ.map τ * (eOf P).map τ = (eOf P).map τ * ν.map τ`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hγe]`. Both sides reduce to the same expression.

Establish `hgS : gM A γ w * S = S * ν.map τ`. Rewrite using `[hgM, ← hAE]`. Combine the equalities or inequalities in the displayed calculation. Introduce `b i hbi`. Establish `h1` using `congrFun (congrFun hgS i) b`.

Establish `hl : (gM A γ w * S) i b = gM A γ w i (eI k r b) * (s b : ℂ)`. Simplify using `[S, Matrix.mul_apply, bvec, Pi.single_apply]`. Establish `hr : (S * ν.map τ) i b = (s b : ℂ) * (if i = eI k r b then 1 else 0)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single b]`. Simplify using `[S, bvec, Pi.single_apply, (hν b b).2 rfl]`.

Introduce `a _ hab`. Distinguish the cases in `hia : i = eI k r a`. Establish `hba : b < a`. Establish `: b.val ≤ a.val` using `by rw [hia] at hbi; exact hbi`. Conclude with `lt_of_le_of_ne this (fun h => hab h.symm)`.

Simplify using `[(hν a b).1 hba]`. Simplify using `[S, bvec, Pi.single_apply, hia]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hl, hr]`. Establish `hs0 : (s b : ℂ) ≠ 0` using `by exact_mod_cast (hs b).ne'`.

Establish `h2` using `mul_right_cancel₀ hs0 (h1.trans (mul_comm _ _))`. Conclude with `h2`. Establish `hH : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), r ≤ j.val → j.val ≤ r + k → H (eI k r a) j = 0`. Introduce `a j h1 h2`. Establish `ha` using `a.isLt`.

Establish `hv : (eI k r a).val = a.val` using `rfl`. Use `show Hpk k r (eI k r a) j = 0`. Unfold `Hpk`. Rewrite using `[if_neg (by rw [hv]; omega), if_neg (by omega), if_neg (fun h => absurd h.1 (by rw [hv]; omega))]`. Use `set K := cT (σ : E →+* E) (eOf P) * J with hKdef`.

Establish `hKf : K * f = 1`. Use extensionality with `a b`. Establish `h1` using `congrFun (congrFun hD.1 a.castSucc) b`. Simplify using `only [pairM, K, cT, eOf, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id, Matrix.of_apply, Matrix.one_apply] at h1 ⊢`. Rewrite using `[h1]`.

Simplify using `[Fin.castSucc_inj]`. Use `set Q := 1 - f * K with hQdef`. Establish `hKQ : K * Q = 0`. Rewrite using `[hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKf, Matrix.one_mul, sub_self]`. Establish `hcol : ∀ j, ∃ c, γ *ᵥ (Q *ᵥ Pi.single j 1) - Q *ᵥ Pi.single j 1 = eOf P *ᵥ c`.

Introduce `j`. Apply `hX` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_mulVec, hKQ, Matrix.zero_mulVec]`. Use `choose c hc using hcol`. Use `set C : Matrix (Fin r) (Fin (2 * r + k + 1)) E := Matrix.of fun a j => c j a with hCdef`.

Establish `hsj : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) i j, (M *ᵥ Pi.single j 1) i = M i j`. Introduce `M i j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hQC : (γ - 1) * Q = eOf P * C`. Use extensionality with `i j`.

Establish `h1` using `congrFun (hc j) i`. Rewrite `h1` using `[Matrix.mulVec_mulVec, ← Matrix.sub_mulVec]`. Establish `e1 : γ * Q - Q = (γ - 1) * Q` using `by rw [Matrix.sub_mul, Matrix.one_mul]`. Rewrite `h1` using `[e1, hsj]`. Rewrite using `[h1, Matrix.mul_apply]`.

Simplify using `[Matrix.mulVec, dotProduct, C]`. Use `set fw := f.map τ with hfwdef`. Use `set Kw := Ewᴴ * J.map τ with hKwdef`. Establish `hQw : (G - 1) * (1 - fw * Kw) = Ew * C.map τ`. Establish `h1` using `congrArg τ.mapMatrix hQC`.

Rewrite `h1` using `[map_mul, map_sub, map_one, hQdef, map_sub, map_one]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_mul, hKdef, map_cT_of_conj _ τ hτ] at h1`. Conclude with `h1`. Establish `hKB : Kw * B⁻¹ = Sᴴ * H` using `by show Ewᴴ * J.map τ * B⁻¹ = Sᴴ * H`. Rewrite using `[← hJw, ← hAE]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[hBB, Matrix.mul_one]`. Establish `hdecomp : gM A γ w - 1 = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H)`. Establish `e1 : gM A γ w - 1 = B * (G - 1) * B⁻¹`. Rewrite using `[hgM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBB]`.

Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_add_cancel, Matrix.mul_one]`. Use `_ = B * ((G - 1) * (1 - fw * Kw)) * B⁻¹ + B * (G - 1) * fw * (Kw * B⁻¹) := by`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by`. Rewrite using `[hQw, hKB, ← hAE]`. Simplify using `only [Matrix.mul_assoc]`. Introduce `i j hj1 hj2 hi`.

Establish `h1` using `congrFun (congrFun hdecomp i) j`. Rewrite `h1` using `[Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]`. Establish `z1 : (S * (C.map τ * B⁻¹)) i j = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Establish `hia : i ≠ eI k r a` using `fun h => by`. Establish `ha` using `a.isLt`. Rewrite `hi` using `[h]`. Conclude with `absurd hi (show ¬ r ≤ a.val by omega)`. Simplify using `[S, bvec, Pi.single_apply, hia]`.

Establish `z2 : (B * (G - 1) * fw * (Sᴴ * H) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `h3 : (Sᴴ * H : Matrix (Fin r) (Fin (2 * r + k + 1)) ℂ) a j = 0`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l = eI k r a`. Substitute `hl` using the available equality. Rewrite using `[hH a j hj1 hj2, mul_zero]`. Simplify using `[S, bvec, Pi.single_apply, hl, Matrix.conjTranspose_apply]`.

Rewrite using `[h3, mul_zero]`. Rewrite `h1` using `[z1, z2, add_zero]`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem gM_mem_Nset (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ w, gM A γ w ∈ Nset k r := by
  intro hV γ hγ w
  obtain ⟨hCM, -, hJ, -, -, hD, -, hM, hs, hAd⟩ := hV
  obtain ⟨⟨hU, ⟨ν, hν, hγe⟩, hX⟩, -⟩ := hγ
  set τ := w.embedding with hτdef
  have hτ : ∀ x, τ ((σ : E →+* E) x) = star (τ x) := fun x => hCM.2.2.2 τ x
  set B := A w with hBdef
  set G := γ.map τ with hGdef
  set H := Hpk k r with hHdef
  set Ew := (eOf P).map τ with hEwdef
  have hJw : Bᴴ * H * B = J.map τ := hM w

  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJw
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    have h2 : τ J.det = (J.map τ).det := by rw [RingHom.map_det]; rfl
    exact hJ.2 ((map_eq_zero τ).1 (h2.trans h1.symm))
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu

  have hGU : Gᴴ * J.map τ * G = J.map τ := by
    have h1 := congrArg (fun M => M.map τ) hU
    simp only [IsUn, Matrix.map_mul, map_cT_of_conj _ τ hτ] at h1
    exact h1

  set S : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => (s a : ℂ) * bvec (eI k r a) i with hSdef
  have hAE : B * Ew = S := by
    ext i a
    have h1 := congrFun (hAd w a).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ew, eOf, S] using h1
  have hgM : gM A γ w = B * G * B⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    show (gM A γ w)ᴴ * H * gM A γ w = H
    rw [hgM]
    calc (B * G * B⁻¹)ᴴ * H * (B * G * B⁻¹) = (B⁻¹)ᴴ * (Gᴴ * (Bᴴ * H * B) * G) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * H * B) * B⁻¹ := by rw [hJw, hGU]
      _ = (B * B⁻¹)ᴴ * H * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hBB]; simp
  ·
    have hGE : G * Ew = Ew * ν.map τ := by
      show γ.map τ * (eOf P).map τ = (eOf P).map τ * ν.map τ
      rw [← Matrix.map_mul, ← Matrix.map_mul, hγe]
      rfl
    have hgS : gM A γ w * S = S * ν.map τ := by
      rw [hgM, ← hAE]
      calc B * G * B⁻¹ * (B * Ew) = B * G * (B⁻¹ * B) * Ew := by simp only [Matrix.mul_assoc]
        _ = B * (G * Ew) := by rw [hBiB, Matrix.mul_one, Matrix.mul_assoc]
        _ = B * Ew * ν.map τ := by rw [hGE, Matrix.mul_assoc]
    intro b i hbi
    have h1 := congrFun (congrFun hgS i) b
    have hl : (gM A γ w * S) i b = gM A γ w i (eI k r b) * (s b : ℂ) := by
      simp [S, Matrix.mul_apply, bvec, Pi.single_apply]
    have hr : (S * ν.map τ) i b = (s b : ℂ) * (if i = eI k r b then 1 else 0) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · simp [S, bvec, Pi.single_apply, (hν b b).2 rfl]
      · intro a _ hab
        by_cases hia : i = eI k r a
        · have hba : b < a := by
            have : b.val ≤ a.val := by rw [hia] at hbi; exact hbi
            exact lt_of_le_of_ne this (fun h => hab h.symm)
          simp [(hν a b).1 hba]
        · simp [S, bvec, Pi.single_apply, hia]
      · simp
    rw [hl, hr] at h1
    have hs0 : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have h2 := mul_right_cancel₀ hs0 (h1.trans (mul_comm _ _))
    exact h2
  ·
    have hH : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), r ≤ j.val → j.val ≤ r + k → H (eI k r a) j = 0 := by
      intro a j h1 h2
      have ha := a.isLt
      have hv : (eI k r a).val = a.val := rfl
      show Hpk k r (eI k r a) j = 0
      unfold Hpk
      rw [if_neg (by rw [hv]; omega), if_neg (by omega), if_neg (fun h => absurd h.1 (by rw [hv]; omega))]
    set K := cT (σ : E →+* E) (eOf P) * J with hKdef
    have hKf : K * f = 1 := by
      ext a b
      have h1 := congrFun (congrFun hD.1 a.castSucc) b
      simp only [pairM, K, cT, eOf, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
        Matrix.submatrix_apply, id, Matrix.of_apply, Matrix.one_apply] at h1 ⊢
      rw [h1]
      simp [Fin.castSucc_inj]
    set Q := 1 - f * K with hQdef
    have hKQ : K * Q = 0 := by
      rw [hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKf, Matrix.one_mul, sub_self]
    have hcol : ∀ j, ∃ c, γ *ᵥ (Q *ᵥ Pi.single j 1) - Q *ᵥ Pi.single j 1 = eOf P *ᵥ c := by
      intro j
      apply hX
      rw [Matrix.mulVec_mulVec, hKQ, Matrix.zero_mulVec]
    choose c hc using hcol
    set C : Matrix (Fin r) (Fin (2 * r + k + 1)) E := Matrix.of fun a j => c j a with hCdef
    have hsj : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) i j, (M *ᵥ Pi.single j 1) i = M i j := by
      intro M i j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hQC : (γ - 1) * Q = eOf P * C := by
      ext i j
      have h1 := congrFun (hc j) i
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec] at h1
      have e1 : γ * Q - Q = (γ - 1) * Q := by rw [Matrix.sub_mul, Matrix.one_mul]
      rw [e1, hsj] at h1
      rw [h1, Matrix.mul_apply]
      simp [Matrix.mulVec, dotProduct, C]
    set fw := f.map τ with hfwdef
    set Kw := Ewᴴ * J.map τ with hKwdef
    have hQw : (G - 1) * (1 - fw * Kw) = Ew * C.map τ := by
      have h1 := congrArg τ.mapMatrix hQC
      rw [map_mul, map_sub, map_one, hQdef, map_sub, map_one] at h1
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, hKdef, map_cT_of_conj _ τ hτ] at h1
      exact h1
    have hKB : Kw * B⁻¹ = Sᴴ * H := by
      show Ewᴴ * J.map τ * B⁻¹ = Sᴴ * H
      rw [← hJw, ← hAE]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hBB, Matrix.mul_one]
    have hdecomp : gM A γ w - 1 = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
      have e1 : gM A γ w - 1 = B * (G - 1) * B⁻¹ := by
        rw [hgM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBB]
      rw [e1]
      calc B * (G - 1) * B⁻¹ = B * (G - 1) * ((1 - fw * Kw) + fw * Kw) * B⁻¹ := by
            rw [sub_add_cancel, Matrix.mul_one]
        _ = B * ((G - 1) * (1 - fw * Kw)) * B⁻¹ + B * (G - 1) * fw * (Kw * B⁻¹) := by
            rw [Matrix.mul_add, Matrix.add_mul]; simp only [Matrix.mul_assoc]
        _ = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
            rw [hQw, hKB, ← hAE]; simp only [Matrix.mul_assoc]
    intro i j hj1 hj2 hi
    have h1 := congrFun (congrFun hdecomp i) j
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply] at h1
    have z1 : (S * (C.map τ * B⁻¹)) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hia : i ≠ eI k r a := fun h => by
        have ha := a.isLt
        rw [h] at hi
        exact absurd hi (show ¬ r ≤ a.val by omega)
      simp [S, bvec, Pi.single_apply, hia]
    have z2 : (B * (G - 1) * fw * (Sᴴ * H) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have h3 : (Sᴴ * H : Matrix (Fin r) (Fin (2 * r + k + 1)) ℂ) a j = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l = eI k r a
        · subst hl
          rw [hH a j hj1 hj2, mul_zero]
        · simp [S, bvec, Pi.single_apply, hl, Matrix.conjTranspose_apply]
      rw [h3, mul_zero]
    rw [z1, z2, add_zero] at h1
    exact sub_eq_zero.1 h1

end GlobalTheory.SnMass.VolN

end
