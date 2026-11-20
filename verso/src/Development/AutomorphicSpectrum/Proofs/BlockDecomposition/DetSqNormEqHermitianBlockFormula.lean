import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.KWhit

/- English proof (translation)
Introduce `n _ _ t u D K₁ K₂ β h g e η he hη hK h1 h2 htu hh hβ hg hgdet`. Take `⟨s, hsdef⟩ : ∃ s : ℝ, s = ‖η‖ ^ (-(1 / 2 : ℝ))` from `⟨_, rfl⟩`. Rewrite `hg` using `[← hsdef]`. Take `⟨M, hM⟩ : ∃ M : Matrix n n ℂ, M = g⁻¹ * h.map star * g⁻¹ᴴ` from `⟨_, rfl⟩`. Rewrite using `[← hM]`.

Establish `hn : 0 < ‖η‖` using `norm_pos_iff.mpr hη`. Establish `hss : s * s = ‖η‖ ^ (-1 : ℝ)`. Rewrite using `[hsdef, ← Real.rpow_add hn]`. Evaluate the numerical expressions. Establish `hs : s * s * ‖η‖ = 1`.

Rewrite using `[hss, Real.rpow_neg_one, inv_mul_cancel₀ hn.ne']`. Establish `hs0 : s ≠ 0`. Introduce `h0`. Rewrite `hs` using `[h0]`. Simplify using `at hs`.

Establish `hinv : s⁻¹ = s * ‖η‖` using `inv_eq_of_mul_eq_one_right (by linear_combination hs)`. Establish `nsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z`. Introduce `z`. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Conclude with `(Complex.mul_conj z).symm`.

Establish `hsstar : star (s : ℂ) = s`. Conclude with `Complex.conj_ofReal s`. Establish `hsinvstar : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹`. Rewrite using `[star_inv₀, hsstar]`. Establish `hee : e * star e = 1`.

Rewrite using `[← nsq e, he]`. Evaluate the numerical expressions. Establish `hee' : star e * e = 1` using `by rw [mul_comm]; exact hee`. Establish `hsC : (s : ℂ) ≠ 0` using `by exact_mod_cast hs0`. Establish `hsa : star (-(η * (s : ℂ))) = -(star η * (s : ℂ))`.

Rewrite using `[star_neg, star_mul', hsstar]`. Establish `ha : -(η * (s : ℂ)) * star (-(η * (s : ℂ))) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹`. Rewrite using `[hsa]`. Establish `e1 : -(η * (s : ℂ)) * -(star η * (s : ℂ)) = (η * star η) * ((s : ℂ) * (s : ℂ))`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, ← nsq η]`. Establish `e2 : ‖η‖ ^ 2 * (s * s) = s⁻¹ * s⁻¹`. Rewrite using `[hinv]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have e3 : ((‖η‖ ^ 2 : ℝ) : ℂ) * ((s : ℂ) * (s : ℂ)) = ((‖η‖ ^ 2 * (s * s) : ℝ) : ℂ) := by first | (push_cast; ring) | push_cast | simp`.

Rewrite using `[e3, e2]`. Apply the tactic sequence `first | (push_cast; ring) | push_cast | simp`. Establish `ha' : star (-(η * (s : ℂ))) * -(η * (s : ℂ)) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹`. Rewrite using `[mul_comm]`. Conclude with `ha`.

Establish `hs_ij : ∀ i j, star (h i j) = h j i`. Introduce `i j`. Establish `hx` using `congrArg (fun X : Matrix n n ℂ => X j i) hh`. Simplify using `only [Matrix.conjTranspose_apply] at hx`. Conclude with `hx`.

Establish `hT : h.map star = hᵀ`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `hs_ij i j`. Establish `hTH : hᵀᴴ = hᵀ`.

Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply]`. Conclude with `hs_ij i j`. Establish `hgg : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hgdet`. Establish `hgg' : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g hgdet`.

Establish `hMH : Mᴴ = M`. Rewrite using `[hM, hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hTH, mul_assoc]`. Establish `hgM : g * M = hᵀ * g⁻¹ᴴ`. Rewrite using `[hM, hT, ← mul_assoc, ← mul_assoc, hgg, one_mul]`. Establish `hut : uᴴ * t = 1`.

Establish `hx` using `congrArg Matrix.conjTranspose htu`. Rewrite `hx` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one]`. Then use the resulting hypothesis. Establish `huH : uᴴ = (s : ℂ) • g⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `hu : u = (s : ℂ) • g⁻¹ᴴ`.

Combine the equalities or inequalities in the displayed calculation. Establish `ht : t = (s : ℂ)⁻¹ • g`. Establish `h3 : (s : ℂ) • t = g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h3, smul_smul, inv_mul_cancel₀ hsC, one_smul]`.

Establish `hβu : β * u = (-(η * (s : ℂ))) • (g * M)`. Rewrite using `[hβ, hu, hgM, neg_mul, smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul]`. Establish `hDD : D * Dᴴ = t * tᴴ + (β * u) * (β * u)ᴴ`. Establish `step1 : D * Dᴴ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]`. Rewrite using `[step1, ← h1, ← h2]`. Simplify using `only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hee', one_smul]`. Establish `hmain : D * Dᴴ = ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • (g * (1 + M * M) * gᴴ)`. Rewrite using `[hDD, ht, hβu]`.

Simplify using `only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsinvstar, ha']`. Rewrite using `[← smul_add]`. Use `congr 1`. Simplify using `only [Matrix.conjTranspose_mul, hMH, mul_add, add_mul, mul_one, mul_assoc]`. Establish `hdet : D.det * star D.det = t.det * star t.det * (1 + M * M).det`.

Establish `lhs : D.det * star D.det = (D * Dᴴ).det`. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose]`. Rewrite using `[lhs, hmain, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ht, Matrix.det_smul, star_mul', star_pow, hsinvstar]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hdet` using `[← nsq, ← nsq]`.

Establish `hre` using `congrArg Complex.re hdet`. Use `first`. Consider the case `(rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre; exact hre)`. Consider the case `(simpa [Complex.mul_re] using hre)`.
-/
theorem norm_det_bottom_block_sq :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ),
      ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ →
      tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) →
      g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det →
      ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 *
        (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  intro n _ _ t u D K₁ K₂ β h g e η he hη hK h1 h2 htu hh hβ hg hgdet
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ‖η‖ ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hsdef] at hg
  obtain ⟨M, hM⟩ : ∃ M : Matrix n n ℂ, M = g⁻¹ * h.map star * g⁻¹ᴴ := ⟨_, rfl⟩
  rw [← hM]
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hss : s * s = ‖η‖ ^ (-1 : ℝ) := by
    rw [hsdef, ← Real.rpow_add hn]
    norm_num
  have hs : s * s * ‖η‖ = 1 := by
    rw [hss, Real.rpow_neg_one, inv_mul_cancel₀ hn.ne']
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hinv : s⁻¹ = s * ‖η‖ := inv_eq_of_mul_eq_one_right (by linear_combination hs)
  have nsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  have hsstar : star (s : ℂ) = s := by
    exact Complex.conj_ofReal s
  have hsinvstar : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
    rw [star_inv₀, hsstar]
  have hee : e * star e = 1 := by
    rw [← nsq e, he]
    norm_num
  have hee' : star e * e = 1 := by rw [mul_comm]; exact hee
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsa : star (-(η * (s : ℂ))) = -(star η * (s : ℂ)) := by
    rw [star_neg, star_mul', hsstar]
  have ha : -(η * (s : ℂ)) * star (-(η * (s : ℂ))) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [hsa]
    have e1 : -(η * (s : ℂ)) * -(star η * (s : ℂ)) = (η * star η) * ((s : ℂ) * (s : ℂ)) := by
      ring
    rw [e1, ← nsq η]
    have e2 : ‖η‖ ^ 2 * (s * s) = s⁻¹ * s⁻¹ := by
      rw [hinv]
      ring
    have e3 : ((‖η‖ ^ 2 : ℝ) : ℂ) * ((s : ℂ) * (s : ℂ)) = ((‖η‖ ^ 2 * (s * s) : ℝ) : ℂ) := by
      first | (push_cast; ring) | push_cast | simp
    rw [e3, e2]
    first | (push_cast; ring) | push_cast | simp
  have ha' : star (-(η * (s : ℂ))) * -(η * (s : ℂ)) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [mul_comm]; exact ha
  have hs_ij : ∀ i j, star (h i j) = h j i := by
    intro i j
    have hx := congrArg (fun X : Matrix n n ℂ => X j i) hh
    simp only [Matrix.conjTranspose_apply] at hx
    exact hx
  have hT : h.map star = hᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hTH : hᵀᴴ = hᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgdet
  have hMH : Mᴴ = M := by
    rw [hM, hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hTH, mul_assoc]
  have hgM : g * M = hᵀ * g⁻¹ᴴ := by
    rw [hM, hT, ← mul_assoc, ← mul_assoc, hgg, one_mul]
  have hut : uᴴ * t = 1 := by
    have hx := congrArg Matrix.conjTranspose htu
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] at hx
  have huH : uᴴ = (s : ℂ) • g⁻¹ := by
    calc uᴴ = g⁻¹ * (g * uᴴ) := by rw [← mul_assoc, hgg', one_mul]
      _ = (s : ℂ) • g⁻¹ := by rw [hg, mul_smul_comm, mul_one]
  have hu : u = (s : ℂ) • g⁻¹ᴴ := by
    calc u = uᴴᴴ := (Matrix.conjTranspose_conjTranspose u).symm
      _ = (s : ℂ) • g⁻¹ᴴ := by rw [huH, Matrix.conjTranspose_smul, hsstar]
  have ht : t = (s : ℂ)⁻¹ • g := by
    have h3 : (s : ℂ) • t = g := by
      calc (s : ℂ) • t = ((s : ℂ) • (1 : Matrix n n ℂ)) * t := by rw [smul_mul_assoc, one_mul]
        _ = g * uᴴ * t := by rw [hg]
        _ = g := by rw [mul_assoc, hut, mul_one]
    rw [← h3, smul_smul, inv_mul_cancel₀ hsC, one_smul]
  have hβu : β * u = (-(η * (s : ℂ))) • (g * M) := by
    rw [hβ, hu, hgM, neg_mul, smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul]
  have hDD : D * Dᴴ = t * tᴴ + (β * u) * (β * u)ᴴ := by
    have step1 : D * Dᴴ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
      calc D * Dᴴ = D * (K₁ * K₁ᴴ + K₂ * K₂ᴴ) * Dᴴ := by rw [hK, mul_one]
        _ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
          simp only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]
    rw [step1, ← h1, ← h2]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hee', one_smul]
  have hmain : D * Dᴴ = ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • (g * (1 + M * M) * gᴴ) := by
    rw [hDD, ht, hβu]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsinvstar, ha']
    rw [← smul_add]
    congr 1
    simp only [Matrix.conjTranspose_mul, hMH, mul_add, add_mul, mul_one, mul_assoc]
  have hdet : D.det * star D.det = t.det * star t.det * (1 + M * M).det := by
    have lhs : D.det * star D.det = (D * Dᴴ).det := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [lhs, hmain, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      ht, Matrix.det_smul, star_mul', star_pow, hsinvstar]
    ring
  rw [← nsq, ← nsq] at hdet
  have hre := congrArg Complex.re hdet
  first
    | (rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre; exact hre)
    | (simpa [Complex.mul_re] using hre)

end GlobalTheory.CompanionTheory.KWhit
