import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

noncomputable def spOf (γ : GL (Fin r) E) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ :=
  Matrix.of fun p q => crd X bas (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
    ((bas (Pi.single p.swap 1) : X.Λ) : Fin r → E)) q.swap

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.
-/
theorem gl_mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

variable {X bas}

/- English proof (translation)
Establish `hent : ∀ a b, ∑ c, ∑ d, (γ : Matrix (Fin r) (Fin r) E) c a * X.Gm c d * cc ((γ : Matrix (Fin r) (Fin r) E) d b) = X.Gm a b`. Introduce `a b`. Establish `h` using `hγ (Pi.single a 1) (Pi.single b 1)`. Simplify `h` using `[herm, Matrix.mulVec, dotProduct, Pi.single_apply, cc]`. Establish `key : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1`.

Introduce `τ`. Use extensionality with `a b`. Establish `h` using `congrArg τ.1 (hent a b)`. Simplify using `only [map_sum, map_mul, cc, NumberField.IsCMField.complexEmbedding_complexConj] at h`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `h`. Establish `hgram : ∀ (τ : X.Ψ) (m : Matrix (Fin r) (Fin r) ℂ), gram τ.1 X.Gm m = mᵀ * X.Gm.map τ.1 * m.map (starRingEnd ℂ)`. Introduce `τ m`. Use extensionality with `a b`.

Simplify using `only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hmat : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ)`. Introduce `τ`. Establish `hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ` using `rfl`.

Rewrite using `[hm, hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `τ`. Take `⟨hdet, hpos⟩` from `hx τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations.

Establish `hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ` using `rfl`. Rewrite using `[hm, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `mul_ne_zero ((map_ne_zero τ.1).mpr (Matrix.isUnits_det_units γ).ne_zero) hdet`. Simplify `hpos i` using `only [dmin, hmat τ]`.
-/
theorem IsUn.lact_mem {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by

  have hent : ∀ a b, ∑ c, ∑ d, (γ : Matrix (Fin r) (Fin r) E) c a * X.Gm c d *
      cc ((γ : Matrix (Fin r) (Fin r) E) d b) = X.Gm a b := by
    intro a b
    have h := hγ (Pi.single a 1) (Pi.single b 1)
    simpa [herm, Matrix.mulVec, dotProduct, Pi.single_apply, cc] using h

  have key : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    intro τ
    ext a b
    have h := congrArg τ.1 (hent a b)
    simp only [map_sum, map_mul, cc, NumberField.IsCMField.complexEmbedding_complexConj] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact h

  have hgram : ∀ (τ : X.Ψ) (m : Matrix (Fin r) (Fin r) ℂ),
      gram τ.1 X.Gm m = mᵀ * X.Gm.map τ.1 * m.map (starRingEnd ℂ) := by
    intro τ m
    ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmat : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    intro τ
    have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [hm, hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    calc (mat x τ)ᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
          (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) *
            (mat x τ).map (starRingEnd ℂ))
        = (mat x τ)ᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) *
            (mat x τ).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
      _ = (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by rw [key]
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  refine ⟨?_, fun i => ?_⟩
  · have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [hm, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero τ.1).mpr (Matrix.isUnits_det_units γ).ne_zero) hdet
  · simpa only [dmin, hmat τ] using hpos i

/- English proof (translation)
Establish `hinv : ∀ u v : Fin r → E, EF X (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF X u v`. Introduce `u v`. Establish `h` using `hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)`. Rewrite `h` using `[gl_mulVec_inv_mulVec, gl_mulVec_inv_mulVec]`. Rewrite using `[EF_def, EF_def, h]`.

Establish `hrow : ∀ p p' : Fin g ⊕ Fin g, ∑ i, (spOf X bas γ p (Sum.inr i) * spOf X bas γ p' (Sum.inl i) - spOf X bas γ p (Sum.inl i) * spOf X bas γ p' (Sum.inr i)) = ((omegaStd (Pi.single p.swap 1 : Fin g ⊕ Fin g → ℤ) (Pi.single p'.swap 1) : ℤ) : ℚ)`. Introduce `p p'`. Establish `h` using `hinv (bas (Pi.single p.swap 1)) (bas (Pi.single p'.swap 1))`. Rewrite `h` using `[EF_crd hs, hs]`. Simplify using `only [spOf, Matrix.of_apply, Sum.swap_inl, Sum.swap_inr]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[SymplecticGroup.mem_iff]`. Use extensionality with `p p'`. Establish `hJl : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inl j) = spOf X bas γ p (Sum.inr j)`. Introduce `j`.

Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]`. Establish `hJr : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inr j) = -spOf X bas γ p (Sum.inl j)`. Introduce `j`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]`. Rewrite using `[Matrix.mul_apply, Fintype.sum_sum_type]`.

Simplify using `only [hJl, hJr, Matrix.transpose_apply, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]`. Rewrite using `[hrow]`. Apply the tactic sequence `rcases p with i | i <;> rcases p' with j | j <;>`. Simplify using `[omegaStd, Pi.single_apply, Matrix.J, Matrix.one_apply, eq_comm]`.
-/
theorem spOf_mem (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    spOf X bas γ ∈ Matrix.symplecticGroup (Fin g) ℚ := by

  have hinv : ∀ u v : Fin r → E, EF X (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF X u v := by
    intro u v
    have h := hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
    rw [gl_mulVec_inv_mulVec, gl_mulVec_inv_mulVec] at h
    rw [EF_def, EF_def, h]

  have hrow : ∀ p p' : Fin g ⊕ Fin g,
      ∑ i, (spOf X bas γ p (Sum.inr i) * spOf X bas γ p' (Sum.inl i) -
        spOf X bas γ p (Sum.inl i) * spOf X bas γ p' (Sum.inr i)) =
      ((omegaStd (Pi.single p.swap 1 : Fin g ⊕ Fin g → ℤ) (Pi.single p'.swap 1) : ℤ) : ℚ) := by
    intro p p'
    have h := hinv (bas (Pi.single p.swap 1)) (bas (Pi.single p'.swap 1))
    rw [EF_crd hs, hs] at h
    simp only [spOf, Matrix.of_apply, Sum.swap_inl, Sum.swap_inr]
    linarith
  rw [SymplecticGroup.mem_iff]
  ext p p'
  have hJl : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inl j) = spOf X bas γ p (Sum.inr j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  have hJr : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inr j) = -spOf X bas γ p (Sum.inl j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hJl, hJr, Matrix.transpose_apply, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    ← Finset.sum_sub_distrib]
  rw [hrow]
  rcases p with i | i <;> rcases p' with j | j <;>
    simp [omegaStd, Pi.single_apply, Matrix.J, Matrix.one_apply, eq_comm]

/- English proof (translation)
Establish `hsym` using `tauMat_isSymm (idx := idx) hs hx`. Use extensionality with `i k`. Establish `hcol : (fun l => perMat X bas idx s (lact γ x) l k) = per X x (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)) ∘ idx`. Use function extensionality and compare the values at `l`. Rewrite using `[perMat_apply, Function.comp_apply, ← per_lact x hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)), gl_mulVec_inv_mulVec]`.

Establish `hlhs : (hMat X bas idx x * perMat X bas idx s (lact γ x)) i k = (hMat X bas idx x *ᵥ fun l => perMat X bas idx s (lact γ x) l k) i`. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[hlhs, hcol, hMat_mulVec_per_crd (idx := idx) hs hx]`. Simplify using `only [spOf, qm, qv, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, Pi.add_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Sum.swap_swap, Sum.swap_inl, Sum.swap_inr]`. Rewrite using `[add_comm]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsym.apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hMat_mul_perMat_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : Fin g → Fin g ⊕ Fin g) :
    hMat X bas idx x * perMat X bas idx s (lact γ x) =
      (qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inl j)) * tauMat X bas idx x +
        qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inr j)))ᵀ := by
  have hsym := tauMat_isSymm (idx := idx) hs hx
  ext i k
  have hcol : (fun l => perMat X bas idx s (lact γ x) l k) =
      per X x (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)) ∘ idx := by
    funext l
    rw [perMat_apply, Function.comp_apply,
      ← per_lact x hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)), gl_mulVec_inv_mulVec]
  have hlhs : (hMat X bas idx x * perMat X bas idx s (lact γ x)) i k =
      (hMat X bas idx x *ᵥ fun l => perMat X bas idx s (lact γ x) l k) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hlhs, hcol, hMat_mulVec_per_crd (idx := idx) hs hx]
  simp only [spOf, qm, qv, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, Pi.add_apply,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Sum.swap_swap, Sum.swap_inl,
    Sum.swap_inr]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym.apply]
  ring

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs _ γ hγ`. Use `⟨spOf X bas γ, spOf_mem hs hγ, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx'` using `IsUn.lact_mem hγ hx`. Establish `hD : hMat X bas idx x * perMat X bas idx Sum.inl (lact γ x) = (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ` using `hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inl`. Establish `hN : hMat X bas idx x * perMat X bas idx Sum.inr (lact γ x) = (qm (spOf X bas γ).toBlocks₁₁ * tauMat X bas idx x + qm (spOf X bas γ).toBlocks₁₂)ᵀ` using `hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inr`.

Establish `hH` using `isUnit_det_hMat (idx := idx) hs hx`. Establish `hP` using `isUnit_det_perMat (idx := idx) hs hx'`. Establish `hPeq : perMat X bas idx Sum.inl (lact γ x) = (hMat X bas idx x)⁻¹ * (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ`. Rewrite using `[← hD, Matrix.nonsing_inv_mul_cancel_left _ _ hH]`. Establish `hh : hMat X bas idx (lact γ x) = ((spDen (spOf X bas γ) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x`.

Express the relevant statement in the definitionally equal form `(perMat X bas idx Sum.inl (lact γ x))⁻¹ = _`. Rewrite using `[hPeq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hH, Matrix.transpose_nonsing_inv]`. Use `⟨hx', ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩, ?_, hh⟩` and prove the remaining obligations. Establish `ht : tauMat X bas idx (lact γ x) = (spAct (spOf X bas γ) (tauMat X bas idx x))ᵀ`. Express the relevant statement in the definitionally equal form `hMat X bas idx (lact γ x) * perMat X bas idx Sum.inr (lact γ x) = _`.

Rewrite using `[hh, Matrix.mul_assoc, hN, spAct, Matrix.transpose_mul]`. Establish `hsym` using `tauMat_isSymm (idx := idx) hs hx'`. Rewrite using `[← hsym, ht, Matrix.transpose_transpose]`.
-/
theorem periods_lact_symplectic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∃ σ ∈ Matrix.symplecticGroup (Fin g) ℚ, ∀ x ∈ X.dom, lact γ x ∈ X.dom ∧ tauMat X bas idx x ∈ Siegel (Fin g) ∧ tauMat X bas idx (lact γ x) = spAct σ (tauMat X bas idx x) ∧ hMat X bas idx (lact γ x) = ((spDen σ (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
  intro E _ _ _ r X g bas idx n hs _ γ hγ
  refine ⟨spOf X bas γ, spOf_mem hs hγ, fun x hx => ?_⟩
  have hx' := IsUn.lact_mem hγ hx
  have hD : hMat X bas idx x * perMat X bas idx Sum.inl (lact γ x) =
      (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inl
  have hN : hMat X bas idx x * perMat X bas idx Sum.inr (lact γ x) =
      (qm (spOf X bas γ).toBlocks₁₁ * tauMat X bas idx x + qm (spOf X bas γ).toBlocks₁₂)ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inr
  have hH := isUnit_det_hMat (idx := idx) hs hx
  have hP := isUnit_det_perMat (idx := idx) hs hx'
  have hPeq : perMat X bas idx Sum.inl (lact γ x) =
      (hMat X bas idx x)⁻¹ * (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    rw [← hD, Matrix.nonsing_inv_mul_cancel_left _ _ hH]
  have hh : hMat X bas idx (lact γ x) =
      ((spDen (spOf X bas γ) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
    change (perMat X bas idx Sum.inl (lact γ x))⁻¹ = _
    rw [hPeq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hH, Matrix.transpose_nonsing_inv]
  refine ⟨hx', ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩, ?_, hh⟩
  have ht : tauMat X bas idx (lact γ x) = (spAct (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    change hMat X bas idx (lact γ x) * perMat X bas idx Sum.inr (lact γ x) = _
    rw [hh, Matrix.mul_assoc, hN, spAct, Matrix.transpose_mul]
  have hsym := tauMat_isSymm (idx := idx) hs hx'
  rw [← hsym, ht, Matrix.transpose_transpose]

end GlobalTheory.SW
