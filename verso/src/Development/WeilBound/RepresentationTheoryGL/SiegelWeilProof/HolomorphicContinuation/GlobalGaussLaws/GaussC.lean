import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussB

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `inG_rel hg`. Establish `h3' : g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = 1`. Use `congrArg conjTranspose h3` as an intermediate fact. Simplify `this` using `[conjTranspose_sub, conjTranspose_mul]`. Establish `key : (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) - (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) = Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂) - (g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂ …`.

Simplify using `only [conjTranspose_add, conjTranspose_mul]`. Use `noncomm_ring`. Rewrite using `[key, h3, h3', h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem identG {g : M2 n} (hg : InG g) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) = Xᴴ - Y := by
  obtain ⟨h1, h2, h3⟩ := inG_rel hg
  have h3' : g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = 1 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have key : (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) =
      Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂) -
        (g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁) * Y +
        Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁) * Y +
        (g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [key, h3, h3', h1, h2]
  simp

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hdet`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `hid` using `identG hg Z Z`. Establish `h0 : star v ⬝ᵥ ((Zᴴ - Z) *ᵥ v) = 0`.

Rewrite using `[← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]`. Simplify using the standard rewrite rules. Establish `h0' : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0`. Rewrite using `[← neg_sub, neg_mulVec, dotProduct_neg, h0, neg_zero]`. Establish `hpos` using `Matrix.PosDef.dotProduct_mulVec_pos hZ hv`.

Rewrite `hpos` using `[smul_mulVec, dotProduct_smul, h0', smul_zero]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem det_CZD {g : M2 n} (hg : InG g) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hid := identG hg Z Z
  have h0 : star v ⬝ᵥ ((Zᴴ - Z) *ᵥ v) = 0 := by
    rw [← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub,
      dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have h0' : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← neg_sub, neg_mulVec, dotProduct_neg, h0, neg_zero]
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
  rw [smul_mulVec, dotProduct_smul, h0', smul_zero] at hpos
  exact lt_irrefl _ hpos

end PositivityTheory.Rg.Sw.Glob.GaussH
