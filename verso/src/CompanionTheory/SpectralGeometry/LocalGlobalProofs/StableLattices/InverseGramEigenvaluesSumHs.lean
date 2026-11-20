import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo

open scoped ComplexOrder in

/- English proof (translation)
Establish `hmul : S7.toM g * S7.toM g⁻¹ = 1` using `by show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective (S7.toM g⁻¹).mulVec`. Introduce `x y hxy`. Establish `h` using `congrArg (S7.toM g).mulVec hxy`.

Simplify `h` using `[Matrix.mulVec_mulVec, hmul]`. Establish `hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef` using `Matrix.PosDef.conjTranspose_mul_self _ hinj`. Use `⟨fun i => hpd.eigenvalues_pos i, ?_⟩` and prove the remaining obligations. Establish `htr` using `hT.trace_eq_sum_eigenvalues`. Establish `hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re`.

Rewrite using `[htr]`. Simplify using the standard rewrite rules. Establish `hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g)`. Rewrite using `[S7.toM_inv]`. Use `show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _`.

Rewrite using `[hs_mul_J, hs_J_mul, hs_conjTranspose]`. Rewrite using `[hre, ← hhs, ← hs_conjTranspose, hs_eq_trace, conjTranspose_conjTranspose]`.
-/
theorem specpos_inv_eigenvalues (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε)
    (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  have hmul : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp
  have hinj : Function.Injective (S7.toM g⁻¹).mulVec := by
    intro x y hxy
    have h := congrArg (S7.toM g).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hmul] using h
  have hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hinj
  refine ⟨fun i => hpd.eigenvalues_pos i, ?_⟩
  have htr := hT.trace_eq_sum_eigenvalues
  have hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re := by
    rw [htr]
    simp
  have hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g) := by
    rw [S7.toM_inv]
    show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _
    rw [hs_mul_J, hs_J_mul, hs_conjTranspose]
  rw [hre, ← hhs, ← hs_conjTranspose, hs_eq_trace, conjTranspose_conjTranspose]

end GlobalTheory.CompanionTheory.UGeo
