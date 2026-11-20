import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `n m P Q hP`. Use `set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P := (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ`. Establish `: P.IsPrime` using `hP`. Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Take `⟨s, hs1, hs2⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)`.

Take `⟨t, ht1, ht2⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)`. Establish `hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤ Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P)` using `trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)`. Rewrite `hle` using `[hs2, ht2]`. Establish `hst : s ≤ t` using `by exact_mod_cast hle`. Rewrite using `[hs1, ht1]`.

Conclude with `hst` after adjusting the coercions.
-/
theorem ImageDimLe.proof : ImageDimLe.Statement := by
  intro n m P Q hP
  set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ
  have : P.IsPrime := hP
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)
  obtain ⟨t, ht1, ht2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)
  have hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤
      Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  rw [hs2, ht2] at hle
  have hst : s ≤ t := by exact_mod_cast hle
  rw [hs1, ht1]
  exact_mod_cast hst

end

end GroundTheory.Heights₂.Heights
