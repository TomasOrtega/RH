import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealSeparate
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFormsThroughPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealNeBotDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `F _ n k P Q hP hQ hne hle q hqQ`. Assume the negation of the conclusion as `hqP`. Use `hP.isPrime` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P q) ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hqP (Ideal.Quotient.eq_zero_iff_mem.mp (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))`. Set `x : Fin n → AlgebraicClosure F` to `fun j => φ (Ideal.Quotient.mk P (X j))`. Establish `hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g)`. Introduce `g`.

Establish `h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) = φ.comp (Ideal.Quotient.mkₐ F P)`. Use extensionality with `j`. Simplify using `[x]`. Rewrite using `[h]`. Both sides reduce to the same expression.

Establish `hxq : aeval x q ≠ 0` using `by rw [hev]; exact hφ`. Establish `hx0 : x ≠ 0`. Introduce `h0`. Apply `hxq` to reduce the goal to its premises. Establish `hc : constantCoeff q = 0`.

Assume the negation of the conclusion as `hc`. Establish `hmem` using `hQ.isHomog q hqQ 0`. Rewrite `hmem` using `[homogeneousComponent_zero, ← constantCoeff_eq]`. Conclude with `hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))`. Rewrite using `[h0, aeval_zero, hc, map_zero]`.

Take `⟨u, hux, huQ⟩` from `hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩`. Apply `huQ` to reduce the goal to its premises. Use `hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_` and prove the remaining obligations. Establish `hgP` using `hle hg`. Simplify using `only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP`.

Use `hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩` and prove the remaining obligations. Rewrite using `[hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]`.
-/
theorem IncIdealSeparate.proof (hZ : IncidenceZeroLocus.Statement) (hT : FormsThroughPoint.Statement)
    (hD : IncIdealNeBotDim.Statement) : IncIdealSeparate.Statement := by
  intro F _ n k P Q hP hQ hne hle q hqQ
  by_contra hqP
  have := hP.isPrime

  obtain ⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F,
      φ (Ideal.Quotient.mk P q) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqP (Ideal.Quotient.eq_zero_iff_mem.mp
      (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))
  let x : Fin n → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk P (X j))
  have hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g) := by
    intro g
    have h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) =
        φ.comp (Ideal.Quotient.mkₐ F P) := by
      ext j
      simp [x]
    rw [h]
    rfl
  have hxq : aeval x q ≠ 0 := by rw [hev]; exact hφ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hxq
    have hc : constantCoeff q = 0 := by
      by_contra hc
      have hmem := hQ.isHomog q hqQ 0
      rw [homogeneousComponent_zero, ← constantCoeff_eq] at hmem
      exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))
    rw [h0, aeval_zero, hc, map_zero]

  obtain ⟨u, hux, huQ⟩ := hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩
  apply huQ
  refine hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_
  have hgP := hle hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP
  refine hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩
  rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]

end GroundTheory.Heights₂.Heights
