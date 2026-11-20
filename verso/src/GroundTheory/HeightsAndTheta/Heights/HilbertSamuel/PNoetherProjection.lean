import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNoetherProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

/- English proof (translation)
Introduce `σ _ P hP`. Establish `: Nontrivial (MvPolynomial σ ℚ ⧸ P)` using `Ideal.Quotient.nontrivial_iff.mpr hP`. Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ P)`. Use `choose ℓ hℓ using fun j => Ideal.Quotient.mk_surjective (g (X j))`. Establish `hcomp : (Ideal.Quotient.mkₐ ℚ P).comp (aeval ℓ) = g`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`. Simplify using `[hℓ]`. Establish `hcompR : (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom = g.toRingHom`. Rewrite using `[← hcomp]`.

Both sides reduce to the same expression. Use `⟨s, ℓ, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hq]`.

Introduce `f`. Take `⟨p, hpm, hp⟩` from `hint (Ideal.Quotient.mk P f)`. Use `⟨p, hpm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, hcompR]`. Conclude with `hp`.
-/
theorem NoetherProjection.proof : NoetherProjection.Statement := by
  intro σ _ P hP
  have : Nontrivial (MvPolynomial σ ℚ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ P)
  choose ℓ hℓ using fun j => Ideal.Quotient.mk_surjective (g (X j))
  have hcomp : (Ideal.Quotient.mkₐ ℚ P).comp (aeval ℓ) = g := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [hℓ]
  have hcompR : (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom = g.toRingHom := by
    rw [← hcomp]
    rfl
  refine ⟨s, ℓ, ?_, ?_⟩
  · intro q hq
    apply hinj
    rw [map_zero, ← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · intro f
    obtain ⟨p, hpm, hp⟩ := hint (Ideal.Quotient.mk P f)
    refine ⟨p, hpm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, hcompR]
    exact hp

end GroundTheory.Heights₂.Heights.HilbertSamuel
