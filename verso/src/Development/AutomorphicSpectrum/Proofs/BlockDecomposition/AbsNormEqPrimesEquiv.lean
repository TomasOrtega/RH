import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

open NumberField IsDedekindDomain GroundTheory.LocalField GroundTheory.Global
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.Rgads

/- English proof (translation)
Establish `e` using `Ideal.quotientEquiv p.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (Rat.HeightOneSpectrum.span_natGenerator p)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv]`. Use `Ideal.absNorm_span_singleton ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : ℤ)` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite using `[this]`.

Simplify using `only [Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]`. Both sides reduce to the same expression.
-/
theorem absNorm_eq_primesEquiv (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm p.asIdeal = (Rat.HeightOneSpectrum.primesEquiv p : ℕ) := by
  have e := Ideal.quotientEquiv p.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    (Rat.HeightOneSpectrum.span_natGenerator p)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv]
  have := Ideal.absNorm_span_singleton ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : ℤ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  rw [this]
  simp only [Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]
  rfl

/- English proof (translation)
Use `⟨⟨Rat.HeightOneSpectrum.primesEquiv, fun v => (absNorm_eq_primesEquiv v).symm⟩, fun v μ h s => ?_⟩` and prove the remaining obligations. Rewrite using `[localLFactor_of_isUnramified h, residueCard_adicCompletion]`. Both sides reduce to the same expression.
-/
theorem e1b : faceMap_comp_succAbove_castSucc := by
  refine ⟨⟨Rat.HeightOneSpectrum.primesEquiv, fun v => (absNorm_eq_primesEquiv v).symm⟩,
    fun v μ h s => ?_⟩
  rw [localLFactor_of_isUnramified h, residueCard_adicCompletion]
  rfl

end GlobalTheory.CompanionTheory.Rgads
