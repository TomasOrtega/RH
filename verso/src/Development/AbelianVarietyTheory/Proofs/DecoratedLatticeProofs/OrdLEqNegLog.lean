import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.AbsInert

/- English proof (translation)
Unfold `ordL`. Rewrite using `[dif_neg hy, WithZero.toAdd_unzero_eq_log]`.
-/
theorem ordL_eq_neg_log {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {y : L}
    (hy : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ))) : ordL y = -WithZero.log (Valued.v y) := by
  unfold ordL
  rw [dif_neg hy, WithZero.toAdd_unzero_eq_log]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ v w h hw x`. Use `set N : Fv F v := Algebra.norm (Fv F v) x.1 with hNdef`. Use `set z : w.adicCompletion E := toCompl h x.1 with hzdef`. Establish `hN0 : N ≠ 0` using `((x.isUnit.map (Algebra.norm (Fv F v))).ne_zero)`. Establish `hz0 : z ≠ 0` using `(x.isUnit.map (toCompl h)).ne_zero`.

Establish `key` using `GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x.1`. Establish `key'` using `congrArg (toCompl h) key`. Rewrite `key'` using `[map_mul]`. Establish `hl : toCompl h (algebraMap (Fv F v) (Fv F v ⊗[F] E) N) = GlobalTheory.LFun.complMap h N`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`.

Rewrite `key'` using `[hl]`. Set `c : w.adicCompletion E →+* w.adicCompletion E` to `(GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (((sigR (Fv F v) σ : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E)).comp (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom)`. Establish `he : ∀ t, GlobalTheory.LFun.InertChart.complEquiv hw h t = toCompl h t` using `fun _ => rfl`. Establish `hs : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm z = x.1`. Rewrite using `[RingEquiv.symm_apply_eq, he]`.

Establish `hcz : c z = toCompl h (sigR (Fv F v) σ x.1)` using `by show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) = _`. Rewrite using `[hs, he]`. Establish `hc : GlobalTheory.LFun.IsConjAt σ h c`. Unfold `GlobalTheory.LFun.IsConjAt`. Introduce `t`.

Use `show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (toCompl h t))) = _`. Rewrite using `[← he t, RingEquiv.symm_apply_apply, he]`. Take `⟨ϖ, hU⟩` from `GlobalTheory.LFun.InertChart.exists_isUnramInv hσ hw hc`. Establish `hvc : Valued.v (toCompl h (sigR (Fv F v) σ x.1)) = Valued.v z`. Rewrite using `[← hcz]`.

Conclude with `hU.2.1 z`. Establish `he1 : w.asIdeal.ramificationIdx (𝓞 F) = 1` using `GlobalTheory.LFun.isUnram_iff.mp (GlobalTheory.LFun.isUnram_of_isInertAt hw) w h`. Establish `hvN : Valued.v N = Valued.v z ^ 2`. Establish `hv` using `GlobalTheory.LFun.valued_complMap h hN0`. Rewrite `hv` using `[he1, pow_one, key', map_mul, hvc]`.

Rewrite using `[sq]`. Conclude with `hv.symm`. Establish `hz' : Valued.v z ≠ 0` using `(Valuation.ne_zero_iff _).mpr hz0`. Establish `hN' : Valued.v N ≠ 0` using `(Valuation.ne_zero_iff _).mpr hN0`. Rewrite using `[GlobalTheory.Doubling.absEv_apply, coe_nnnorm]`.

Use `show ‖N‖ = _`. Rewrite using `[NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hN', WithZero.toAdd_unzero_eq_log, hvN, WithZero.log_pow, ordL_eq_neg_log (y := toCompl h x.1) hz']`. Establish `hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) = (qV F v : ℝ)` using `by simp [qV]`. Rewrite using `[NNReal.coe_zpow, hq]`. Use `congr 1`.

Rewrite using `[nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem absEv_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV F v : ℝ) ^ (-(2 * ordL (toCompl h x.1))) := by
  intro F E _ _ _ _ _ σ hσ v w h hw x

  set N : Fv F v := Algebra.norm (Fv F v) x.1 with hNdef
  set z : w.adicCompletion E := toCompl h x.1 with hzdef
  have hN0 : N ≠ 0 := ((x.isUnit.map (Algebra.norm (Fv F v))).ne_zero)
  have hz0 : z ≠ 0 := (x.isUnit.map (toCompl h)).ne_zero

  have key := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x.1
  have key' := congrArg (toCompl h) key
  rw [map_mul] at key'
  have hl : toCompl h (algebraMap (Fv F v) (Fv F v ⊗[F] E) N) = GlobalTheory.LFun.complMap h N := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [hl] at key'

  let c : w.adicCompletion E →+* w.adicCompletion E :=
    (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp
      (((sigR (Fv F v) σ : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E)).comp (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom)
  have he : ∀ t, GlobalTheory.LFun.InertChart.complEquiv hw h t = toCompl h t := fun _ => rfl
  have hs : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm z = x.1 := by
    rw [RingEquiv.symm_apply_eq, he]
  have hcz : c z = toCompl h (sigR (Fv F v) σ x.1) := by
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) = _
    rw [hs, he]
  have hc : GlobalTheory.LFun.IsConjAt σ h c := by
    unfold GlobalTheory.LFun.IsConjAt
    intro t
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (toCompl h t))) = _
    rw [← he t, RingEquiv.symm_apply_apply, he]

  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hσ hw hc
  have hvc : Valued.v (toCompl h (sigR (Fv F v) σ x.1)) = Valued.v z := by
    rw [← hcz]
    exact hU.2.1 z

  have he1 : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    GlobalTheory.LFun.isUnram_iff.mp (GlobalTheory.LFun.isUnram_of_isInertAt hw) w h
  have hvN : Valued.v N = Valued.v z ^ 2 := by
    have hv := GlobalTheory.LFun.valued_complMap h hN0
    rw [he1, pow_one, key', map_mul, hvc] at hv
    rw [sq]
    exact hv.symm
  have hz' : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hN' : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).mpr hN0

  rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  show ‖N‖ = _
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hN', WithZero.toAdd_unzero_eq_log,
    hvN, WithZero.log_pow, ordL_eq_neg_log (y := toCompl h x.1) hz']
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) = (qV F v : ℝ) := by simp [qV]
  rw [NNReal.coe_zpow, hq]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.AbsInert

end
