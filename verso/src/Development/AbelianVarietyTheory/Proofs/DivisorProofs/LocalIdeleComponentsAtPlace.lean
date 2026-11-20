import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCoord

section

open GlobalTheory.SplitGLLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

/- English proof (translation)
Establish `hv : (((Units.map (oneAdd (liftPair h t))).comp MulEquiv.prodUnits.symm.toMonoidHom (y, 1) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 + liftPair h t ((y : Fv F v) - 1, ((1 : (Fv F v)ˣ) : Fv F v) - 1)` using `rfl`. Use `⟨(Units.map (oneAdd (liftPair h t))).comp MulEquiv.prodUnits.symm.toMonoidHom (y, 1), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, map_add, map_one, piW_liftPair, add_sub_cancel]`. Rewrite using `[hv, map_add, map_one, piW_comp_liftPair, add_sub_cancel]`. Both sides reduce to the same expression.

Rewrite using `[hv, add_sub_cancel_left]`. Conclude with `at_liftPair h t _`.
-/
theorem exists_idele (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (y : (Fv F v)ˣ) :
    ∃ s : (AF F ⊗[F] E)ˣ, piW t (s : AF F ⊗[F] E) = y ∧ piW (t.comp σ) (s : AF F ⊗[F] E) = 1 ∧
      At (evFin F v) ((s : AF F ⊗[F] E) - 1) := by
  have hv : (((Units.map (oneAdd (liftPair h t))).comp MulEquiv.prodUnits.symm.toMonoidHom (y, 1) : (AF F ⊗[F] E)ˣ) :
      AF F ⊗[F] E) = 1 + liftPair h t ((y : Fv F v) - 1, ((1 : (Fv F v)ˣ) : Fv F v) - 1) := rfl
  refine ⟨(Units.map (oneAdd (liftPair h t))).comp MulEquiv.prodUnits.symm.toMonoidHom (y, 1), ?_, ?_, ?_⟩
  · rw [hv, map_add, map_one, piW_liftPair, add_sub_cancel]
  · rw [hv, map_add, map_one, piW_comp_liftPair, add_sub_cancel]; rfl
  · rw [hv, add_sub_cancel_left]; exact at_liftPair h t _

/- English proof (translation)
Establish `hN : ∀ z : Fv F v ⊗[F] E, Algebra.norm (Fv F v) z = splitProj t z * splitProj (t.comp σ) z` using `fun z => by`. Use `congrArg (splitProj t) (GlobalTheory.Doubling.algebraMap_norm_eq h z)` as an intermediate fact. Rewrite `this` using `[AlgHom.commutes, map_mul, ← splitProj_comp]`. Conclude with `this`. Rewrite using `[absE_of_mem (v := v) (mem_idelesAt.2 h3), GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_mul, ← ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 y).1]`.

Conclude with `(congrArg₂ (fun p q : Fv F v => ‖p‖ * ‖q‖) h1 h2).trans (by simp)`.
-/
theorem absE_eq (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (s : (AF F ⊗[F] E)ˣ) (y : (Fv F v)ˣ)
    (h1 : piW t (s : AF F ⊗[F] E) = y) (h2 : piW (t.comp σ) (s : AF F ⊗[F] E) = 1)
    (h3 : At (evFin F v) ((s : AF F ⊗[F] E) - 1)) : (absE F E s : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) y := by
  have hN : ∀ z : Fv F v ⊗[F] E, Algebra.norm (Fv F v) z = splitProj t z * splitProj (t.comp σ) z := fun z => by
    have := congrArg (splitProj t) (GlobalTheory.Doubling.algebraMap_norm_eq h z)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  rw [absE_of_mem (v := v) (mem_idelesAt.2 h3), GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_mul,
    ← ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 y).1]
  exact (congrArg₂ (fun p q : Fv F v => ‖p‖ * ‖q‖) h1 h2).trans (by simp)

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ v hv w hw`. Take `⟨τ⟩` from `GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully F E σ hσ v hv`. Take `⟨t, rfl⟩` from `GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hw`. Set `e : ((splitPrime t).adicCompletion E)ˣ →* (Fv F v)ˣ` to `Units.map (GlobalTheory.LFun.SplitTie.complEquiv t (splitPrime_under t)).symm.toMonoidHom`. Establish `he : ∀ x, Units.map (GlobalTheory.LFun.complMap (splitPrime_under t)).toMonoidHom (e x) = x` using `fun x => Units.ext ((GlobalTheory.LFun.SplitTie.complEquiv t (splitPrime_under t)).apply_symm_apply (x : (splitPrime t).adicCompletion E))`.

Establish `key : ∀ x, piW t ((locIdele F (splitPrime t) x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (e x : Fv F v) ∧ piW (t.comp σ) ((locIdele F (splitPrime t) x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 ∧ At (evFin F v) (((locIdele F (splitPrime t) x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1)` using `fun x => by`. Take `⟨s, h1, h2, h3⟩` from `exists_idele hσ t (e x)`. Establish `a` using `GlobalTheory.ChrLocal.eq_locIdele_splitPrime hσ t s h3 h2`. Establish `hp : Units.map (piW t).toMonoidHom s = e x` using `Units.ext h1`. Rewrite `a` using `[hp, he]`.

Rewrite using `[← a]`. Conclude with `⟨h1, h2, h3⟩`. Use `⟨t, fun x => e x, fun x => (key x).1, fun x => (key x).2.1, fun x => (key x).2.2, ?_, ?_⟩` and prove the remaining obligations. Introduce `χ x`. Express the relevant statement in the definitionally equal form `((Circle.toUnits (χ (locIdele F (splitPrime t) (Units.map _ (e x))))) : ℂ) = _`.

Rewrite using `[he]`. Both sides reduce to the same expression. Introduce `x z`. Rewrite using `[absE_eq hσ t _ (e x) (key x).1 (key x).2.1 (key x).2.2]`. Both sides reduce to the same expression.
-/
theorem local_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
  ∃ (t : E →ₐ[F] Fv F v) (e : (w.adicCompletion E)ˣ → (Fv F v)ˣ),
    (∀ x, piW t ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (e x : Fv F v)) ∧
    (∀ x, piW (t.comp σ) ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1) ∧
    (∀ x, At (evFin F v) (((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1)) ∧
    (∀ (χ : Chr F E) x, ((chrW χ t (e x) : ℂˣ) : ℂ) = (χ (locIdele F w x) : ℂ)) ∧
    ∀ x (z : ℂ), GlobalTheory.SplitFlip.apow (e x) z = (((absE F E (locIdele F w x) : ℝ≥0) : ℝ) : ℂ) ^ z := by
  intro F E _ _ _ _ _ σ hσ v hv w hw
  obtain ⟨τ⟩ := GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully F E σ hσ v hv
  obtain ⟨t, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hw
  let e : ((splitPrime t).adicCompletion E)ˣ →* (Fv F v)ˣ :=
    Units.map (GlobalTheory.LFun.SplitTie.complEquiv t (splitPrime_under t)).symm.toMonoidHom
  have he : ∀ x, Units.map (GlobalTheory.LFun.complMap (splitPrime_under t)).toMonoidHom (e x) = x := fun x =>
    Units.ext ((GlobalTheory.LFun.SplitTie.complEquiv t (splitPrime_under t)).apply_symm_apply
      (x : (splitPrime t).adicCompletion E))
  have key : ∀ x, piW t ((locIdele F (splitPrime t) x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (e x : Fv F v) ∧
      piW (t.comp σ) ((locIdele F (splitPrime t) x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 ∧
      At (evFin F v) (((locIdele F (splitPrime t) x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := fun x => by
    obtain ⟨s, h1, h2, h3⟩ := exists_idele hσ t (e x)
    have a := GlobalTheory.ChrLocal.eq_locIdele_splitPrime hσ t s h3 h2
    have hp : Units.map (piW t).toMonoidHom s = e x := Units.ext h1
    rw [hp, he] at a
    rw [← a]
    exact ⟨h1, h2, h3⟩
  refine ⟨t, fun x => e x, fun x => (key x).1, fun x => (key x).2.1, fun x => (key x).2.2, ?_, ?_⟩
  · intro χ x
    change ((Circle.toUnits (χ (locIdele F (splitPrime t) (Units.map _ (e x))))) : ℂ) = _
    rw [he]
    rfl
  · intro x z
    rw [absE_eq hσ t _ (e x) (key x).1 (key x).2.1 (key x).2.2]
    rfl

end GlobalTheory.SplitCoord
