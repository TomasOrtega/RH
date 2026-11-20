import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open NumberField Topology

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
The claim follows from `(continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp continuous_fst`.
-/
theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

omit [IsTotallyComplex E] in

/- English proof (translation)
The claim follows from `continuous_snd`.
-/
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)`.
-/
theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

omit [IsTotallyComplex E] in

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)`.
-/
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Establish `hmul : Continuous fun g : GA E a => g₀⁻¹ * g` using `continuous_const.mul continuous_id`. Establish `hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀`. Use `(h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)` using `by filter_upwards [hN] with g hg`. Rewrite using `[chart_val]`. Establish `hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x` using `fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg`. Use `conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]`.

Use `ContinuousAt.congr ?_ heq.symm` and prove the remaining obligations. Establish `hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val)` using `(contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt`. Conclude with `ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt`.
-/
theorem IsAutForm.continuous {φ : Sm E a} (h : IsAutForm φ) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hmul : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ := by
    refine (h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_
    simp
  have heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
    filter_upwards [hN] with g hg
    rw [chart_val]
    have hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x :=
      fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg
    conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt
  exact ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc
    (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt

end GlobalTheory.CuspRep
