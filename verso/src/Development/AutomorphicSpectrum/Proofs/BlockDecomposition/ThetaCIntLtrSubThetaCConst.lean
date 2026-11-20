import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecayStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSumStatement
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ThcInt

/- English proof (translation)
Simplify using `only [scalC, map_mul]`.
-/
theorem scalC_mul (a b : IdeleGroup k) :
    (scalC (a * b) : GL ι 𝔸[k]) = scalC a * scalC b := by
  simp only [scalC, map_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, scalC, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Conclude with `(Matrix.scalar_commute _ (fun r ↦ Commute.all _ r) _)`.
-/
theorem scalC_commute (a : IdeleGroup k) (A : GL ι 𝔸[k]) :
    (scalC a : GL ι 𝔸[k]) * A = A * scalC a := by
  apply Units.ext
  simp only [Units.val_mul, scalC, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r) _)

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Use `continuous_matrix fun i j ↦ ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify `continuous_id'` using `[Matrix.scalar_apply]`.

Simplify `continuous_const` using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]`.
-/
theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  refine Continuous.units_map _ ?_
  refine continuous_matrix fun i j ↦ ?_
  by_cases h : i = j
  · subst h
    simpa [Matrix.scalar_apply] using continuous_id'
  · simpa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h] using continuous_const

/- English proof (translation)
Simplify using `only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]`.
-/
theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Simplify using `[ltr]`.
-/
theorem ltr_apply_zero (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : ltr A F 0 = F 0 := by
  simp [ltr]

/- English proof (translation)
Take `⟨u, hu, hb⟩` from `GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC`. Use `continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hb h hh ξ` and prove the remaining obligations. Use `(continuous_of_mem_schwartzBruhatPi hF).comp ?_` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_mulVec continuous_const`.
-/
theorem continuousOn_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) : ContinuousOn (thetaC F) C := by
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hb h hh ξ
  refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
  exact Units.continuous_val.matrix_mulVec continuous_const

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)`.
-/
theorem continuous_char (ω : HeckeCharacter k) :
    Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
  continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)

/- English proof (translation)
Establish `hE` using `isCompact_closure_normOneFundamentalDomain k`. Establish `hφ : Continuous fun u : normOneSubgroup k ↦ A * (scalC (s * (u : IdeleGroup k)) : GL ι 𝔸[k])` using `continuous_const.mul (continuous_scalC.comp (continuous_const.mul continuous_subtype_val))`. Establish `h1 : ContinuousOn (fun u : normOneSubgroup k ↦ thetaC (ltr A F) (scalC (s * (u : IdeleGroup k)))) (closure (normOneFundamentalDomain k))`. Simplify using `only [thetaC_ltr]`. Conclude with `(continuousOn_thetaC hF (hE.image hφ)).comp hφ.continuousOn (Set.mapsTo_image _ _)`.

Conclude with `((h1.mul (continuous_char ω).continuousOn).integrableOn_compact hE).mono_set subset_closure`.
-/
theorem integrableOn_thetaCIntegrand {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (A : GL ι 𝔸[k]) (ω : HeckeCharacter k) (s : IdeleGroup k) :
    IntegrableOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hφ : Continuous fun u : normOneSubgroup k ↦
      A * (scalC (s * (u : IdeleGroup k)) : GL ι 𝔸[k]) :=
    continuous_const.mul (continuous_scalC.comp (continuous_const.mul continuous_subtype_val))
  have h1 : ContinuousOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))))
      (closure (normOneFundamentalDomain k)) := by
    simp only [thetaC_ltr]
    exact (continuousOn_thetaC hF (hE.image hφ)).comp hφ.continuousOn (Set.mapsTo_image _ _)
  exact ((h1.mul (continuous_char ω).continuousOn).integrableOn_compact hE).mono_set subset_closure

/- English proof (translation)
The claim follows from `((continuous_char ω).continuousOn.integrableOn_compact (isCompact_closure_normOneFundamentalDomain k)).mono_set subset_closure`.
-/
theorem integrableOn_char' (ω : HeckeCharacter k) :
    IntegrableOn (fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) :=
  ((continuous_char ω).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain k)).mono_set subset_closure

/- English proof (translation)
Rewrite using `[thetaCInt, thetaCConst, volChar, ← integral_const_mul, ← integral_sub (integrableOn_thetaCIntegrand hF A ω _) ((integrableOn_char' ω).const_mul _)]`. Use `integral_congr_ae (Eventually.of_forall fun u ↦ ?_)` and prove the remaining obligations. Simplify using `only []`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaCInt_ltr_sub_thetaCConst (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (A : GL ι 𝔸[k]) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) :
    thetaCInt w (ltr A F) ω t - thetaCConst (ltr A F) ω =
      ∫ u in normOneFundamentalDomain k,
        (thetaC (ltr A F) (scalC (moduleSection w t * (u : IdeleGroup k))) - ltr A F 0) *
          (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k := by
  rw [thetaCInt, thetaCConst, volChar, ← integral_const_mul,
    ← integral_sub (integrableOn_thetaCIntegrand hF A ω _) ((integrableOn_char' ω).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only []
  ring

end ThcInt

open ThcInt in

/- English proof (translation)
Establish `hE` using `isCompact_closure_normOneFundamentalDomain k`. Establish `hS : Continuous fun p : normOneSubgroup k × GL ι 𝔸[k] ↦ p.2 * (scalC (p.1 : IdeleGroup k) : GL ι 𝔸[k])` using `continuous_snd.mul (continuous_scalC.comp (continuous_subtype_val.comp continuous_fst))`. Take `⟨M, hM⟩` from `GlobalTheory.T.theta_sub_value_zero_rapid_decay w hΨ ((hE.prod hC).image hS) r`. Use `⟨M * (normOneMeasure k).real (normOneFundamentalDomain k), fun A hA t ht ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[thetaCInt_ltr_sub_thetaCConst w hΨ A ω t, ← mul_assoc]`.

Use `norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top k) fun u hu ↦ ?_` and prove the remaining obligations. Establish `hc : A * (scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) = scalC (moduleSection w t) * (A * scalC (u : IdeleGroup k))`. Rewrite using `[scalC_mul, ← mul_assoc, ← mul_assoc, scalC_commute]`. Rewrite using `[norm_mul, Circle.norm_coe, mul_one, thetaC_ltr, ltr_apply_zero, hc]`. Conclude with `hM _ ⟨(u, A), ⟨subset_closure hu, hA⟩, rfl⟩ t ht`.
-/
theorem exists_norm_thetaCInt_sub_le (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ A ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaCInt w (ltr A Ψ) ω t - thetaCConst (ltr A Ψ) ω‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hS : Continuous fun p : normOneSubgroup k × GL ι 𝔸[k] ↦
      p.2 * (scalC (p.1 : IdeleGroup k) : GL ι 𝔸[k]) :=
    continuous_snd.mul (continuous_scalC.comp (continuous_subtype_val.comp continuous_fst))
  obtain ⟨M, hM⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w hΨ ((hE.prod hC).image hS) r
  refine ⟨M * (normOneMeasure k).real (normOneFundamentalDomain k), fun A hA t ht ↦ ?_⟩
  rw [thetaCInt_ltr_sub_thetaCConst w hΨ A ω t, ← mul_assoc]
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top k)
    fun u hu ↦ ?_
  have hc : A * (scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) =
      scalC (moduleSection w t) * (A * scalC (u : IdeleGroup k)) := by
    rw [scalC_mul, ← mul_assoc, ← mul_assoc, scalC_commute]
  rw [norm_mul, Circle.norm_coe, mul_one, thetaC_ltr, ltr_apply_zero, hc]
  exact hM _ ⟨(u, A), ⟨subset_closure hu, hA⟩, rfl⟩ t ht

end GlobalTheory.CompanionTheory.AdelicThetaSeries
