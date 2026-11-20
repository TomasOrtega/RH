import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric

namespace Formalism.L2.SG.Pf.RescaleCore.NCov

def AdCocpt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ C : Set (AF F), IsCompact C ∧ ∀ a : AF F, ∃ x : F, a - algebraMap F (AF F) x ∈ C

namespace AdCocptW

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `first`. Consider the case `exact isCompact_closedBall (0 : v.Completion) R`. Consider the case `exact (haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion isCompact_closedBall (0 : v.Completion) R)`. Consider the case `exact (by`. Establish `hi` using `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v`.

Establish `hc` using `(hi.isClosedEmbedding).isCompact_preimage (isCompact_closedBall (0 : ℂ) R)`. Establish `e : (NumberField.InfinitePlace.Completion.extensionEmbedding v) ⁻¹' closedBall 0 R = closedBall (0 : v.Completion) R`. Use extensionality with `z`. Simplify using `only [Set.mem_preimage, mem_closedBall, dist_zero_right]`. Rewrite using `[hi.norm_map_of_map_zero (map_zero _)]`.

Rewrite `hc` using `[e]`. Conclude with `hc)`.
-/
theorem NCovAd_ball_compact (v : InfinitePlace F) (R : ℝ) :
    IsCompact (closedBall (0 : v.Completion) R) := by
  first
  | exact isCompact_closedBall (0 : v.Completion) R
  | exact (haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
      isCompact_closedBall (0 : v.Completion) R)
  | exact (by
      have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v
      have hc := (hi.isClosedEmbedding).isCompact_preimage (isCompact_closedBall (0 : ℂ) R)
      have e : (NumberField.InfinitePlace.Completion.extensionEmbedding v) ⁻¹' closedBall 0 R =
          closedBall (0 : v.Completion) R := by
        ext z
        simp only [Set.mem_preimage, mem_closedBall, dist_zero_right]
        rw [hi.norm_map_of_map_zero (map_zero _)]
      rw [e] at hc
      exact hc)

/- English proof (translation)
Use `set b := NumberField.mixedEmbedding.latticeBasis F with hb`. Establish `hB : ∃ R : ℝ, ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R` using `by first`. Consider the case `exact (ZSpan.fundamentalDomain_isBounded b).exists_norm_le`. Consider the case `exact isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded b)`. Take `⟨R, hR⟩` from `hB`.

Use `⟨R, fun x => ?_⟩` and prove the remaining obligations. Take `⟨⟨w, hw⟩, hwD, -⟩` from `ZSpan.exist_unique_vadd_mem_fundamentalDomain b (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)`. Establish `hc' : ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • b i = w` using `by first`. Consider the case `exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw`. Consider the case `exact Submodule.mem_span_range_iff_exists_fun.mp hw`.

Take `⟨c, hc⟩` from `hc'`. Set `γ : 𝓞 F` to `∑ i, c i • NumberField.RingOfIntegers.basis F i`. Establish `hγ : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F γ) = w`. Rewrite using `[← hc]`. Simplify using `only [γ, map_sum, map_zsmul, hb, NumberField.mixedEmbedding.latticeBasis_apply, NumberField.integralBasis_apply]`.

Use `⟨-γ, fun v => ?_⟩` and prove the remaining obligations. Establish `hneg : ((-γ : 𝓞 F) : F) = -(algebraMap (𝓞 F) F γ)` using `by first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `(push_cast; rfl)`.

Use `set z := x - algebraMap F (Ainf F) ((-γ : 𝓞 F) : F) with hzdef`. Establish `hz : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z ∈ ZSpan.fundamentalDomain b`. Establish `e : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z = w + NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x`. Rewrite using `[hzdef, hneg, map_neg, sub_neg_eq_add, map_add, ← hγ, NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, add_comm]`. Rewrite using `[e]`.

Use `first`. Consider the case `exact hwD`. Consider the case `(rw [Submodule.vadd_def, vadd_eq_add] at hwD; exact hwD)`. Consider the case `(simpa [Submodule.vadd_def] using hwD)`. Establish `hn` using `hR _ hz`.

Distinguish the cases in `hv : v.IsReal`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Conclude with `((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) _).symm`. Use `_ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1‖ := norm_le_pi_norm _ _`.

Use `_ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_fst_le _`. Use `_ ≤ R := hn`. Establish `hv' : v.IsComplex` using `NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`.

Conclude with `((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _).symm`. Use `_ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2‖ := norm_le_pi_norm _ _`. Use `_ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_snd_le _`. Use `_ ≤ R := hn`.
-/
theorem NCovAd_inf_approx : ∃ R : ℝ, ∀ x : Ainf F, ∃ β : 𝓞 F,
    ∀ v : InfinitePlace F, ‖(x - algebraMap F (Ainf F) (β : F)) v‖ ≤ R := by
  classical
  set b := NumberField.mixedEmbedding.latticeBasis F with hb
  have hB : ∃ R : ℝ, ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R := by
    first
    | exact (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
    | exact isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded b)
  obtain ⟨R, hR⟩ := hB
  refine ⟨R, fun x => ?_⟩
  obtain ⟨⟨w, hw⟩, hwD, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)
  have hc' : ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • b i = w := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
    | exact Submodule.mem_span_range_iff_exists_fun.mp hw
  obtain ⟨c, hc⟩ := hc'
  let γ : 𝓞 F := ∑ i, c i • NumberField.RingOfIntegers.basis F i
  have hγ : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F γ) = w := by
    rw [← hc]
    simp only [γ, map_sum, map_zsmul, hb, NumberField.mixedEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
  refine ⟨-γ, fun v => ?_⟩
  have hneg : ((-γ : 𝓞 F) : F) = -(algebraMap (𝓞 F) F γ) := by
    first
    | rfl
    | simp
    | (push_cast; rfl)
  set z := x - algebraMap F (Ainf F) ((-γ : 𝓞 F) : F) with hzdef
  have hz : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z ∈ ZSpan.fundamentalDomain b := by
    have e : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z = w + NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
      rw [hzdef, hneg, map_neg, sub_neg_eq_add, map_add, ← hγ,
        NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, add_comm]
    rw [e]
    first
    | exact hwD
    | (rw [Submodule.vadd_def, vadd_eq_add] at hwD; exact hwD)
    | (simpa [Submodule.vadd_def] using hwD)
  have hn := hR _ hz
  by_cases hv : v.IsReal
  · calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 ⟨v, hv⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_fst_le _
      _ ≤ R := hn
  · have hv' : v.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
    calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 ⟨v, hv'⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_snd_le _
      _ ≤ R := hn

/- English proof (translation)
Use `show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (algebraMap F (Af F) (β : F)) v ∈ v.adicCompletionIntegers F`. Introduce `v`. Use `first`. Consider the case `exact v.coe_mem_adicCompletionIntegers β`. Consider the case `exact (v.mem_adicCompletionIntegers F).mpr (by`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Simplify using `using v.valuation_le_one β)`. Consider the case `exact (v.mem_adicCompletionIntegers F).mpr (by show Valued.v ((β : F) : v.adicCompletion F) ≤ 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Simplify using `using v.valuation_le_one β)`.
-/
theorem NCovAd_int_mem (β : 𝓞 F) : algebraMap F (Af F) (β : F) ∈ Formalism.UG.intAd F := by
  show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    (algebraMap F (Af F) (β : F)) v ∈ v.adicCompletionIntegers F
  intro v
  first
  | exact v.coe_mem_adicCompletionIntegers β
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      show Valued.v ((β : F) : v.adicCompletion F) ≤ 1
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)

/- English proof (translation)
Take `⟨m, hm, hma⟩` from `PIW.AdelClassFin.DictRing.af_denom a`. Take `⟨β, y, hy, hβ⟩` from `PIW.AdelClassFin.DictRing.af_approx _ hma m hm`. Use `⟨(β : F) / m, ?_⟩` and prove the remaining obligations. Establish `hmF : (m : F) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F)` using `(map_natCast _ m).symm`.

Establish `hu : IsUnit ((m : ℕ) : Af F)`. Rewrite using `[hcast]`. Conclude with `(isUnit_iff_ne_zero.2 hmF).map _`. Establish `e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y`. Rewrite using `[mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hu.mul_left_cancel e1]`. Conclude with `hy`.
-/
theorem NCovAd_fin_approx (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    ring
  rw [hu.mul_left_cancel e1]
  exact hy

end AdCocptW

end Formalism.L2.SG.Pf.RescaleCore.NCov
