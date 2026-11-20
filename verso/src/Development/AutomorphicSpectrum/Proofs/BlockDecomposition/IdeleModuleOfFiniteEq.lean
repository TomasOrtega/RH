import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField.AdeleRing nonZeroDivisors

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k]

/- English proof (translation)
Establish `h : infiniteModule (ofFinite b : IdeleGroup k) = 1` using `Finset.prod_eq_one fun w _ ↦ by`. Rewrite using `[show ((ofFinite b : IdeleGroup k) : 𝔸[k]).1 w = 1 from rfl, norm_one, one_pow]`. Rewrite using `[ideleModule_apply, h, one_mul]`.
-/
theorem ideleModule_ofFinite_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  have h : infiniteModule (ofFinite b : IdeleGroup k) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      rw [show ((ofFinite b : IdeleGroup k) : 𝔸[k]).1 w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, h, one_mul]

/- English proof (translation)
The claim follows from `(Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).1 (mem_integralFiniteAdeles.1 hb v))`.
-/
theorem norm_le_one_of_mem_OH {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (v : HeightOneSpectrum (𝓞 k)) :
    ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).1
      (mem_integralFiniteAdeles.1 hb v))

/- English proof (translation)
Rewrite using `[finiteModule, finprod_eq_prod _ (finite_mulSupport_norm _)]`. Conclude with `Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun v _ ↦ norm_le_one_of_mem_OH hb v`.
-/
theorem finiteModule_le_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) : finiteModule (ofFinite b) ≤ 1 := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm _)]
  exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun v _ ↦ norm_le_one_of_mem_OH hb v

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 k), ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ < 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `hu ((mem_finiteIntegralUnits k).2 fun v ↦ ⟨mem_integralFiniteAdeles.1 hb v, ?_⟩)` and prove the remaining obligations. Establish `hv1 : ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ = 1` using `le_antisymm (norm_le_one_of_mem_OH hb v) (hcon v)`.

Establish `hmul : (b : FiniteAdeleRing (𝓞 k) k) v * ((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1` using `congrArg (fun a : FiniteAdeleRing (𝓞 k) k ↦ a v) (Units.mul_inv b)`. Establish `hn : ‖((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v‖ = 1`. Use `congrArg norm hmul` as an intermediate fact. Rewrite `this` using `[norm_mul, hv1, one_mul, norm_one]`. Then use the resulting hypothesis. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).2 ((Valued.toNormedField.norm_le_one_iff).1 hn.le)`.

Establish `hfin` using `finite_mulSupport_norm (ofFinite b : IdeleGroup k)`. Establish `hvS : v ∈ hfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset, Function.mem_mulSupport]`. Conclude with `hv.ne`. Rewrite using `[finiteModule, finprod_eq_prod _ hfin, ← Finset.mul_prod_erase _ _ hvS]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finiteModule_lt_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (hu : b ∉ finiteIntegralUnits k) :
    finiteModule (ofFinite b) < 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 k), ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ < 1 := by
    by_contra hcon
    push_neg at hcon
    refine hu ((mem_finiteIntegralUnits k).2 fun v ↦ ⟨mem_integralFiniteAdeles.1 hb v, ?_⟩)
    have hv1 : ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ = 1 :=
      le_antisymm (norm_le_one_of_mem_OH hb v) (hcon v)
    have hmul : (b : FiniteAdeleRing (𝓞 k) k) v *
        ((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun a : FiniteAdeleRing (𝓞 k) k ↦ a v) (Units.mul_inv b)
    have hn : ‖((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v‖ = 1 := by
      have := congrArg norm hmul
      rwa [norm_mul, hv1, one_mul, norm_one] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).2
      ((Valued.toNormedField.norm_le_one_iff).1 hn.le)
  have hfin := finite_mulSupport_norm (ofFinite b : IdeleGroup k)
  have hvS : v ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
    exact hv.ne
  rw [finiteModule, finprod_eq_prod _ hfin, ← Finset.mul_prod_erase _ _ hvS]
  calc _ ≤ ‖((ofFinite b : IdeleGroup k) : 𝔸[k]).2 v‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun u _ ↦ norm_le_one_of_mem_OH hb u)
          (norm_nonneg _)
    _ < 1 := by rwa [mul_one]

def integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) : ℂ :=
  g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (((n : ℝ) : ℝ) : ℂ)

/- English proof (translation)
Rewrite using `[ideleModule_ofFinite_eq, Complex.ofReal_cpow (finiteModule_pos _).le]`.
-/
theorem cpow_module_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) (x : ℝ) :
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((finiteModule (ofFinite b) ^ x : ℝ) : ℂ) := by
  rw [ideleModule_ofFinite_eq, Complex.ofReal_cpow (finiteModule_pos _).le]

/- English proof (translation)
Rewrite using `[integrand, cpow_module_eq, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (finiteModule_pos _).le _)]`.
-/
theorem norm_integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ = ‖g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)‖ *
      finiteModule (ofFinite b) ^ (n : ℝ) := by
  rw [integrand, cpow_module_eq, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (finiteModule_pos _).le _)]

/- English proof (translation)
Establish `h1 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)` using `((GJMatrix.mem_finiteSchwartzBruhatPi k).1 hg).1.continuous.comp (continuous_pi fun _ ↦ Units.continuous_val)`. Establish `h2 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ (ω.toIdele (ofFinite b) : ℂ)` using `continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_ofFinite)`. Establish `h3 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp ((continuous_finiteModule.comp continuous_ofFinite).rpow_const fun b ↦ Or.inl (finiteModule_pos _).ne')`. Establish `: integrand g ω n = fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ)`. Use function extensionality and compare the values at `b`.

Rewrite using `[integrand, cpow_module_eq]`. Rewrite using `[this]`. Conclude with `(h1.mul h2).mul h3`.
-/
theorem continuous_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) (ω : HeckeCharacter k) (n : ℕ) :
    Continuous (integrand g ω n) := by
  have h1 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k) :=
    ((GJMatrix.mem_finiteSchwartzBruhatPi k).1 hg).1.continuous.comp
      (continuous_pi fun _ ↦ Units.continuous_val)
  have h2 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ (ω.toIdele (ofFinite b) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_ofFinite)
  have h3 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((continuous_finiteModule.comp continuous_ofFinite).rpow_const
        fun b ↦ Or.inl (finiteModule_pos _).ne')
  have : integrand g ω n = fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) *
      (ω.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) := by
    funext b
    rw [integrand, cpow_module_eq]
  rw [this]
  exact (h1.mul h2).mul h3

/- English proof (translation)
Rewrite using `[norm_integrand]`. Distinguish the cases in `h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0`. Rewrite using `[h0, norm_zero, zero_mul]`. Conclude with `finiteZetaBound_nonneg _ _ _`. Establish `hO` using `(hb _).2 h0`.

Establish `hL : (b : FiniteAdeleRing (𝓞 k) k) ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ)`. Rewrite using `[← SetLike.mem_coe, idealFiniteAdeles_one]`. Conclude with `hO`. Rewrite using `[finiteZetaBound, if_pos hL]`. Establish `hpow : finiteModule (ofFinite b) ^ (n : ℝ) ≤ finiteModule (ofFinite b) ^ (2 : ℝ)` using `Real.rpow_le_rpow_of_exponent_ge (finiteModule_pos _) (finiteModule_le_one hO) (by exact_mod_cast hn)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_integrand_le {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} (ω : HeckeCharacter k)
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k)) {n : ℕ} (hn : 2 ≤ n)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ ≤ finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2 b := by
  rw [norm_integrand]
  by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
  · rw [h0, norm_zero, zero_mul]
    exact finiteZetaBound_nonneg _ _ _
  have hO := (hb _).2 h0
  have hL : (b : FiniteAdeleRing (𝓞 k) k) ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) := by
    rw [← SetLike.mem_coe, idealFiniteAdeles_one]
    exact hO
  rw [finiteZetaBound, if_pos hL]
  have hpow : finiteModule (ofFinite b) ^ (n : ℝ) ≤ finiteModule (ofFinite b) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (finiteModule_pos _) (finiteModule_le_one hO)
      (by exact_mod_cast hn)
  calc _ ≤ 1 * finiteModule (ofFinite b) ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_right (hb _).1 (Real.rpow_nonneg (finiteModule_pos _).le _)
    _ ≤ _ := by rwa [one_mul]

/- English proof (translation)
Distinguish the cases in `hW : b ∈ finiteIntegralUnits k`. Rewrite using `[Set.indicator_of_mem (SetLike.mem_coe.2 hW)]`. Establish `hm : finiteModule (ofFinite b : IdeleGroup k) = 1` using `finiteModule_eq_one_of_mem hW`. Use `tendsto_const_nhds.congr fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[integrand, cpow_module_eq, hu b hW, hm, Real.one_rpow, Complex.ofReal_one, one_mul]`.

Rewrite using `[Set.indicator_of_notMem (fun h ↦ hW (SetLike.mem_coe.1 h))]`. Distinguish the cases in `h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0`. Use `tendsto_const_nhds.congr fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[integrand, h0, zero_mul, zero_mul]`. Establish `hlt` using `finiteModule_lt_one ((hb _).2 h0) hW`.

Use `squeeze_zero_norm (a := fun n : ℕ ↦ finiteModule (ofFinite b) ^ n) (fun n ↦ ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (finiteModule_pos _).le hlt)` and prove the remaining obligations. Rewrite using `[norm_integrand, Real.rpow_natCast]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} {ω : HeckeCharacter k}
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k))
    (hu : ∀ u ∈ finiteIntegralUnits k,
      g (fun _ ↦ (u : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite u) : ℂ) = 1)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    Tendsto (fun n ↦ integrand g ω n b) atTop
      (𝓝 (((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b)) := by
  by_cases hW : b ∈ finiteIntegralUnits k
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hW)]
    have hm : finiteModule (ofFinite b : IdeleGroup k) = 1 := finiteModule_eq_one_of_mem hW
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [integrand, cpow_module_eq, hu b hW, hm, Real.one_rpow, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem (fun h ↦ hW (SetLike.mem_coe.1 h))]
    by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [integrand, h0, zero_mul, zero_mul]
    have hlt := finiteModule_lt_one ((hb _).2 h0) hW
    refine squeeze_zero_norm (a := fun n : ℕ ↦ finiteModule (ofFinite b) ^ n) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (finiteModule_pos _).le hlt)
    rw [norm_integrand, Real.rpow_natCast]
    calc _ ≤ 1 * finiteModule (ofFinite b) ^ n :=
          mul_le_mul_of_nonneg_right (hb _).1 (pow_nonneg (finiteModule_pos _).le _)
      _ = _ := one_mul _

/- English proof (translation)
Introduce `k _ _ g ω hg hb hu B`. Establish `hlim : Tendsto (fun n : ℕ ↦ ∫ b, integrand g ω n b ∂finiteIdeleMeasure k) atTop (𝓝 (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) : Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k))` using `tendsto_integral_filter_of_dominated_convergence (finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2) (Eventually.of_forall fun n ↦ (continuous_integrand hg ω n).aestronglyMeasurable) ((eventually_ge_atTop 2).mono fun n hn ↦ Eventually.of_forall (norm_integrand_le ω hb hn)) (int …`. Establish `hval : (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) : Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k) = 1`. Rewrite using `[integral_indicator_const _ (isOpen_finiteIntegralUnits k).measurableSet, Measure.real, finiteIdeleMeasure_finiteIntegralUnits]`. Simplify using the standard rewrite rules.

Rewrite `hlim` using `[hval]`. Take `⟨n, hn, hB⟩` from `((hlim.eventually_ne one_ne_zero).and (tendsto_natCast_atTop_atTop.eventually_gt_atTop B)).exists`. Conclude with `⟨n, hB, hn⟩`.
-/
theorem zFinLim : ZFinLim := by
  intro k _ _ g ω hg hb hu B
  have hlim : Tendsto (fun n : ℕ ↦ ∫ b, integrand g ω n b ∂finiteIdeleMeasure k) atTop
      (𝓝 (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k)) :=
    tendsto_integral_filter_of_dominated_convergence
      (finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2)
      (Eventually.of_forall fun n ↦ (continuous_integrand hg ω n).aestronglyMeasurable)
      ((eventually_ge_atTop 2).mono fun n hn ↦ Eventually.of_forall (norm_integrand_le ω hb hn))
      (integrable_finiteZetaBound 1 (by norm_num))
      (Eventually.of_forall (tendsto_integrand hb hu))
  have hval : (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
      Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k) = 1 := by
    rw [integral_indicator_const _ (isOpen_finiteIntegralUnits k).measurableSet, Measure.real,
      finiteIdeleMeasure_finiteIntegralUnits]
    simp
  rw [hval] at hlim
  obtain ⟨n, hn, hB⟩ := ((hlim.eventually_ne one_ne_zero).and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop B)).exists
  exact ⟨n, hB, hn⟩

end GlobalTheory.CompanionTheory.EisTF
