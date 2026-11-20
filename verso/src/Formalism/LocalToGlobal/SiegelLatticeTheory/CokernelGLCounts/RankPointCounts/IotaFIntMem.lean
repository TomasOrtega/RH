import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WithZeroLeOneEqExp

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.PCountEx

section Clear

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

/- English proof (translation)
Use `haveI := (A p).lf`. Establish `h` using `((A p).val (algebraMap (𝓞 F) F t) 1).2 (by simpa using p.valuation_le_one t)`. Rewrite `h` using `[map_one]`. Rewrite using `[Valuation.mem_integer_iff]`. Conclude with `(Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).1 h`.
-/
theorem iotaF_int_mem (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    (A p).ιF (algebraMap (𝓞 F) F t) ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  have h := ((A p).val (algebraMap (𝓞 F) F t) 1).2 (by simpa using p.valuation_le_one t)
  rw [map_one] at h
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).1 h

/- English proof (translation)
Use `haveI := (A p).lf`. Distinguish the cases in `hl : l = 0`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[hl, mul_zero]`. Conclude with `Subring.zero_mem _`.

Take `⟨π, hπp, hπ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot`. Establish `hπv : p.valuation F (algebraMap (𝓞 F) F π) < 1` using `by first`. Consider the case `exact (p.valuation_lt_one_iff_mem π).2 hπp`. Consider the case `exact (p.valuation_lt_one_iff_mem (K := F) π).2 hπp`. Establish `hπF0 : algebraMap (𝓞 F) F π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hπ0`.

Take `⟨c, hc⟩ : ∃ c, c = (A p).ιF (algebraMap (𝓞 F) F π)` from `⟨_, rfl⟩`. Establish `hcint : c ∈ (ValuativeRel.valuation (A p).Fp).integer`. Rewrite using `[hc]`. Conclude with `iotaF_int_mem A p π`. Establish `hc0 : c ≠ 0`.

Rewrite using `[hc]`. Conclude with `(map_ne_zero (A p).ιF).2 hπF0`. Establish `hnot : -(c⁻¹) ∉ (ValuativeRel.valuation (A p).Fp).integer`. Introduce `hmem`. Rewrite `hmem` using `[Valuation.mem_integer_iff]`.

Establish `h1` using `(Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).2 hmem`. Establish `h2 : -(c⁻¹) = (A p).ιF (-(algebraMap (𝓞 F) F π)⁻¹)` using `by rw [hc, map_neg, map_inv₀]`. Rewrite `h1` using `[h2, ← map_one (A p).ιF, (A p).val, map_one]`. Establish `h3 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) = 1`. Rewrite using `[← map_mul, mul_neg, mul_inv_cancel₀ hπF0, Valuation.map_neg, map_one]`.

Establish `h4 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) ≤ p.valuation F (algebraMap (𝓞 F) F π) * 1` using `by first`. Consider the case `gcongr`. Consider the case `exact mul_le_mul_right' h1 _`. Consider the case `exact mul_le_mul_of_nonneg_left h1 (zero_le _)`. Rewrite `h4` using `[h3, mul_one]`.

Conclude with `absurd h4 (not_le.2 hπv)`. Establish `hW : IsOpen ((fun z => (z * l - 1) * c⁻¹) ⁻¹' ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp))` using `Valuation.isOpen_integer.preimage (((continuous_mul_right l).sub continuous_const).mul continuous_const)`. Establish `hne : ((fun z => (z * l - 1) * c⁻¹) ⁻¹' ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)).Nonempty`. Use `⟨l⁻¹, ?_⟩` and prove the remaining obligations. Use `show (l⁻¹ * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer`.

Rewrite using `[inv_mul_cancel₀ hl, sub_self, zero_mul]`. Conclude with `Subring.zero_mem _`. Take `⟨y, hy⟩` from `(A p).dense.exists_mem_open hW hne`. Establish `hy' : ((A p).ιF y * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer` using `hy`. Establish `hy1 : (A p).ιF y * l ∈ (ValuativeRel.valuation (A p).Fp).integer`.

Establish `e : (A p).ιF y * l = ((A p).ιF y * l - 1) * c⁻¹ * c + 1`. Rewrite using `[mul_assoc, inv_mul_cancel₀ hc0, mul_one, sub_add_cancel]`. Rewrite using `[e]`. Conclude with `Subring.add_mem _ (Subring.mul_mem _ hy' hcint) (Subring.one_mem _)`. Establish `hy0 : (A p).ιF y ≠ 0`.

Introduce `h0`. Rewrite `hy'` using `[h0, zero_mul, zero_sub, neg_mul, one_mul]`. Conclude with `hnot hy'`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) y`. Establish `hb' : algebraMap (𝓞 F) F b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`.

Establish `hy0' : (A p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) ≠ 0` using `hy0`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hy0'` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Establish `e : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F b * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_mul, mul_assoc]`. Conclude with `Subring.mul_mem _ (iotaF_int_mem A p b) hy1`.
-/
theorem clear_F (p : HeightOneSpectrum (𝓞 F)) (l : (A p).Fp) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ (A p).ιF (algebraMap (𝓞 F) F t) * l ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  by_cases hl : l = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [hl, mul_zero]
    exact Subring.zero_mem _
  obtain ⟨π, hπp, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hπv : p.valuation F (algebraMap (𝓞 F) F π) < 1 := by
    first
    | exact (p.valuation_lt_one_iff_mem π).2 hπp
    | exact (p.valuation_lt_one_iff_mem (K := F) π).2 hπp
  have hπF0 : algebraMap (𝓞 F) F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hπ0
  obtain ⟨c, hc⟩ : ∃ c, c = (A p).ιF (algebraMap (𝓞 F) F π) := ⟨_, rfl⟩
  have hcint : c ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    rw [hc]
    exact iotaF_int_mem A p π
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (map_ne_zero (A p).ιF).2 hπF0
  have hnot : -(c⁻¹) ∉ (ValuativeRel.valuation (A p).Fp).integer := by
    intro hmem
    rw [Valuation.mem_integer_iff] at hmem
    have h1 := (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).2 hmem
    have h2 : -(c⁻¹) = (A p).ιF (-(algebraMap (𝓞 F) F π)⁻¹) := by rw [hc, map_neg, map_inv₀]
    rw [h2, ← map_one (A p).ιF, (A p).val, map_one] at h1
    have h3 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) = 1 := by
      rw [← map_mul, mul_neg, mul_inv_cancel₀ hπF0, Valuation.map_neg, map_one]
    have h4 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) ≤
        p.valuation F (algebraMap (𝓞 F) F π) * 1 := by
      first
      | gcongr
      | exact mul_le_mul_right' h1 _
      | exact mul_le_mul_of_nonneg_left h1 (zero_le _)
    rw [h3, mul_one] at h4
    exact absurd h4 (not_le.2 hπv)
  have hW : IsOpen ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)) :=
    Valuation.isOpen_integer.preimage (((continuous_mul_right l).sub continuous_const).mul continuous_const)
  have hne : ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)).Nonempty := by
    refine ⟨l⁻¹, ?_⟩
    show (l⁻¹ * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer
    rw [inv_mul_cancel₀ hl, sub_self, zero_mul]
    exact Subring.zero_mem _
  obtain ⟨y, hy⟩ := (A p).dense.exists_mem_open hW hne
  have hy' : ((A p).ιF y * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer := hy
  have hy1 : (A p).ιF y * l ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    have e : (A p).ιF y * l = ((A p).ιF y * l - 1) * c⁻¹ * c + 1 := by
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one, sub_add_cancel]
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ hy' hcint) (Subring.one_mem _)
  have hy0 : (A p).ιF y ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_sub, neg_mul, one_mul] at hy'
    exact hnot hy'
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hy0' : (A p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) ≠ 0 := hy0
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    apply hy0'
    simp
  · have e : algebraMap (𝓞 F) F a =
        algebraMap (𝓞 F) F b * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) := by
      field_simp
    rw [e, map_mul, mul_assoc]
    exact Subring.mul_mem _ (iotaF_int_mem A p b) hy1

/- English proof (translation)
Use `haveI := (A p).lf`. Rewrite using `[(A p).O_def]`. Establish `e : algebraMap (A p).Fp (A p).Ep w = algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hw⟩` using `rfl`. Rewrite using `[e]`. Conclude with `isIntegral_algebraMap`.
-/
private theorem ιF_mem_O_of_mem_integers (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Fp)
    (hw : w ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) : algebraMap (A p).Fp (A p).Ep w ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have e : algebraMap (A p).Fp (A p).Ep w = algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hw⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

/- English proof (translation)
Use `haveI := (A p).lf`. Rewrite using `[(A p).O_def]`. Establish `hm` using `iotaF_int_mem A p t`. Establish `e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) = algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hm⟩` using `rfl`. Rewrite using `[e]`.

Conclude with `isIntegral_algebraMap`.
-/
private theorem algebraMap_ιF_mem_O (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have hm := iotaF_int_mem A p t
  have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) =
      algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hm⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

/- English proof (translation)
Use `haveI := (A p).lf`. Establish `hz : z ∈ Submodule.span (A p).Fp (Set.range (A p).ιE)`. Rewrite using `[(A p).span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨e, rfl⟩` from `hx`. Establish `hz : IsAlgebraic ℤ e` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)`. Establish `inj : ∀ x : ℤ, algebraMap ℤ E x = 0 → x = 0` using `fun x hx => by simpa using hx`. Establish `hint : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e)` using `by first`.

Consider the case `(obtain ⟨⟨w, hw⟩, y, hy0, hyw⟩ := exists_integral_multiple hz inj`. Use `⟨y, hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `hw' : IsIntegral ℤ w` using `hw`. Simplify `hw')` using `[hyw]`.

Consider the case `(obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple`. Conclude with `⟨y, hy0, by simpa [zsmul_eq_mul] using hy⟩)`. Take `⟨y, hy0, hy⟩` from `hint`. Use `⟨(y : 𝓞 F), by exact_mod_cast hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[← (A p).compat, ← map_mul]`.

Establish `e1 : algebraMap F E (algebraMap (𝓞 F) F (y : 𝓞 F)) * e = (y : E) * e` using `by simp`. Rewrite using `[e1, (A p).O_def]`. Establish `h2 : IsIntegral ℤ ((A p).ιE ((y : E) * e))` using `hy.map (A p).ιE.toIntAlgHom`. Conclude with `h2.tower_top`. Consider the case `zero`.

Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero]`. Conclude with `Subring.zero_mem _`. Consider the case `add x y _ _ hx hy`. Take `⟨t1, h10, h1⟩` from `hx`.

Take `⟨t2, h20, h2⟩` from `hy`. Use `⟨t1 * t2, mul_ne_zero h10 h20, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t1 * t2))) * (x + y) = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) * (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) + algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F …`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Subring.add_mem _ (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t2) h1) (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t1) h2)`. Consider the case `smul c x _ hx`. Take `⟨t1, h10, h1⟩` from `hx`. Take `⟨t2, h20, h2⟩` from `clear_F A p c`.

Use `⟨t2 * t1, mul_ne_zero h20 h10, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Establish `e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t2 * t1))) * (algebraMap (A p).Fp (A p).Ep c * x) = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2) * c) * (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x)`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Subring.mul_mem _ (ιF_mem_O_of_mem_integers A p _ h2) h1`.
-/
theorem clear_one (p : HeightOneSpectrum (𝓞 F)) (z : (A p).Ep) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) * z ∈ (A p).O := by
  haveI := (A p).lf
  have hz : z ∈ Submodule.span (A p).Fp (Set.range (A p).ιE) := by
    rw [(A p).span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    have hz : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
    have inj : ∀ x : ℤ, algebraMap ℤ E x = 0 → x = 0 := fun x hx => by simpa using hx
    have hint : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e) := by
      first
      | (obtain ⟨⟨w, hw⟩, y, hy0, hyw⟩ := exists_integral_multiple hz inj
         refine ⟨y, hy0, ?_⟩
         rw [mul_comm]
         have hw' : IsIntegral ℤ w := hw
         simpa [hyw] using hw')
      | (obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
         exact ⟨y, hy0, by simpa [zsmul_eq_mul] using hy⟩)
    obtain ⟨y, hy0, hy⟩ := hint
    refine ⟨(y : 𝓞 F), by exact_mod_cast hy0, ?_⟩
    rw [← (A p).compat, ← map_mul]
    have e1 : algebraMap F E (algebraMap (𝓞 F) F (y : 𝓞 F)) * e = (y : E) * e := by simp
    rw [e1, (A p).O_def]
    have h2 : IsIntegral ℤ ((A p).ιE ((y : E) * e)) := hy.map (A p).ιE.toIntAlgHom
    exact h2.tower_top
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [mul_zero]
    exact Subring.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := hy
    refine ⟨t1 * t2, mul_ne_zero h10 h20, ?_⟩
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t1 * t2))) * (x + y) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) +
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) * y) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t2) h1)
      (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t1) h2)
  | smul c x _ hx =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := clear_F A p c
    refine ⟨t2 * t1, mul_ne_zero h20 h10, ?_⟩
    rw [Algebra.smul_def]
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t2 * t1))) *
        (algebraMap (A p).Fp (A p).Ep c * x) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2) * c) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.mul_mem _ (ιF_mem_O_of_mem_integers A p _ h2) h1

/- English proof (translation)
Use `choose t ht0 ht using fun q : S × ι => clear_one A q.1.1 (z q.1 q.2)`. Use `⟨∏ q, t q, Finset.prod_ne_zero_iff.2 (fun q _ => ht0 q), fun p hp k => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ (⟨⟨p, hp⟩, k⟩ : S × ι))]`. Simplify using `only [map_mul]`. Rewrite using `[mul_comm (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t ⟨⟨p, hp⟩, k⟩)))), mul_assoc]`.

Conclude with `Subring.mul_mem _ (algebraMap_ιF_mem_O A p _) (ht ⟨⟨p, hp⟩, k⟩)`.
-/
theorem clear (S : Finset (HeightOneSpectrum (𝓞 F))) {ι : Type} [Fintype ι] (z : ∀ p, ι → (A p).Ep) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ p ∈ S, ∀ k,
      algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * z p k ∈ (A p).O := by
  classical
  choose t ht0 ht using fun q : S × ι => clear_one A q.1.1 (z q.1 q.2)
  refine ⟨∏ q, t q, Finset.prod_ne_zero_iff.2 (fun q _ => ht0 q), fun p hp k => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ (⟨⟨p, hp⟩, k⟩ : S × ι))]
  simp only [map_mul]
  rw [mul_comm (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t ⟨⟨p, hp⟩, k⟩)))), mul_assoc]
  exact Subring.mul_mem _ (algebraMap_ιF_mem_O A p _) (ht ⟨⟨p, hp⟩, k⟩)

end Clear

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}

/- English proof (translation)
Establish `h` using `fun ab : Fin n × Fin n => approxE A S c hc (fun p => g p ab.1 ab.2)`. Use `choose x hxS hxO using h`. Use `⟨fun a b => if b < a then x (a, b) else if a = b then 1 else 0, fun a => by simp, fun a b hab => ?_, fun p hp a b => ?_, fun p hp a b => ?_⟩` and prove the remaining obligations. Simplify using `[not_lt.2 hab.le, hab.ne]`. Distinguish the cases in `hba : b < a`.

Simplify using `only [hba, if_true]`. Conclude with `hxS (a, b) p hp`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Break down `eq_or_ne a b with rfl | hab` into its components or cases. Simplify using `[hg1 p hp a]`.

Establish `hlt : a < b` using `lt_of_le_of_ne (not_lt.1 hba) hab`. Simplify using `[hba, hab, hg0 p hp a b hlt]`. Distinguish the cases in `hba : b < a`. Simplify using `only [hba, if_true]`. Conclude with `hxO (a, b) p hp`.

Simplify using `only [hba, if_false] split_ifs`. Rewrite using `[map_one]`. Conclude with `one_mem _`. Rewrite using `[map_zero]`. Conclude with `zero_mem _`.
-/
theorem approx_lo (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, a < b → g p a b = 0) :
    ∃ L : Matrix (Fin n) (Fin n) E, (∀ a, L a a = 1) ∧ (∀ a b, a < b → L a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (L a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (L a b) ∈ (A p).O := by
  have h := fun ab : Fin n × Fin n => approxE A S c hc (fun p => g p ab.1 ab.2)
  choose x hxS hxO using h
  refine ⟨fun a b => if b < a then x (a, b) else if a = b then 1 else 0, fun a => by simp, fun a b hab => ?_,
    fun p hp a b => ?_, fun p hp a b => ?_⟩
  · simp [not_lt.2 hab.le, hab.ne]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxS (a, b) p hp
    · refine ⟨0, zero_mem _, ?_⟩
      rcases eq_or_ne a b with rfl | hab
      · simp [hg1 p hp a]
      · have hlt : a < b := lt_of_le_of_ne (not_lt.1 hba) hab
        simp [hba, hab, hg0 p hp a b hlt]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxO (a, b) p hp
    · simp only [hba, if_false]
      split_ifs
      · rw [map_one]; exact one_mem _
      · rw [map_zero]; exact zero_mem _

/- English proof (translation)
Take `⟨L, hL1, hL0, hLS, hLn⟩` from `approx_lo A S c hc (fun p => (g p).transpose) (fun p hp a => by simpa using hg1 p hp a) (fun p hp a b hab => by simpa [Matrix.transpose_apply] using hg0 p hp b a hab)`. Use `⟨L.transpose, fun a => by simpa using hL1 a, fun a b hab => by simpa using hL0 b a hab, fun p hp a b => ?_, fun p hp a b => by simpa using hLn p hp b a⟩` and prove the remaining obligations. Simplify `hLS p hp b a` using `[Matrix.transpose_apply]`.
-/
theorem approx_up (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, b < a → g p a b = 0) :
    ∃ U : Matrix (Fin n) (Fin n) E, (∀ a, U a a = 1) ∧ (∀ a b, b < a → U a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (U a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (U a b) ∈ (A p).O := by
  obtain ⟨L, hL1, hL0, hLS, hLn⟩ := approx_lo A S c hc (fun p => (g p).transpose)
    (fun p hp a => by simpa using hg1 p hp a)
    (fun p hp a b hab => by simpa [Matrix.transpose_apply] using hg0 p hp b a hab)
  refine ⟨L.transpose, fun a => by simpa using hL1 a, fun a b hab => by simpa using hL0 b a hab,
    fun p hp a b => ?_, fun p hp a b => by simpa using hLn p hp b a⟩
  simpa [Matrix.transpose_apply] using hLS p hp b a

end Mat

end Formalism.L2.SG.Pf.PCountEx
