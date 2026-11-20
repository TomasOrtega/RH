import Mathlib

noncomputable section

namespace PI.AdicCompletionValuation

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `h` using `v.coe_mem_adicCompletionIntegers (K := F) r`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Conclude with `h`.
-/
theorem algebraMap_mem_integer (r : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ Valued.integer (v.adicCompletion F) := by
  have h := v.coe_mem_adicCompletionIntegers (K := F) r
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  exact h

/- English proof (translation)
Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F)) k`. Simplify using `only at hab`. Substitute `hab` using the available equality. Establish `hb0 : (b : 𝓞 F) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Establish `hspan : Ideal.span {(b : 𝓞 F)} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`. Establish `hfin` using `Ideal.finite_factors hspan`. Establish `hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ n : ℕ, WithZero.exp (-(n : ℤ)) ≤ w.intValuation (b : 𝓞 F)`. Introduce `w`.

Rewrite using `[intValuation_def, if_neg hb0]`. Conclude with `⟨_, le_rfl⟩`. Use `choose n hn using hn`. Establish `hdist : ∀ i ∈ insert v hfin.toFinset, ∀ j ∈ insert v hfin.toFinset, i ≠ j → (fun w : HeightOneSpectrum (𝓞 F) => w.asIdeal) i ≠ (fun w => w.asIdeal) j`. Introduce `i _ j _ hij h`.

Conclude with `hij (HeightOneSpectrum.ext h)`. Take `⟨c, hc⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v hfin.toFinset) (fun w : HeightOneSpectrum (𝓞 F) => w.asIdeal) (fun w => if w = v then 1 else n w) (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime) hdist (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then (1 : 𝓞 F) …`. Establish `hcv : c ∉ v.asIdeal`. Introduce `hmem`. Establish `h1` using `hc v (Finset.mem_insert_self v _)`.

Simplify using `at h1`. Apply `v.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h2` using `v.asIdeal.sub_mem hmem h1`. Simplify using `using h2`.

Establish `hcw : ∀ w ∈ hfin.toFinset, w ≠ v → c ∈ w.asIdeal ^ n w`. Introduce `w hw hwv`. Establish `h1` using `hc w (Finset.mem_insert_of_mem hw)`. Simplify `h1` using `[hwv]`. Establish `key : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F (algebraMap (𝓞 F) F c * IsLocalization.mk' F a b) ≤ 1`.

Introduce `w`. Establish `hvc : w.valuation F (algebraMap (𝓞 F) F c) = w.intValuation c` using `valuation_of_algebraMap w c`. Rewrite using `[map_mul, hvc]`. Distinguish the cases in `hwv : w = v`. Rewrite using `[hwv, intValuation_eq_one_iff.mpr hcv, one_mul]`.

Conclude with `hk`. Rewrite using `[valuation_of_mk']`. Establish `hbne : w.intValuation (b : 𝓞 F) ≠ 0`. Conclude with `intValuation_ne_zero w _ hb0`. Distinguish the cases in `hwS : w ∈ hfin.toFinset`.

Establish `hc' : w.intValuation c ≤ w.intValuation (b : 𝓞 F)` using `((intValuation_le_pow_iff_mem w c (n w)).mpr (hcw w hwS hwv)).trans (hn w)`. Rewrite using `[div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact mul_le_mul' hc' (mul_le_mul_right' (intValuation_le_one w a) _)`. Consider the case `(gcongr; exact intValuation_le_one w a)`.

Use `_ = 1 := by rw [one_mul, mul_inv_cancel₀ hbne]`. Establish `hb1 : w.intValuation (b : 𝓞 F) = 1`. Rewrite using `[intValuation_eq_one_iff]`. Introduce `hmem`. Conclude with `hwS (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr hmem))`.

Rewrite using `[hb1, div_one]`. Conclude with `mul_le_one' (intValuation_le_one w c) (intValuation_le_one w a)`. Take `⟨r', hr'⟩` from `RingHom.mem_range.mp (mem_integers_of_valuation_le_one F _ key)`. Establish `hmax : v.asIdeal.IsMaximal` using `v.isMaximal`. Take `⟨y, i, hi, hyi⟩` from `hmax.exists_inv hcv`.

Use `⟨y * r', ?_⟩` and prove the remaining obligations. Establish `hi' : i = 1 - y * c` using `by linear_combination hyi`. Establish `hdiff : IsLocalization.mk' F a b - algebraMap (𝓞 F) F (y * r') = IsLocalization.mk' F a b * algebraMap (𝓞 F) F i`. Rewrite using `[hi']`. Simplify using `only [map_mul, map_sub, map_one, hr']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdiff, map_mul]`. Establish `hvi : v.valuation F (algebraMap (𝓞 F) F i) < 1` using `(valuation_lt_one_iff_mem v i).mpr hi`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact mul_le_mul_right' hk _`.

Consider the case `gcongr`. Use `_ = v.valuation F (algebraMap (𝓞 F) F i) := one_mul _`. Use `_ < 1 := hvi`.
-/
private theorem exists_ringOfIntegers_valuation_sub_lt_one_of_le (k : F) (hk : v.valuation F k ≤ 1) :
    ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F)) k
  dsimp only at hab
  subst hab
  have hb0 : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hspan : Ideal.span {(b : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb0
  have hfin := Ideal.finite_factors hspan
  have hn : ∀ w : HeightOneSpectrum (𝓞 F),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) ≤ w.intValuation (b : 𝓞 F) := by
    intro w
    rw [intValuation_def, if_neg hb0]
    exact ⟨_, le_rfl⟩
  choose n hn using hn
  have hdist : ∀ i ∈ insert v hfin.toFinset, ∀ j ∈ insert v hfin.toFinset, i ≠ j →
      (fun w : HeightOneSpectrum (𝓞 F) => w.asIdeal) i ≠ (fun w => w.asIdeal) j := by
    intro i _ j _ hij h
    exact hij (HeightOneSpectrum.ext h)
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v hfin.toFinset)
    (fun w : HeightOneSpectrum (𝓞 F) => w.asIdeal)
    (fun w => if w = v then 1 else n w)
    (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime) hdist
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then (1 : 𝓞 F) else 0)
  have hcv : c ∉ v.asIdeal := by
    intro hmem
    have h1 := hc v (Finset.mem_insert_self v _)
    simp at h1
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 := v.asIdeal.sub_mem hmem h1
    simpa using h2
  have hcw : ∀ w ∈ hfin.toFinset, w ≠ v → c ∈ w.asIdeal ^ n w := by
    intro w hw hwv
    have h1 := hc w (Finset.mem_insert_of_mem hw)
    simpa [hwv] using h1
  have key : ∀ w : HeightOneSpectrum (𝓞 F),
      w.valuation F (algebraMap (𝓞 F) F c * IsLocalization.mk' F a b) ≤ 1 := by
    intro w
    have hvc : w.valuation F (algebraMap (𝓞 F) F c) = w.intValuation c :=
      valuation_of_algebraMap w c
    rw [map_mul, hvc]
    by_cases hwv : w = v
    · rw [hwv, intValuation_eq_one_iff.mpr hcv, one_mul]
      exact hk
    · rw [valuation_of_mk']
      have hbne : w.intValuation (b : 𝓞 F) ≠ 0 := by
        exact intValuation_ne_zero w _ hb0
      by_cases hwS : w ∈ hfin.toFinset
      · have hc' : w.intValuation c ≤ w.intValuation (b : 𝓞 F) :=
          ((intValuation_le_pow_iff_mem w c (n w)).mpr (hcw w hwS hwv)).trans (hn w)
        rw [div_eq_mul_inv]
        calc w.intValuation c * (w.intValuation a * (w.intValuation (b : 𝓞 F))⁻¹)
            ≤ w.intValuation (b : 𝓞 F) * (1 * (w.intValuation (b : 𝓞 F))⁻¹) := by
              first
              | exact mul_le_mul' hc' (mul_le_mul_right' (intValuation_le_one w a) _)
              | (gcongr; exact intValuation_le_one w a)
          _ = 1 := by rw [one_mul, mul_inv_cancel₀ hbne]
      · have hb1 : w.intValuation (b : 𝓞 F) = 1 := by
          rw [intValuation_eq_one_iff]
          intro hmem
          exact hwS (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr hmem))
        rw [hb1, div_one]
        exact mul_le_one' (intValuation_le_one w c) (intValuation_le_one w a)
  obtain ⟨r', hr'⟩ := RingHom.mem_range.mp (mem_integers_of_valuation_le_one F _ key)
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hcv
  refine ⟨y * r', ?_⟩
  have hi' : i = 1 - y * c := by linear_combination hyi
  have hdiff : IsLocalization.mk' F a b - algebraMap (𝓞 F) F (y * r') =
      IsLocalization.mk' F a b * algebraMap (𝓞 F) F i := by
    rw [hi']
    simp only [map_mul, map_sub, map_one, hr']
    ring
  rw [hdiff, map_mul]
  have hvi : v.valuation F (algebraMap (𝓞 F) F i) < 1 := (valuation_lt_one_iff_mem v i).mpr hi
  calc v.valuation F (IsLocalization.mk' F a b) * v.valuation F (algebraMap (𝓞 F) F i)
      ≤ 1 * v.valuation F (algebraMap (𝓞 F) F i) := by
        first
        | exact mul_le_mul_right' hk _
        | gcongr
    _ = v.valuation F (algebraMap (𝓞 F) F i) := one_mul _
    _ < 1 := hvi

/- English proof (translation)
Conclude with `valuedAdicCompletion_eq_valuation' v k`.
-/
private theorem valued_algebraMap_adicCompletion_eq_valuation' (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by
  exact valuedAdicCompletion_eq_valuation' v k

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), valued_algebraMap_adicCompletion_eq_valuation']`. Conclude with `valuation_of_algebraMap v a`.
-/
private theorem valued_algebraMap_ringOfIntegers_eq_intValuation (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = v.intValuation a := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), valued_algebraMap_adicCompletion_eq_valuation']
  exact valuation_of_algebraMap v a

/- English proof (translation)
Use `first`. Consider the case `exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.denseRange_coe F v`. Consider the case `exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v`. Consider the case `exact IsDedekindDomain.HeightOneSpectrum.denseRange_coe F v`. Consider the case `exact (v.valuation F).denseRange_coe`.

Consider the case `exact Valuation.Completion.denseRange_coe`. Consider the case `exact UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F))`. Consider the case `(intro x; exact UniformSpace.Completion.denseRange_coe x)`. Consider the case `exact (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F))).comp (WithVal.equiv (v.valuation F)).symm.surjective.denseRange (UniformSpace.Completion.continuous_coe _)`. Consider the case `exact @UniformSpace.Completion.denseRange_coe F v.adicValued.toUniformSpace`.

Consider the case `(letI := v.adicValued; exact UniformSpace.Completion.denseRange_coe)`. Consider the case `(refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F)))`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `first`. Consider the case `exact ⟨WithVal.equiv _ y, rfl⟩`.

Consider the case `exact ⟨WithVal.ofVal y, rfl⟩`. Consider the case `exact ⟨y, rfl⟩`. Consider the case `exact ⟨WithVal.equiv _ y, by simp⟩`. Consider the case `exact ⟨WithVal.ofVal y, by simp⟩)`. Consider the case `(delta IsDedekindDomain.HeightOneSpectrum.adicCompletion`.

Conclude with `UniformSpace.Completion.denseRange_coe)`. Consider the case `(unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion Valuation.Completion`. Use `Dense.mono ?_ UniformSpace.Completion.denseRange_coe` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Use `first`.

Consider the case `exact ⟨WithVal.equiv _ y, rfl⟩`. Consider the case `exact ⟨WithVal.ofVal y, rfl⟩`. Consider the case `exact ⟨y, rfl⟩)`.
-/
private theorem denseRange_algebraMap_adicCompletion' : DenseRange (algebraMap F (v.adicCompletion F)) := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.denseRange_coe F v
  | exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v
  | exact IsDedekindDomain.HeightOneSpectrum.denseRange_coe F v
  | exact (v.valuation F).denseRange_coe
  | exact Valuation.Completion.denseRange_coe
  | exact UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F))
  | (intro x; exact UniformSpace.Completion.denseRange_coe x)
  | exact (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F))).comp
      (WithVal.equiv (v.valuation F)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  | exact @UniformSpace.Completion.denseRange_coe F v.adicValued.toUniformSpace
  | (letI := v.adicValued; exact UniformSpace.Completion.denseRange_coe)
  | (refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F)))
     rintro _ ⟨y, rfl⟩
     first
     | exact ⟨WithVal.equiv _ y, rfl⟩
     | exact ⟨WithVal.ofVal y, rfl⟩
     | exact ⟨y, rfl⟩
     | exact ⟨WithVal.equiv _ y, by simp⟩
     | exact ⟨WithVal.ofVal y, by simp⟩)
  | (delta IsDedekindDomain.HeightOneSpectrum.adicCompletion
     exact UniformSpace.Completion.denseRange_coe)
  | (unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion Valuation.Completion
     refine Dense.mono ?_ UniformSpace.Completion.denseRange_coe
     rintro _ ⟨y, rfl⟩
     first
     | exact ⟨WithVal.equiv _ y, rfl⟩
     | exact ⟨WithVal.ofVal y, rfl⟩
     | exact ⟨y, rfl⟩)

/- English proof (translation)
Take `⟨π, hπp, hπ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Establish `hvP : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) < 1`. Rewrite using `[valued_algebraMap_ringOfIntegers_eq_intValuation]`. Conclude with `(intValuation_lt_one_iff_mem v π).mpr hπp`. Establish `hP0 : algebraMap (𝓞 F) (v.adicCompletion F) π ≠ 0`.

Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Conclude with `(map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hπ0)`. Establish `hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))` using `Valued.isOpen_valuationSubring _`. Establish `hW : IsOpen ((fun y => (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (y - x)) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)))`. Apply `hO.preimage` to reduce the goal to its premises.

Conclude with `continuous_const.mul (continuous_id.sub continuous_const)`. Establish `hxW : x ∈ ((fun y => (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (y - x)) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)))` using `by show (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (x - x) ∈ v.adicCompletionIntegers F`. Rewrite using `[sub_self, mul_zero]`. Conclude with `zero_mem _`. Take `⟨k, hk⟩` from `(denseRange_algebraMap_adicCompletion' F v).exists_mem_open hW ⟨x, hxW⟩`.

Establish `h1 : (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (algebraMap F (v.adicCompletion F) k - x) ∈ v.adicCompletionIntegers F` using `hk`. Establish `h2` using `(mem_adicCompletionIntegers (𝓞 F) F v).mp h1`. Establish `hk' : Valued.v (algebraMap F (v.adicCompletion F) k - x) < 1`. Establish `e : algebraMap F (v.adicCompletion F) k - x = algebraMap (𝓞 F) (v.adicCompletion F) π * ((algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (algebraMap F (v.adicCompletion F) k - x))`. Rewrite using `[mul_inv_cancel_left₀ hP0]`.

Rewrite using `[e, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact mul_le_mul_left' h2 _`. Consider the case `gcongr`. Use `_ < 1 := by rw [mul_one]; exact hvP`.

Establish `hkv : v.valuation F k ≤ 1`. Rewrite using `[← valued_algebraMap_adicCompletion_eq_valuation' F v k]`. Establish `h3` using `Valuation.map_add_le (v := Valued.v) hk'.le hx`. Rewrite `h3` using `[sub_add_cancel]`. Then use the resulting hypothesis. Take `⟨r, hr⟩` from `exists_ringOfIntegers_valuation_sub_lt_one_of_le F v k hkv`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `e : x - algebraMap (𝓞 F) (v.adicCompletion F) r = (x - algebraMap F (v.adicCompletion F) k) + algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r)`. Rewrite using `[map_sub, ← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Valuation.map_add_lt (v := Valued.v) ?_ ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hk'`. Rewrite using `[valued_algebraMap_adicCompletion_eq_valuation']`. Conclude with `hr`.
-/
private theorem exists_ringOfIntegers_valued_sub_lt_one_of_le_one (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  obtain ⟨π, hπp, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hvP : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) < 1 := by
    rw [valued_algebraMap_ringOfIntegers_eq_intValuation]
    exact (intValuation_lt_one_iff_mem v π).mpr hπp
  have hP0 : algebraMap (𝓞 F) (v.adicCompletion F) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hπ0)
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hW : IsOpen ((fun y => (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (y - x)) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    apply hO.preimage
    exact continuous_const.mul (continuous_id.sub continuous_const)
  have hxW : x ∈ ((fun y => (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (y - x)) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    show (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (x - x) ∈ v.adicCompletionIntegers F
    rw [sub_self, mul_zero]
    exact zero_mem _
  obtain ⟨k, hk⟩ := (denseRange_algebraMap_adicCompletion' F v).exists_mem_open hW ⟨x, hxW⟩
  have h1 : (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ *
      (algebraMap F (v.adicCompletion F) k - x) ∈ v.adicCompletionIntegers F := hk
  have h2 := (mem_adicCompletionIntegers (𝓞 F) F v).mp h1
  have hk' : Valued.v (algebraMap F (v.adicCompletion F) k - x) < 1 := by
    have e : algebraMap F (v.adicCompletion F) k - x =
        algebraMap (𝓞 F) (v.adicCompletion F) π * ((algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ *
          (algebraMap F (v.adicCompletion F) k - x)) := by
      rw [mul_inv_cancel_left₀ hP0]
    rw [e, map_mul]
    calc _ ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) * 1 := by
          first
          | exact mul_le_mul_left' h2 _
          | gcongr
      _ < 1 := by rw [mul_one]; exact hvP
  have hkv : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap_adicCompletion_eq_valuation' F v k]
    have h3 := Valuation.map_add_le (v := Valued.v) hk'.le hx
    rwa [sub_add_cancel] at h3
  obtain ⟨r, hr⟩ := exists_ringOfIntegers_valuation_sub_lt_one_of_le F v k hkv
  refine ⟨r, ?_⟩
  have e : x - algebraMap (𝓞 F) (v.adicCompletion F) r =
      (x - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    ring
  rw [e]
  refine Valuation.map_add_lt (v := Valued.v) ?_ ?_
  · rw [Valuation.map_sub_swap]
    exact hk'
  · rw [valued_algebraMap_adicCompletion_eq_valuation']
    exact hr

/- English proof (translation)
Use `show ¬ IsUnit d`. Introduce `hu`. Establish `h1 : Valued.v (d : v.adicCompletion F) = 1`. Conclude with `(Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.mp hu`. Conclude with `(ne_of_lt hd) h1`.
-/
private theorem mem_maximalIdeal_of_valued_lt_one (d : Valued.integer (v.adicCompletion F))
    (hd : Valued.v (d : v.adicCompletion F) < 1) :
    d ∈ IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion F)) := by
  show ¬ IsUnit d
  intro hu
  have h1 : Valued.v (d : v.adicCompletion F) = 1 := by
    exact (Valuation.integer.integers
      (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.mp hu
  exact (ne_of_lt hd) h1

/- English proof (translation)
Set `f0 : 𝓞 F →+* Valued.integer (v.adicCompletion F)` to `(algebraMap (𝓞 F) (v.adicCompletion F)).codRestrict _ (algebraMap_mem_integer F v)`. Set `φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))` to `(IsLocalRing.residue (Valued.integer (v.adicCompletion F))).comp f0`. Establish `hker : ∀ a ∈ v.asIdeal, φ a = 0`. Introduce `a ha`. Use `show IsLocalRing.residue (Valued.integer (v.adicCompletion F)) (f0 a) = 0`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Apply `mem_maximalIdeal_of_valued_lt_one` to reduce the goal to its premises. Use `show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) < 1`. Rewrite using `[valued_algebraMap_ringOfIntegers_eq_intValuation]`. Conclude with `(intValuation_lt_one_iff_mem v a).mpr ha`.

Establish `hsurj : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker)`. Introduce `z`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`. Establish `hx : Valued.v (x : v.adicCompletion F) ≤ 1`. Conclude with `x.2`.

Take `⟨r, hr⟩` from `exists_ringOfIntegers_valued_sub_lt_one_of_le_one F v x hx`. Use `⟨Ideal.Quotient.mk _ r, ?_⟩` and prove the remaining obligations. Use `show φ r = IsLocalRing.residue (Valued.integer (v.adicCompletion F)) x`. Rewrite using `[← sub_eq_zero]`. Use `show IsLocalRing.residue (Valued.integer (v.adicCompletion F)) (f0 r) - IsLocalRing.residue (Valued.integer (v.adicCompletion F)) x = 0`.

Rewrite using `[← map_sub, IsLocalRing.residue_eq_zero_iff]`. Apply `mem_maximalIdeal_of_valued_lt_one` to reduce the goal to its premises. Use `show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r - (x : v.adicCompletion F)) < 1`. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hr`.

Conclude with `Finite.of_surjective _ hsurj`.
-/
theorem finite_residueField :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  classical
  let f0 : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
    (algebraMap (𝓞 F) (v.adicCompletion F)).codRestrict _ (algebraMap_mem_integer F v)
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
    (IsLocalRing.residue (Valued.integer (v.adicCompletion F))).comp f0
  have hker : ∀ a ∈ v.asIdeal, φ a = 0 := by
    intro a ha
    show IsLocalRing.residue (Valued.integer (v.adicCompletion F)) (f0 a) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    apply mem_maximalIdeal_of_valued_lt_one
    show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) < 1
    rw [valued_algebraMap_ringOfIntegers_eq_intValuation]
    exact (intValuation_lt_one_iff_mem v a).mpr ha
  have hsurj : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    have hx : Valued.v (x : v.adicCompletion F) ≤ 1 := by
      exact x.2
    obtain ⟨r, hr⟩ := exists_ringOfIntegers_valued_sub_lt_one_of_le_one F v x hx
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    show φ r = IsLocalRing.residue (Valued.integer (v.adicCompletion F)) x
    rw [← sub_eq_zero]
    show IsLocalRing.residue (Valued.integer (v.adicCompletion F)) (f0 r) -
      IsLocalRing.residue (Valued.integer (v.adicCompletion F)) x = 0
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply mem_maximalIdeal_of_valued_lt_one
    show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r - (x : v.adicCompletion F)) < 1
    rw [Valuation.map_sub_swap]
    exact hr
  exact Finite.of_surjective _ hsurj

instance compactSpace_integer : CompactSpace (Valued.integer (v.adicCompletion F)) := by
  haveI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion F)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  haveI : CompleteSpace (Valued.integer (v.adicCompletion F)) :=
    (Valued.isClosed_integer (v.adicCompletion F)).completeSpace_coe
  haveI := finite_residueField F v
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, this⟩

/- English proof (translation)
Establish `: CompactSpace (Valued.integer (v.adicCompletion F))` using `compactSpace_integer F v`. Conclude with `isCompact_iff_compactSpace.mpr this`.
-/
theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have : CompactSpace (Valued.integer (v.adicCompletion F)) := compactSpace_integer F v
  exact isCompact_iff_compactSpace.mpr this

instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v)
  exact inferInstanceAs (LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

instance locallyCompactSpace_adeleRing : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance t2Space_adeleRing : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end PI.AdicCompletionValuation
