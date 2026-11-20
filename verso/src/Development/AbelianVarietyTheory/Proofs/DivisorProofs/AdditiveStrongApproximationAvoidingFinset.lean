import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import GroundTheory.GlobalFields.Adele.IntegersLattice
import GroundTheory.GlobalFields.Adele.Approximation

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
open Filter

namespace GlobalTheory.AddApproxPlaces

open NumberField.mixedEmbedding MeasureTheory in

/- English proof (translation)
Take `⟨g, hg, hB⟩` from `adjust_f F (f := f) (w₁ := w₀) ((minkowskiBound F 1).toNNReal + 1) (fun w _ => hf w)`. Establish `h : minkowskiBound F 1 < volume (convexBodyLT F g)`. Rewrite using `[convexBodyLT_volume, hB, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← ENNReal.coe_mul, ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]`. Conclude with `(lt_add_one _).trans_le (le_mul_of_one_le_left zero_le (one_le_convexBodyLTFactor F))`. Take `⟨a, ha, hlt⟩` from `exists_ne_zero_mem_ringOfIntegers_lt F h`.

Use `⟨a, RingOfIntegers.coe_ne_zero_iff.2 ha, fun w hw => ?_, fun v => v.valuation_le_one a⟩` and prove the remaining obligations. Rewrite using `[← hg w hw]`. Conclude with `hlt w`.
-/
theorem exists_small_of_infinitePlace (F : Type) [Field F] [NumberField F] (w₀ : InfinitePlace F)
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w ≠ w₀ → w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F g ≤ 1 := by
  classical
  obtain ⟨g, hg, hB⟩ := adjust_f F (f := f) (w₁ := w₀) ((minkowskiBound F 1).toNNReal + 1) (fun w _ => hf w)
  have h : minkowskiBound F 1 < volume (convexBodyLT F g) := by
    rw [convexBodyLT_volume, hB, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← ENNReal.coe_mul,
      ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]
    exact (lt_add_one _).trans_le (le_mul_of_one_le_left zero_le (one_le_convexBodyLTFactor F))
  obtain ⟨a, ha, hlt⟩ := exists_ne_zero_mem_ringOfIntegers_lt F h
  refine ⟨a, RingOfIntegers.coe_ne_zero_iff.2 ha, fun w hw => ?_, fun v => v.valuation_le_one a⟩
  rw [← hg w hw]; exact hlt w

open NumberField.mixedEmbedding MeasureTheory nonZeroDivisors in

/- English proof (translation)
Use `set P : NNReal := convexBodyLTFactor F * ∏ w, (f w) ^ (w.mult) with hP`. Establish `hP0 : 0 < P` using `pos_iff_ne_zero.2 (mul_ne_zero (convexBodyLTFactor_ne_zero F) (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hf w)))`. Use `set B : NNReal := (minkowskiBound F 1).toNNReal with hB`. Establish `hN : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ)`. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm p` after adjusting the coercions.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt ((B : ℝ) / P) hN`. Establish `hJ : ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ p.ne_bot)`. Set `I : (FractionalIdeal (𝓞 F)⁰ F)ˣ` to `(Units.mk0 _ hJ)⁻¹`. Establish `hI : minkowskiBound F I = ENNReal.ofReal (((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹) * minkowskiBound F 1`. Unfold `minkowskiBound`.

Rewrite using `[volume_fundamentalDomain_fractionalIdealLatticeBasis F 1]`. Simplify using `only [volume_fundamentalDomain_fractionalIdealLatticeBasis, I, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, Units.val_one, map_one, map_pow]`. Simplify using `[mul_assoc]`. Establish `h : minkowskiBound F I < volume (convexBodyLT F f)`. Establish `hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ k` using `by positivity`.

Rewrite using `[hI, convexBodyLT_volume, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← hB, ← ENNReal.coe_mul, ← hP, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hP0), inv_mul_lt_iff₀ hp …`. Conclude with `(div_lt_iff₀ (by exact_mod_cast hP0)).1 hk`. Take `⟨a, ha, ha0, hlt⟩` from `exists_ne_zero_mem_ideal_lt F I h`. Use `⟨a, ha0, hlt, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hnle : ¬ p.asIdeal ^ k ≤ v.asIdeal` using `fun hle => hv (HeightOneSpectrum.ext (p.isMaximal.eq_of_le v.isPrime.ne_top (v.isPrime.le_of_pow_le hle)).symm)`.

Take `⟨b, hb, hbv⟩` from `SetLike.not_le_iff_exists.1 hnle`. Establish `ha' : a ∈ ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹`. Simplify `ha` using `[I]`. Establish `hab` using `(FractionalIdeal.mem_inv_iff hJ).1 ha' (algebraMap (𝓞 F) F b) (FractionalIdeal.mem_coeIdeal_of_mem _ hb)`. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 hab`.

Establish `h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1` using `le_antisymm (v.valuation_le_one b) (not_lt.1 fun h => hbv ((v.valuation_lt_one_iff_mem b).1 h))`. Establish `h2 : v.valuation F (algebraMap (𝓞 F) F c) ≤ 1` using `v.valuation_le_one c`. Rewrite `h2` using `[hc, map_mul, h1, mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_small_of_finitePlace (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ p → v.valuation F g ≤ 1 := by
  classical
  set P : NNReal := convexBodyLTFactor F * ∏ w, (f w) ^ (w.mult) with hP
  have hP0 : 0 < P := pos_iff_ne_zero.2 (mul_ne_zero (convexBodyLTFactor_ne_zero F)
    (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hf w)))
  set B : NNReal := (minkowskiBound F 1).toNNReal with hB
  have hN : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((B : ℝ) / P) hN
  have hJ : ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ p.ne_bot)
  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := (Units.mk0 _ hJ)⁻¹
  have hI : minkowskiBound F I = ENNReal.ofReal (((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹) * minkowskiBound F 1 := by
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis F 1]
    simp only [volume_fundamentalDomain_fractionalIdealLatticeBasis, I, Units.val_inv_eq_inv_val,
      Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, Units.val_one, map_one, map_pow]
    simp [mul_assoc]
  have h : minkowskiBound F I < volume (convexBodyLT F f) := by
    have hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ k := by positivity
    rw [hI, convexBodyLT_volume, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← hB, ← ENNReal.coe_mul, ← hP,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hP0), inv_mul_lt_iff₀ hpos]
    exact (div_lt_iff₀ (by exact_mod_cast hP0)).1 hk
  obtain ⟨a, ha, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt F I h
  refine ⟨a, ha0, hlt, fun v hv => ?_⟩
  have hnle : ¬ p.asIdeal ^ k ≤ v.asIdeal := fun hle =>
    hv (HeightOneSpectrum.ext (p.isMaximal.eq_of_le v.isPrime.ne_top (v.isPrime.le_of_pow_le hle)).symm)
  obtain ⟨b, hb, hbv⟩ := SetLike.not_le_iff_exists.1 hnle
  have ha' : a ∈ ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simpa [I] using ha
  have hab := (FractionalIdeal.mem_inv_iff hJ).1 ha' (algebraMap (𝓞 F) F b)
    (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hab
  have h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1 :=
    le_antisymm (v.valuation_le_one b) (not_lt.1 fun h => hbv ((v.valuation_lt_one_iff_mem b).1 h))
  have h2 : v.valuation F (algebraMap (𝓞 F) F c) ≤ 1 := v.valuation_le_one c
  rwa [hc, map_mul, h1, mul_one] at h2

/- English proof (translation)
Establish `hM : ∀ᶠ a in 𝓝 (0 : Af F), ∀ c ∈ {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}, a * c ∈ N`. Use `(GlobalTheory.AdeleCocompact.isCompact_integral F).eventually_forall_of_forall_eventually fun c _ => ?_` and prove the remaining obligations. Establish `hcont : Continuous (fun p : Af F × Af F => p.1 * p.2)` using `by fun_prop`. Conclude with `hcont.continuousAt.eventually_mem (by simpa using hN)`. Take `⟨n, hn⟩` from `((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually hM).exists`.

Establish `h0 : ((n.factorial : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 n.factorial_ne_zero`. Use `⟨(n.factorial : ℕ), Nat.cast_ne_zero.2 n.factorial_ne_zero, fun y hy => ?_⟩` and prove the remaining obligations. Establish `e : y = ((n.factorial : ℕ) : Af F) * (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y)`. Rewrite using `[← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]`. Rewrite using `[e]`.

Use `hn _ fun v => ?_` and prove the remaining obligations. Establish `e' : (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) v = (((((n.factorial : ℕ) : F)⁻¹ : F)) : v.adicCompletion F) * evalV F v y` using `rfl`. Rewrite using `[e', HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]`. Establish `h1` using `hy v`. Rewrite `h1` using `[map_natCast]`.

Establish `h2 : v.valuation F ((n.factorial : ℕ) : F) ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Conclude with `(inv_mul_le_one₀ (pos_iff_ne_zero.2 h2)).2 h1`.
-/
theorem exists_int_nhds_finite (F : Type) [Field F] [NumberField F] (N : Set (Af F)) (hN : N ∈ 𝓝 (0 : Af F)) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ y : Af F,
      (∀ v, Valued.v (evalV F v y) ≤ v.valuation F (algebraMap (𝓞 F) F m)) → y ∈ N := by
  have hM : ∀ᶠ a in 𝓝 (0 : Af F), ∀ c ∈ {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}, a * c ∈ N := by
    refine (GlobalTheory.AdeleCocompact.isCompact_integral F).eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : Af F × Af F => p.1 * p.2) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hN)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually hM).exists
  have h0 : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  refine ⟨(n.factorial : ℕ), Nat.cast_ne_zero.2 n.factorial_ne_zero, fun y hy => ?_⟩
  have e : y = ((n.factorial : ℕ) : Af F) * (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) := by
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  rw [e]
  refine hn _ fun v => ?_
  have e' : (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) v =
      (((((n.factorial : ℕ) : F)⁻¹ : F)) : v.adicCompletion F) * evalV F v y := rfl
  rw [e', HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have h1 := hy v
  rw [map_natCast] at h1
  have h2 : v.valuation F ((n.factorial : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  exact (inv_mul_le_one₀ (pos_iff_ne_zero.2 h2)).2 h1

/- English proof (translation)
Establish `hN' : N ∈ 𝓝 (0 : (w : InfinitePlace F) → w.Completion)` using `hN`. Take `⟨δ, hδ, h⟩` from `Metric.mem_nhds_iff.1 hN'`. Conclude with `⟨δ, hδ, fun y hy => h (mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 hy))⟩`.
-/
theorem exists_delta_nhds_infinite (F : Type) [Field F] [NumberField F] (N : Set (Ainf F))
    (hN : N ∈ 𝓝 (0 : Ainf F)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Ainf F, (∀ w, ‖y w‖ < δ) → y ∈ N := by
  have hN' : N ∈ 𝓝 (0 : (w : InfinitePlace F) → w.Completion) := hN
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hN'
  exact ⟨δ, hδ, fun y hy => h (mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 hy))⟩

/- English proof (translation)
Establish `hm' : algebraMap (𝓞 F) F m ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 hm`. Establish `hw : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F m)` using `fun w => InfinitePlace.pos_iff.2 hm'`. Set `f : InfinitePlace F → NNReal` to `fun w => ⟨δ / w (algebraMap (𝓞 F) F m), (div_pos hδ (hw w)).le⟩`. Establish `hf : ∀ w, f w ≠ 0` using `fun w => NNReal.coe_ne_zero.1 (div_pos hδ (hw w)).ne'`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg, h1, h2⟩ : ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < f w) ∧ ∀ v, v ∉ S₂ → v.valuation F g ≤ 1 := by`.

Break down `hS with ⟨w₀, hw₀⟩ | ⟨p, hp⟩` into its components or cases. Take `⟨g, hg, h1, h2⟩` from `exists_small_of_infinitePlace F w₀ f hf`. Conclude with `⟨g, hg, fun w hw => h1 w (fun h => hw (h ▸ hw₀)), fun v _ => h2 v⟩`. Take `⟨g, hg, h1, h2⟩` from `exists_small_of_finitePlace F p f hf`. Conclude with `⟨g, hg, fun w _ => h1 w, fun v hv => h2 v (fun h => hv (h ▸ hp))⟩`.

Use `⟨g * algebraMap (𝓞 F) F m, mul_ne_zero hg hm', fun w hw' => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(lt_div_iff₀ (hw w)).1 (h1 w hw')`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_left' (h2 v hv)`.
-/
theorem exists_small (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (hS : S₁.Nonempty ∨ S₂.Nonempty)
    (m : 𝓞 F) (hm : m ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < δ) ∧
      ∀ v, v ∉ S₂ → v.valuation F g ≤ v.valuation F (algebraMap (𝓞 F) F m) := by
  have hm' : algebraMap (𝓞 F) F m ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hm
  have hw : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F m) := fun w => InfinitePlace.pos_iff.2 hm'
  let f : InfinitePlace F → NNReal := fun w => ⟨δ / w (algebraMap (𝓞 F) F m), (div_pos hδ (hw w)).le⟩
  have hf : ∀ w, f w ≠ 0 := fun w => NNReal.coe_ne_zero.1 (div_pos hδ (hw w)).ne'
  obtain ⟨g, hg, h1, h2⟩ : ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < f w) ∧ ∀ v, v ∉ S₂ → v.valuation F g ≤ 1 := by
    rcases hS with ⟨w₀, hw₀⟩ | ⟨p, hp⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_infinitePlace F w₀ f hf
      exact ⟨g, hg, fun w hw => h1 w (fun h => hw (h ▸ hw₀)), fun v _ => h2 v⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_finitePlace F p f hf
      exact ⟨g, hg, fun w _ => h1 w, fun v hv => h2 v (fun h => hv (h ▸ hp))⟩
  refine ⟨g * algebraMap (𝓞 F) F m, mul_ne_zero hg hm', fun w hw' => ?_, fun v hv => ?_⟩
  · rw [map_mul]
    exact (lt_div_iff₀ (hw w)).1 (h1 w hw')
  · rw [map_mul]
    exact mul_le_of_le_one_left' (h2 v hv)

/- English proof (translation)
Establish `hN' : N ∈ 𝓝 ((0 : Ainf F), (0 : Af F))` using `hN`. Take `⟨N₁, hN₁, N₂, hN₂, hsub⟩` from `mem_nhds_prod_iff.1 hN'`. Take `⟨δ, hδ, hδN⟩` from `exists_delta_nhds_infinite F N₁ hN₁`. Take `⟨m, hm, hmN⟩` from `exists_int_nhds_finite F N₂ hN₂`. Take `⟨g, hg, h1, h2⟩` from `exists_small F S₁ S₂ hS m hm δ hδ`.

Use `⟨g, hg, hsub ⟨?_, ?_⟩⟩` and prove the remaining obligations. Apply `hδN` to reduce the goal to its premises. Introduce `w`. Establish `e : ((1 - ε) * algebraMap F (AF F) g).1 w = (1 - fstA F ε w) * (g : w.Completion)`. Express the relevant statement in the definitionally equal form `(fstA F ((1 - ε) * algebraMap F (AF F) g)) w = _`.

Rewrite using `[map_mul, map_sub, map_one, AlgHom.commutes]`. Both sides reduce to the same expression. Rewrite using `[e]`. Distinguish the cases in `hw : w ∈ S₁`. Rewrite using `[hε.1 w hw, sub_self, zero_mul, norm_zero]`.

Conclude with `hδ`. Rewrite using `[hε.2.1 w hw, sub_zero, one_mul]`. Use `GroundTheory.Global.norm_algebraMap_apply (K := F) g w` as an intermediate fact. Conclude with `(this.trans_lt (h1 w hw))`. Apply `hmN` to reduce the goal to its premises.

Introduce `v`. Establish `e : evalV F v ((1 - ε) * algebraMap F (AF F) g).2 = (1 - evalV F v (sndA F ε)) * (g : v.adicCompletion F)`. Express the relevant statement in the definitionally equal form `evalV F v (sndA F ((1 - ε) * algebraMap F (AF F) g)) = _`. Rewrite using `[map_mul, map_mul, map_sub, map_sub, map_one, map_one, AlgHom.commutes, AlgHom.commutes]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Distinguish the cases in `hv : v ∈ S₂`. Rewrite using `[hε.2.2.1 v hv, sub_self, zero_mul, map_zero]`. Conclude with `zero_le'`. Rewrite using `[hε.2.2.2 v hv, sub_zero, one_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `h2 v hv`.
-/
theorem exists_small_adele (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsPlacesIdem S₁ S₂ ε)
    (hS : S₁.Nonempty ∨ S₂.Nonempty) (N : Set (AF F)) (hN : N ∈ 𝓝 (0 : AF F)) :
    ∃ f : F, f ≠ 0 ∧ (1 - ε) * algebraMap F (AF F) f ∈ N := by
  have hN' : N ∈ 𝓝 ((0 : Ainf F), (0 : Af F)) := hN
  obtain ⟨N₁, hN₁, N₂, hN₂, hsub⟩ := mem_nhds_prod_iff.1 hN'
  obtain ⟨δ, hδ, hδN⟩ := exists_delta_nhds_infinite F N₁ hN₁
  obtain ⟨m, hm, hmN⟩ := exists_int_nhds_finite F N₂ hN₂
  obtain ⟨g, hg, h1, h2⟩ := exists_small F S₁ S₂ hS m hm δ hδ
  refine ⟨g, hg, hsub ⟨?_, ?_⟩⟩
  · apply hδN
    intro w
    have e : ((1 - ε) * algebraMap F (AF F) g).1 w = (1 - fstA F ε w) * (g : w.Completion) := by
      change (fstA F ((1 - ε) * algebraMap F (AF F) g)) w = _
      rw [map_mul, map_sub, map_one, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, sub_self, zero_mul, norm_zero]; exact hδ
    · rw [hε.2.1 w hw, sub_zero, one_mul]
      have := GroundTheory.Global.norm_algebraMap_apply (K := F) g w
      exact (this.trans_lt (h1 w hw))
  · apply hmN
    intro v
    have e : evalV F v ((1 - ε) * algebraMap F (AF F) g).2 =
        (1 - evalV F v (sndA F ε)) * (g : v.adicCompletion F) := by
      change evalV F v (sndA F ((1 - ε) * algebraMap F (AF F) g)) = _
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one, AlgHom.commutes, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, sub_self, zero_mul, map_zero]; exact zero_le'
    · rw [hε.2.2.2 v hv, sub_zero, one_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact h2 v hv

/- English proof (translation)
Introduce `F _ _ S₁ S₂ ε hε hS x U hU Z`. Establish `hc : Tendsto (fun p : AF F × AF F => x + (p.1 + p.2)) (𝓝 ((0 : AF F), (0 : AF F))) (𝓝 x)`. Establish `: Continuous (fun p : AF F × AF F => x + (p.1 + p.2))` using `by fun_prop`. Simplify using `using this.tendsto ((0 : AF F), (0 : AF F))`. Take `⟨V₁, hV₁, V₂, hV₂, hV⟩` from `mem_nhds_prod_iff.1 (hc hU)`.

Take `⟨C, hC, hCF⟩` from `GlobalTheory.AdeleCocompact.exists_compact_adele F`. Establish `hM : ∀ᶠ a in 𝓝 (0 : AF F), ∀ c ∈ C, -(a * c) ∈ V₁`. Use `hC.eventually_forall_of_forall_eventually fun c _ => ?_` and prove the remaining obligations. Establish `hcont : Continuous (fun p : AF F × AF F => -(p.1 * p.2))` using `by fun_prop`. Conclude with `hcont.continuousAt.eventually_mem (by simpa using hV₁)`.

Take `⟨f, hf, hfM⟩` from `exists_small_adele F S₁ S₂ ε hε hS _ hM`. Take `⟨t₀, ht₀⟩` from `hCF (algebraMap F (AF F) f⁻¹ * x)`. Use `set c := algebraMap F (AF F) f⁻¹ * x - algebraMap F (AF F) t₀ with hc_def`. Establish `hd₁ : -((1 - ε) * algebraMap F (AF F) f * c) ∈ V₁` using `hfM c ht₀`. Establish `hff : algebraMap F (AF F) f * algebraMap F (AF F) f⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel₀ hf, map_one]`. Establish `e₁ : algebraMap F (AF F) (f * t₀) + ε * (algebraMap F (AF F) f * c) = x + -((1 - ε) * algebraMap F (AF F) f * c)`. Rewrite using `[hc_def, map_mul]`. Take the linear combination `x * hff`. Use `set n := Z.card with hn`.

Establish `hM₂ : ∀ᶠ a in 𝓝 (0 : AF F), ∀ q ∈ Finset.range (n + 1), ((q : ℕ) : AF F) * a ∈ V₂`. Use `(Filter.eventually_all_finset _).2 fun q _ => ?_` and prove the remaining obligations. Establish `hcont : Continuous (fun a : AF F => ((q : ℕ) : AF F) * a)` using `by fun_prop`. Conclude with `hcont.continuousAt.eventually_mem (by simpa using hV₂)`. Take `⟨f₂, hf₂, hf₂M⟩` from `exists_small_adele F S₁ S₂ ε hε hS _ hM₂`.

Choose the witnesses or unpack the hypotheses as in `⟨q, hq, hqZ⟩ : ∃ q ∈ Finset.range (n + 1), f * t₀ + (q : F) * f₂ ∉ Z := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hinj : Set.InjOn (fun q : ℕ => f * t₀ + (q : F) * f₂) (Finset.range (n + 1) : Set ℕ)`. Introduce `a _ b _ hab`.

Establish `: (a : F) * f₂ = (b : F) * f₂` using `add_left_cancel hab`. Conclude with `mul_right_cancel₀ hf₂ this` after adjusting the coercions. Use `Finset.card_le_card_of_injOn _ (fun a ha => hcon a ha) hinj` as an intermediate fact. Simplify using `[hn] at this`. Use `⟨f * t₀ + (q : F) * f₂, hqZ, algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂), ?_⟩` and prove the remaining obligations.

Establish `e₂ : algebraMap F (AF F) (f * t₀ + (q : F) * f₂) + ε * (algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂)) = x + (-((1 - ε) * algebraMap F (AF F) f * c) + ((q : ℕ) : AF F) * ((1 - ε) * algebraMap F (AF F) f₂))`. Rewrite using `[map_add, map_mul (algebraMap F (AF F)) (q : F) f₂, map_natCast]`. Take the linear combination `e₁`. Rewrite using `[e₂]`. Conclude with `hV (Set.mk_mem_prod hd₁ (hf₂M q hq))`.
-/
theorem exists_approx_notMem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 x → ∀ Z : Finset F, ∃ t : F, t ∉ Z ∧ ∃ s : AF F, algebraMap F (AF F) t + ε * s ∈ U := by
  intro F _ _ S₁ S₂ ε hε hS x U hU Z
  have hc : Tendsto (fun p : AF F × AF F => x + (p.1 + p.2)) (𝓝 ((0 : AF F), (0 : AF F))) (𝓝 x) := by
    have : Continuous (fun p : AF F × AF F => x + (p.1 + p.2)) := by fun_prop
    simpa using this.tendsto ((0 : AF F), (0 : AF F))
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.1 (hc hU)
  obtain ⟨C, hC, hCF⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hM : ∀ᶠ a in 𝓝 (0 : AF F), ∀ c ∈ C, -(a * c) ∈ V₁ := by
    refine hC.eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : AF F × AF F => -(p.1 * p.2)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₁)
  obtain ⟨f, hf, hfM⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM
  obtain ⟨t₀, ht₀⟩ := hCF (algebraMap F (AF F) f⁻¹ * x)
  set c := algebraMap F (AF F) f⁻¹ * x - algebraMap F (AF F) t₀ with hc_def
  have hd₁ : -((1 - ε) * algebraMap F (AF F) f * c) ∈ V₁ := hfM c ht₀
  have hff : algebraMap F (AF F) f * algebraMap F (AF F) f⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hf, map_one]
  have e₁ : algebraMap F (AF F) (f * t₀) + ε * (algebraMap F (AF F) f * c) =
      x + -((1 - ε) * algebraMap F (AF F) f * c) := by
    rw [hc_def, map_mul]
    linear_combination x * hff

  set n := Z.card with hn
  have hM₂ : ∀ᶠ a in 𝓝 (0 : AF F), ∀ q ∈ Finset.range (n + 1), ((q : ℕ) : AF F) * a ∈ V₂ := by
    refine (Filter.eventually_all_finset _).2 fun q _ => ?_
    have hcont : Continuous (fun a : AF F => ((q : ℕ) : AF F) * a) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₂)
  obtain ⟨f₂, hf₂, hf₂M⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM₂
  obtain ⟨q, hq, hqZ⟩ : ∃ q ∈ Finset.range (n + 1), f * t₀ + (q : F) * f₂ ∉ Z := by
    by_contra hcon
    push_neg at hcon
    have hinj : Set.InjOn (fun q : ℕ => f * t₀ + (q : F) * f₂) (Finset.range (n + 1) : Set ℕ) := by
      intro a _ b _ hab
      have : (a : F) * f₂ = (b : F) * f₂ := add_left_cancel hab
      exact_mod_cast mul_right_cancel₀ hf₂ this
    have := Finset.card_le_card_of_injOn _ (fun a ha => hcon a ha) hinj
    simp [hn] at this
  refine ⟨f * t₀ + (q : F) * f₂, hqZ, algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂), ?_⟩
  have e₂ : algebraMap F (AF F) (f * t₀ + (q : F) * f₂) +
      ε * (algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂)) =
      x + (-((1 - ε) * algebraMap F (AF F) f * c) + ((q : ℕ) : AF F) * ((1 - ε) * algebraMap F (AF F) f₂)) := by
    rw [map_add, map_mul (algebraMap F (AF F)) (q : F) f₂, map_natCast]
    linear_combination e₁
  rw [e₂]
  exact hV (Set.mk_mem_prod hd₁ (hf₂M q hq))

end GlobalTheory.AddApproxPlaces

end
