import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBound
open NumberField IsDedekindDomain GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.EulerLocVol

/- English proof (translation)
Unfold `locFactor resOrder`. Rewrite using `[if_pos hw]`. Use `set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef`. Use `set c := IsCMField.ringOfIntegersComplexConj E with hcdef`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => by ext; simp [hcdef]`.

Establish `hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a` using `fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩`. Establish `hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E)`. Rewrite using `[hwdef, Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Express the relevant statement in the definitionally equal form `c _ ∈ _`. Rewrite using `[hfix]`. Conclude with `Ideal.mem_map_of_mem _ ha`. Establish `hw0 : w ≠ ⊥`. Rewrite using `[hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`.

Conclude with `v.ne_bot`. Use `haveI hmax : w.IsMaximal := hw.isMaximal hw0`. Use `letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w`. Use `haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0`. Set `σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w)` to `Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle`.

Establish `hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x)` using `fun x => rfl`. Use `letI : StarRing (𝓞 E ⧸ w) := { star := σ star_involutive := fun x => by`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Express the relevant statement in the definitionally equal form `σ (σ _) = _`. Rewrite using `[hσ, hσ, hcc]`.

Use `star_mul := fun x y => by`. Express the relevant statement in the definitionally equal form `σ (x * y) = σ y * σ x`. Rewrite using `[map_mul, mul_comm]`. Use `star_add := fun x y => map_add σ x y }`. Establish `hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x)` using `hσ`.

Rewrite using `[ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]`. Use `set q := Ideal.absNorm v.asIdeal with hq`. Establish `hK : Nat.card (𝓞 E ⧸ w) = q ^ 2`. Establish `h` using `Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal`. Rewrite `h` using `[← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E, Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _), Submodule.cardQuot_apply]`.

Conclude with `h`. Establish `hq2 : 2 ≤ q` using `GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK`. Establish `hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a`. Set `f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w)` to `Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map`. Establish `hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a)` using `fun a => rfl`.

Use `exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨a, ha⟩` from `(IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1 (by change c _ = _; rw [map_add, hcc, add_comm])`. Conclude with `⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add]⟩`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Take `⟨a, ha⟩` from `(IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1 (by change c _ = _; rw [map_mul, hcc, mul_comm])`. Conclude with `⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩`. Use `haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`. Establish `h1` using `Nat.card_le_card_of_surjective f hsurj`. Establish `h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q`.

Rewrite using `[hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite `h1` using `[hK, h2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h` using `GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr`. Establish `h'` using `congrArg (Rat.cast : ℚ → ℝ) h`.

Move the coercions through the operations in `at h'`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Rewrite using `[h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq0.ne')]`.
-/
theorem locFactor_eq_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (-1) ^ i * ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add, hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq0.ne')]

/- English proof (translation)
Use `set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef`. Establish `hq1 : (1 : ℝ) ≤ q`. Establish `: Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`.

Rewrite using `[hqdef]`. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Establish `ht : ∀ i : ℕ, 0 ≤ (q ^ i)⁻¹ ∧ (q ^ i)⁻¹ ≤ 1` using `fun i => ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hq1)⟩`. Establish `hg0 : 0 ≤ ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹)` using `Finset.prod_nonneg fun i _ => sub_nonneg.2 (ht i).2`. Establish `hg1 : ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) ≤ 1` using `Finset.prod_le_one (fun i _ => sub_nonneg.2 (ht i).2) fun i _ => sub_le_self _ (ht i).1`.

Distinguish the cases in `hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime`. Rewrite using `[locFactor_eq_of_isPrime E r v hr hp, ← hqdef, ← Finset.prod_mul_distrib]`. Establish `hf0 : ∀ i : ℕ, 0 ≤ 1 - (-1) ^ i * (q ^ i)⁻¹`. Introduce `i`. Take `⟨h0, h1⟩` from `ht i`.

Apply the tactic sequence `rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> linarith`. Use `⟨Finset.prod_nonneg fun i _ => hf0 i, ?_⟩` and prove the remaining obligations. Use `Finset.prod_le_one (fun i _ => mul_nonneg (hf0 i) (sub_nonneg.2 (ht i).2)) fun i _ => ?_` and prove the remaining obligations. Take `⟨h0, h1⟩` from `ht i`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> nlinarith`.

Establish `heq : locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹)`. Set `_ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)` to `Ideal.Quotient.field _`. Establish `hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `h` using `GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr`.

Establish `hq : (0 : ℝ) < q` using `by linarith`. Unfold `locFactor resOrder`. Rewrite using `[if_neg hp]`. Establish `h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) = q ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹)`. Use `congrArg (fun x : ℚ => (x : ℝ)) h` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[h', ← hqdef, mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]`. Rewrite using `[heq]`. Conclude with `⟨hg0, mul_le_one₀ hg1 hg0 hg1⟩`.
-/
theorem locFactor_nonneg_and_mul_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r) :
    0 ≤ locFactor E r v ∧
      locFactor E r v * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ 1 := by
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hq1 : (1 : ℝ) ≤ q := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    rw [hqdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have ht : ∀ i : ℕ, 0 ≤ (q ^ i)⁻¹ ∧ (q ^ i)⁻¹ ≤ 1 := fun i =>
    ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hq1)⟩
  have hg0 : 0 ≤ ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (ht i).2
  have hg1 : ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) ≤ 1 :=
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (ht i).2) fun i _ => sub_le_self _ (ht i).1
  by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
  · rw [locFactor_eq_of_isPrime E r v hr hp, ← hqdef, ← Finset.prod_mul_distrib]
    have hf0 : ∀ i : ℕ, 0 ≤ 1 - (-1) ^ i * (q ^ i)⁻¹ := by
      intro i
      obtain ⟨h0, h1⟩ := ht i
      rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> linarith
    refine ⟨Finset.prod_nonneg fun i _ => hf0 i, ?_⟩
    refine Finset.prod_le_one (fun i _ => mul_nonneg (hf0 i) (sub_nonneg.2 (ht i).2)) fun i _ => ?_
    obtain ⟨h0, h1⟩ := ht i
    rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> nlinarith
  · have heq : locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) := by
      let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
      have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
      have hq : (0 : ℝ) < q := by linarith
      unfold locFactor resOrder
      rw [if_neg hp]
      have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
          q ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) h
        push_cast at this
        exact this
      rw [h', ← hqdef, mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]
    rw [heq]
    exact ⟨hg0, mul_le_one₀ hg1 hg0 hg1⟩

/- English proof (translation)
Introduce `E _ _ _ r hr hm`. Set `g : ℝ → ℝ` to `fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)`. Use `set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef`. Establish `hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i`. Introduce `i hi`.

Establish `hi2 : 2 ≤ i` using `(Finset.mem_Icc.1 hi).1`. Establish `hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i)`. Use `(summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))` as an intermediate fact. Simplify using `using this`. Use `hs.le_tsum 0 (fun j _ => by positivity)` as an intermediate fact.

Simplify using `using this`. Establish `hZ : 0 < Z` using `Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)`. Establish `hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E)`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Unfold `fdeg`.

Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h2]`. Use linear arithmetic over natural numbers and integers. Establish `g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x` using `fun x hx => Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))`. Establish `g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1` using `fun x hx => Finset.prod_le_one (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))) fun i _ => sub_le_self _ (by positivity)`. Establish `g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y` using `fun x y hx hxy => Finset.prod_le_prod (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))) fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _`.

Establish `hloc : ∀ v, 0 ≤ locFactor E r v ∧ locFactor E r v * g (Ideal.absNorm v.asIdeal) ≤ 1` using `fun v => locFactor_nonneg_and_mul_le_one E r v (by omega)`. Set `pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ` to `ReciprocityTheory.Neutral.Bridge.ratPrimeBelow`. Establish `hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal`. Introduce `v`. Establish `hp` using `ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v`.

Take `⟨f, hfv⟩` from `ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `v.isPrime.ne_top`. Establish `hf0 : f ≠ 0` using `by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv`.

Use `⟨hp, ?_⟩` and prove the remaining obligations. Rewrite using `[hfv]`. Conclude with `Nat.le_self_pow hf0 _`. Establish `key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∏ v ∈ s, locFactor E r v ≤ Z ^ fdeg E`. Introduce `s`.

Use `set T := s.image pv`. Establish `hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p`. Introduce `p hp`. Take `⟨v, -, rfl⟩` from `Finset.mem_image.1 hp`. Conclude with `(hN v).1.one_lt.le` after adjusting the coercions.

Establish `s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal)`. Use `Finset.prod_le_prod (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le)) fun v _ => g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)` and prove the remaining obligations. Establish `s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card`. Rewrite using `[Finset.prod_comp (fun p : ℕ => g p) pv]`. Establish `s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card`.

Use `Finset.prod_le_prod (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_` and prove the remaining obligations. Use `pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_` and prove the remaining obligations. Rewrite using `[hf]`. Take `⟨v, -, rfl⟩` from `Finset.mem_image.1 hp`. Conclude with `ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1`.

Establish `s4 : Z⁻¹ ≤ ∏ p ∈ T, g p`. Rewrite using `[Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]`. Use `Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_` and prove the remaining obligations. Use `GlobalTheory.EulerLocVol.inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_` and prove the remaining obligations. Take `⟨v, -, rfl⟩` from `Finset.mem_image.1 hp`.

Conclude with `(hN v).1`. Establish `hlow : (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal)`. Combine the equalities or inequalities in the displayed calculation. Establish `hL0 : 0 ≤ ∏ v ∈ s, locFactor E r v` using `Finset.prod_nonneg fun v _ => (hloc v).1`. Establish `hprod : (∏ v ∈ s, locFactor E r v) * ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) ≤ 1`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_le_one (fun v _ => mul_nonneg (hloc v).1 (g_nonneg _ ?_)) fun v _ => (hloc v).2` and prove the remaining obligations. Establish `: Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`.

Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Establish `hZf : 0 < Z ^ fdeg E` using `pow_pos hZ _`. Establish `h3 : (∏ v ∈ s, locFactor E r v) * (Z ^ fdeg E)⁻¹ ≤ 1` using `(mul_le_mul_of_nonneg_left hlow hL0).trans hprod`. Rewrite `h3` using `[← div_eq_mul_inv, div_le_one hZf]`. Then use the resulting hypothesis. Conclude with `le_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)`.
-/
theorem tprod_locFactor_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (GlobalTheory.SUVol.locFactor E r) →
      ∏' v, GlobalTheory.SUVol.locFactor E r v ≤
        (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, 0 ≤ locFactor E r v ∧ locFactor E r v * g (Ideal.absNorm v.asIdeal) ≤ 1 :=
    fun v => locFactor_nonneg_and_mul_le_one E r v (by omega)
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      ∏ v ∈ s, locFactor E r v ≤ Z ^ fdeg E := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) := by
      refine Finset.prod_le_prod (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
      refine GlobalTheory.EulerLocVol.inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    have hlow : (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) :=
      calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
        _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
        _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
        _ ≤ _ := s3
        _ = _ := s2.symm
        _ ≤ _ := s1
    have hL0 : 0 ≤ ∏ v ∈ s, locFactor E r v := Finset.prod_nonneg fun v _ => (hloc v).1
    have hprod : (∏ v ∈ s, locFactor E r v) * ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) ≤ 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_one (fun v _ => mul_nonneg (hloc v).1 (g_nonneg _ ?_)) fun v _ => (hloc v).2
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hZf : 0 < Z ^ fdeg E := pow_pos hZ _
    have h3 : (∏ v ∈ s, locFactor E r v) * (Z ^ fdeg E)⁻¹ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlow hL0).trans hprod
    rwa [← div_eq_mul_inv, div_le_one hZf] at h3
  exact le_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)

end GlobalTheory.EulerLocVol
