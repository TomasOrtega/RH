import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.IntegralApproximation

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Rewrite using `[← Valuation.Compatible.vle_iff_le]`. Conclude with `L.val x y`.
-/
theorem v_le_iff (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) (x y : F) :
    valuation L.Fp (L.ιF x) ≤ valuation L.Fp (L.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← Valuation.Compatible.vle_iff_le]
  exact L.val x y

/- English proof (translation)
Establish `h` using `v_le_iff L x 1`. Simplify `h` using `only [map_one]`.
-/
theorem v_le_one_iff (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) (x : F) :
    valuation L.Fp (L.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1 := by
  have h := v_le_iff L x 1
  simpa only [map_one] using h

/- English proof (translation)
Rewrite using `[← not_le, ← not_le]`. Establish `h` using `v_le_iff L 1 x`. Simplify using `only [map_one] at h`. Rewrite using `[h]`.
-/
theorem v_lt_one_iff (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) (x : F) :
    valuation L.Fp (L.ιF x) < 1 ↔ p.valuation F x < 1 := by
  rw [← not_le, ← not_le]
  have h := v_le_iff L 1 x
  simp only [map_one] at h
  rw [h]

/- English proof (translation)
Take `⟨⟨b, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F)) x`. Simplify using `only at hx ⊢`. Establish `hs0 : (s : 𝓞 F) ≠ 0` using `nonZeroDivisors.coe_ne_zero s`. Establish `hvs : p.intValuation (s : 𝓞 F) ≠ 0` using `p.intValuation_ne_zero _ hs0`. Rewrite `hx` using `[HeightOneSpectrum.valuation_of_mk', div_le_one₀ (zero_lt_iff.mpr hvs)]`.

Establish `hp0 : p.asIdeal ≠ ⊥` using `p.ne_bot`. Establish `htop : p.asIdeal ≠ ⊤` using `p.isPrime.ne_top`. Establish `hex : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hs0` to reduce the goal to its premises. Establish `hmem : (s : 𝓞 F) ∈ ⨅ i, p.asIdeal ^ i`. Rewrite using `[Ideal.mem_iInf]`. Introduce `i`. Consider the cases of `i with`.

Consider the case `zero => simp`. Consider the case `succ n => exact h n`. Rewrite `hmem` using `[Ideal.iInf_pow_eq_bot_of_isDomain _ htop]`. Conclude with `(Ideal.mem_bot).1 hmem`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn1, hn⟩ : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) ∧ (s : 𝓞 F) ∈ p.asIdeal ^ n := by`.

Use `⟨Nat.find hex, Nat.find_spec hex, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos` into its components or cases. Simplify using `[h0]`. Establish `hm` using `Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)`. Rewrite `hm` using `[not_not, Nat.sub_add_cancel hpos]`.

Conclude with `hm`. Establish `hb : b ∈ p.asIdeal ^ n`. Rewrite `hn`, the goal using `[← HeightOneSpectrum.intValuation_le_pow_iff_mem]`. Conclude with `hx.trans hn`. Establish `hI : Ideal.span {(s : 𝓞 F)} ⊔ p.asIdeal ^ (n + 1) = p.asIdeal ^ n`.

Apply `Ideal.eq_prime_pow_of_succ_lt_of_le hp0` to reduce the goal to its premises. Use `lt_of_le_of_ne le_sup_right fun h => hn1 ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Conclude with `sup_le ((Ideal.span_singleton_le_iff_mem _).2 hn) (Ideal.pow_le_pow_right (Nat.le_succ n))`.

Rewrite `hb` using `[← hI]`. Take `⟨y, hy, r, hr, hyr⟩` from `Submodule.mem_sup.1 hb`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hs0`.

Establish `key : IsLocalization.mk' F b s - algebraMap (𝓞 F) F c = IsLocalization.mk' F r s`. Rewrite using `[IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← hyr, map_add, map_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, HeightOneSpectrum.valuation_of_mk', div_lt_one₀ (zero_lt_iff.mpr hvs)]`.

Establish `hr'` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem p r (n + 1)).2 hr`. Establish `hs' : ¬ p.intValuation (s : 𝓞 F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))` using `fun h => hn1 ((HeightOneSpectrum.intValuation_le_pow_iff_mem p _ _).1 h)`. Conclude with `lt_of_le_of_lt hr' (not_le.1 hs')`.
-/
theorem exists_int_approx (x : F) (hx : p.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, p.valuation F (x - algebraMap (𝓞 F) F a) < 1 := by
  classical
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F)) x
  dsimp only at hx ⊢
  have hs0 : (s : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hvs : p.intValuation (s : 𝓞 F) ≠ 0 := p.intValuation_ne_zero _ hs0
  rw [HeightOneSpectrum.valuation_of_mk', div_le_one₀ (zero_lt_iff.mpr hvs)] at hx
  have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
  have htop : p.asIdeal ≠ ⊤ := p.isPrime.ne_top
  have hex : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hs0
    have hmem : (s : 𝓞 F) ∈ ⨅ i, p.asIdeal ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      cases i with
      | zero => simp
      | succ n => exact h n
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ htop] at hmem
    exact (Ideal.mem_bot).1 hmem
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) ∧ (s : 𝓞 F) ∈ p.asIdeal ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · simp [h0]
    · have hm := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      rw [not_not, Nat.sub_add_cancel hpos] at hm
      exact hm
  have hb : b ∈ p.asIdeal ^ n := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at hn ⊢
    exact hx.trans hn
  have hI : Ideal.span {(s : 𝓞 F)} ⊔ p.asIdeal ^ (n + 1) = p.asIdeal ^ n := by
    apply Ideal.eq_prime_pow_of_succ_lt_of_le hp0
    · refine lt_of_le_of_ne le_sup_right fun h => hn1 ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hn) (Ideal.pow_le_pow_right (Nat.le_succ n))
  rw [← hI] at hb
  obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 hb
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨c, ?_⟩
  have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hs0
  have key : IsLocalization.mk' F b s - algebraMap (𝓞 F) F c = IsLocalization.mk' F r s := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← hyr, map_add, map_mul]
    field_simp
    ring
  rw [key, HeightOneSpectrum.valuation_of_mk', div_lt_one₀ (zero_lt_iff.mpr hvs)]
  have hr' := (HeightOneSpectrum.intValuation_le_pow_iff_mem p r (n + 1)).2 hr
  have hs' : ¬ p.intValuation (s : 𝓞 F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun h =>
    hn1 ((HeightOneSpectrum.intValuation_le_pow_iff_mem p _ _).1 h)
  exact lt_of_le_of_lt hr' (not_le.1 hs')

/- English proof (translation)
Use `L.lf` as an intermediate fact. Establish `hint : ∀ a : 𝓞 F, (L.ιF.comp (algebraMap (𝓞 F) F)) a ∈ 𝒪[L.Fp]` using `fun a => by`. Rewrite using `[Valuation.mem_integer_iff]`. Conclude with `(v_le_one_iff L _).2 (HeightOneSpectrum.valuation_le_one p a)`. Set `φ : 𝓞 F →+* 𝒪[L.Fp]` to `(L.ιF.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[L.Fp] hint`.

Set `ρ : 𝓞 F →+* IsLocalRing.ResidueField 𝒪[L.Fp]` to `(IsLocalRing.residue 𝒪[L.Fp]).comp φ`. Establish `hmax : ∀ z : 𝒪[L.Fp], valuation L.Fp (z : L.Fp) < 1 → z ∈ IsLocalRing.maximalIdeal 𝒪[L.Fp]` using `fun z hz => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hz))`. Establish `hker : ∀ a ∈ p.asIdeal, ρ a = 0`. Introduce `a ha`. Use `show IsLocalRing.residue _ (φ a) = 0`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Apply `hmax` to reduce the goal to its premises. Use `show valuation L.Fp (L.ιF (algebraMap (𝓞 F) F a)) < 1`. Rewrite using `[v_lt_one_iff L]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem p a).2 ha`.

Establish `hsurj : Function.Surjective ρ`. Introduce `w`. Take `⟨y, rfl⟩` from `IsLocalRing.residue_surjective w`. Establish `hU : IsOpen {z : L.Fp | valuation L.Fp (z - (y : L.Fp)) < 1}`. Rewrite using `[isOpen_iff_mem_nhds]`.

Introduce `z0 hz0`. Rewrite using `[IsValuativeTopology.mem_nhds_iff]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only [Set.mem_setOf_eq, Units.val_one] at hz hz0 ⊢`.

Establish `: z0 + z - (y : L.Fp) = (z0 - y) + z` using `by ring`. Rewrite using `[this]`. Conclude with `Valuation.map_add_lt _ hz0 hz`. Take `⟨x, hx⟩` from `L.dense.exists_mem_open hU ⟨(y : L.Fp), by simp⟩`. Simplify using `only [Set.mem_setOf_eq] at hx`.

Establish `hxI : valuation L.Fp (L.ιF x) ≤ 1`. Establish `: L.ιF x = (L.ιF x - y) + y` using `by ring`. Rewrite using `[this]`. Conclude with `Valuation.map_add_le _ hx.le ((Valuation.mem_integer_iff _ _).1 y.2)`. Take `⟨a, ha⟩` from `exists_int_approx x ((v_le_one_iff L x).1 hxI)`.

Establish `ha' : valuation L.Fp (L.ιF x - L.ιF (algebraMap (𝓞 F) F a)) < 1`. Rewrite using `[← map_sub]`. Conclude with `(v_lt_one_iff L _).2 ha`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `show IsLocalRing.residue _ (φ a) = IsLocalRing.residue _ y`.

Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Apply `hmax` to reduce the goal to its premises. Use `show valuation L.Fp (L.ιF (algebraMap (𝓞 F) F a) - y) < 1`. Establish `: L.ιF (algebraMap (𝓞 F) F a) - (y : L.Fp) = -(L.ιF x - L.ιF (algebraMap (𝓞 F) F a)) + (L.ιF x - y)` using `by ring`. Rewrite using `[this]`.

Conclude with `Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact ha') hx`. Set `ρq` to `Ideal.Quotient.lift p.asIdeal ρ hker`. Establish `hsurjq : Function.Surjective ρq`. Introduce `w`. Take `⟨a, ha⟩` from `hsurj w`.

Conclude with `⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩`. Use `haveI : Finite (𝓞 F ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_res_le (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Nat.card (IsLocalRing.ResidueField 𝒪[L.Fp]) ≤ Ideal.absNorm p.asIdeal := by
  have := L.lf
  have hint : ∀ a : 𝓞 F, (L.ιF.comp (algebraMap (𝓞 F) F)) a ∈ 𝒪[L.Fp] := fun a => by
    rw [Valuation.mem_integer_iff]
    exact (v_le_one_iff L _).2 (HeightOneSpectrum.valuation_le_one p a)
  let φ : 𝓞 F →+* 𝒪[L.Fp] := (L.ιF.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[L.Fp] hint
  let ρ : 𝓞 F →+* IsLocalRing.ResidueField 𝒪[L.Fp] := (IsLocalRing.residue 𝒪[L.Fp]).comp φ
  have hmax : ∀ z : 𝒪[L.Fp], valuation L.Fp (z : L.Fp) < 1 → z ∈ IsLocalRing.maximalIdeal 𝒪[L.Fp] :=
    fun z hz => (IsLocalRing.mem_maximalIdeal _).2
      (mem_nonunits_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hz))
  have hker : ∀ a ∈ p.asIdeal, ρ a = 0 := by
    intro a ha
    show IsLocalRing.residue _ (φ a) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    apply hmax
    show valuation L.Fp (L.ιF (algebraMap (𝓞 F) F a)) < 1
    rw [v_lt_one_iff L]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem p a).2 ha
  have hsurj : Function.Surjective ρ := by
    intro w
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
    have hU : IsOpen {z : L.Fp | valuation L.Fp (z - (y : L.Fp)) < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro z0 hz0
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨1, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_setOf_eq, Units.val_one] at hz hz0 ⊢
      have : z0 + z - (y : L.Fp) = (z0 - y) + z := by ring
      rw [this]
      exact Valuation.map_add_lt _ hz0 hz
    obtain ⟨x, hx⟩ := L.dense.exists_mem_open hU ⟨(y : L.Fp), by simp⟩
    simp only [Set.mem_setOf_eq] at hx
    have hxI : valuation L.Fp (L.ιF x) ≤ 1 := by
      have : L.ιF x = (L.ιF x - y) + y := by ring
      rw [this]
      exact Valuation.map_add_le _ hx.le ((Valuation.mem_integer_iff _ _).1 y.2)
    obtain ⟨a, ha⟩ := exists_int_approx x ((v_le_one_iff L x).1 hxI)
    have ha' : valuation L.Fp (L.ιF x - L.ιF (algebraMap (𝓞 F) F a)) < 1 := by
      rw [← map_sub]
      exact (v_lt_one_iff L _).2 ha
    refine ⟨a, ?_⟩
    show IsLocalRing.residue _ (φ a) = IsLocalRing.residue _ y
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply hmax
    show valuation L.Fp (L.ιF (algebraMap (𝓞 F) F a) - y) < 1
    have : L.ιF (algebraMap (𝓞 F) F a) - (y : L.Fp) =
        -(L.ιF x - L.ιF (algebraMap (𝓞 F) F a)) + (L.ιF x - y) := by ring
    rw [this]
    exact Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact ha') hx
  let ρq := Ideal.Quotient.lift p.asIdeal ρ hker
  have hsurjq : Function.Surjective ρq := by
    intro w
    obtain ⟨a, ha⟩ := hsurj w
    exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩
  haveI : Finite (𝓞 F ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot
  calc Nat.card (IsLocalRing.ResidueField 𝒪[L.Fp]) ≤ Nat.card (𝓞 F ⧸ p.asIdeal) :=
        Nat.card_le_card_of_surjective ρq hsurjq
    _ = Ideal.absNorm p.asIdeal := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Use `L.lf` as an intermediate fact. Conclude with `Finite.one_lt_card_iff_nontrivial.mpr inferInstance`.
-/
theorem one_lt_card_res (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    1 < Nat.card (IsLocalRing.ResidueField 𝒪[L.Fp]) := by
  have := L.lf
  exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance

end Res

/- English proof (translation)
Establish `ha` using `abs_nonneg t`. Prove the components needed by the constructor for the conclusion. Establish `hpos : 0 < 1 - |t|` using `by linarith`. Establish `hinv : (1 - |t|)⁻¹ ≤ 1 + 2 * |t|`. Rewrite using `[inv_eq_one_div, div_le_iff₀ hpos]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hlog : -(2 * |t|) ≤ Real.log (1 - |t|)`. Use `Real.one_sub_inv_le_log_of_pos hpos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Use `Real.add_one_le_exp (2 * |t|)` as an intermediate fact. Combine the linear relations using `[neg_abs_le t]`.
-/
theorem factor_bounds {t : ℝ} (ht : |t| ≤ 1 / 2) :
    Real.exp (-(2 * |t|)) ≤ 1 - t ∧ 1 - t ≤ Real.exp (2 * |t|) := by
  have ha := abs_nonneg t
  constructor
  · have hpos : 0 < 1 - |t| := by linarith
    have hinv : (1 - |t|)⁻¹ ≤ 1 + 2 * |t| := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    have hlog : -(2 * |t|) ≤ Real.log (1 - |t|) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      linarith
    calc Real.exp (-(2 * |t|)) ≤ Real.exp (Real.log (1 - |t|)) := Real.exp_le_exp.2 hlog
      _ = 1 - |t| := Real.exp_log hpos
      _ ≤ 1 - t := by linarith [le_abs_self t]
  · have := Real.add_one_le_exp (2 * |t|)
    linarith [neg_abs_le t]

/- English proof (translation)
Use `set x : ℝ := (N : ℝ)⁻¹ with hx`. Establish `hN' : (2 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hx0 : 0 ≤ x` using `by positivity`. Establish `hx2 : x ≤ 1 / 2`. Rewrite using `[hx]`.

Rewrite using `[inv_le_comm₀ (by positivity) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx1 : x < 1` using `by linarith`. Establish `habs : ∀ i, |η ^ i / (N : ℝ) ^ i| = x ^ i`. Introduce `i`.

Apply the tactic sequence `rcases hη with h | h <;> simp [h, abs_div, abs_pow, hx, inv_pow]`. Establish `hsmall : ∀ i ∈ Finset.Icc a b, |η ^ i / (N : ℝ) ^ i| ≤ 1 / 2`. Introduce `i hi`. Rewrite using `[habs]`. Establish `hi1 : 1 ≤ i` using `le_trans hk (le_trans hak (Finset.mem_Icc.1 hi).1)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ∑ i ∈ Finset.Icc a b, 2 * x ^ i ≤ 4 * x ^ k`. Rewrite using `[← Finset.mul_sum]`. Establish `h1 : ∑ i ∈ Finset.Icc a b, x ^ i ≤ ∑ i ∈ Finset.Ico a (b + 1), x ^ i`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `i hi`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ico] at hi ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `i _ _`. Check the signs of the components of the expression.

Establish `h2` using `geom_sum_Ico_le_of_lt_one (m := a) (n := b + 1) hx0 hx1`. Establish `h3 : x ^ a / (1 - x) ≤ 2 * x ^ a`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[pow_nonneg hx0 a]`. Establish `h4 : x ^ a ≤ x ^ k` using `pow_le_pow_of_le_one hx0 hx1.le hak`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlo : ∀ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) ≤ 1 - η ^ i / (N : ℝ) ^ i`. Introduce `i hi`. Use `(factor_bounds (hsmall i hi)).1` as an intermediate fact. Rewrite `this` using `[habs]`. Then use the resulting hypothesis.

Establish `hhi : ∀ i ∈ Finset.Icc a b, 1 - η ^ i / (N : ℝ) ^ i ≤ Real.exp (2 * x ^ i)`. Introduce `i hi`. Use `(factor_bounds (hsmall i hi)).2` as an intermediate fact. Rewrite `this` using `[habs]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_neg_distrib, Real.exp_sum]`. Use `_ ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) := Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hlo`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_bounds (N : ℕ) (hN : 2 ≤ N) (η : ℝ) (hη : η = 1 ∨ η = -1) (a b k : ℕ) (hk : 1 ≤ k)
    (hak : k ≤ a) :
    Real.exp (-(4 * ((N : ℝ)⁻¹) ^ k)) ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) ∧
      ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) ≤ Real.exp (4 * ((N : ℝ)⁻¹) ^ k) := by
  set x : ℝ := (N : ℝ)⁻¹ with hx
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hx1 : x < 1 := by linarith
  have habs : ∀ i, |η ^ i / (N : ℝ) ^ i| = x ^ i := by
    intro i
    rcases hη with h | h <;> simp [h, abs_div, abs_pow, hx, inv_pow]
  have hsmall : ∀ i ∈ Finset.Icc a b, |η ^ i / (N : ℝ) ^ i| ≤ 1 / 2 := by
    intro i hi
    rw [habs]
    have hi1 : 1 ≤ i := le_trans hk (le_trans hak (Finset.mem_Icc.1 hi).1)
    calc x ^ i ≤ x ^ 1 := pow_le_pow_of_le_one hx0 hx1.le hi1
      _ = x := pow_one x
      _ ≤ 1 / 2 := hx2
  have hsum : ∑ i ∈ Finset.Icc a b, 2 * x ^ i ≤ 4 * x ^ k := by
    rw [← Finset.mul_sum]
    have h1 : ∑ i ∈ Finset.Icc a b, x ^ i ≤ ∑ i ∈ Finset.Ico a (b + 1), x ^ i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_Icc, Finset.mem_Ico] at hi ⊢
        omega
      · intro i _ _
        positivity
    have h2 := geom_sum_Ico_le_of_lt_one (m := a) (n := b + 1) hx0 hx1
    have h3 : x ^ a / (1 - x) ≤ 2 * x ^ a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg hx0 a]
    have h4 : x ^ a ≤ x ^ k := pow_le_pow_of_le_one hx0 hx1.le hak
    linarith
  have hlo : ∀ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) ≤ 1 - η ^ i / (N : ℝ) ^ i := by
    intro i hi
    have := (factor_bounds (hsmall i hi)).1
    rwa [habs] at this
  have hhi : ∀ i ∈ Finset.Icc a b, 1 - η ^ i / (N : ℝ) ^ i ≤ Real.exp (2 * x ^ i) := by
    intro i hi
    have := (factor_bounds (hsmall i hi)).2
    rwa [habs] at this
  constructor
  · calc Real.exp (-(4 * x ^ k)) ≤ Real.exp (-(∑ i ∈ Finset.Icc a b, 2 * x ^ i)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ∏ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) := by
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) :=
          Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hlo
  · calc ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) ≤ ∏ i ∈ Finset.Icc a b, Real.exp (2 * x ^ i) :=
          Finset.prod_le_prod (fun i hi => le_trans (Real.exp_pos _).le (hlo i hi)) hhi
      _ = Real.exp (∑ i ∈ Finset.Icc a b, 2 * x ^ i) := by rw [Real.exp_sum]
      _ ≤ Real.exp (4 * x ^ k) := Real.exp_le_exp.2 hsum

open Formalism.L2.SG.DataInst Formalism.MainNotions.S.LocalSplitGroups

/- English proof (translation)
Unfold `eta₃`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem etaP_pm {D : Formalism.BasicNotions.D7} (p : PlF D) : eta₃ p = 1 ∨ eta₃ p = -1 := by
  unfold eta₃
  split_ifs <;> simp

/- English proof (translation)
Establish `h0 : Ideal.absNorm p.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `p.ne_bot`. Establish `h1 : Ideal.absNorm p.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `p.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
theorem absNorm_two_le {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact p.isPrime.ne_top
  omega

/- English proof (translation)
Unfold `aPD`. Apply `prod_bounds _ (absNorm_two_le p) _ (etaP_pm p) _ _ _ hk` to reduce the goal to its premises. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem aPD_bounds {D : Formalism.BasicNotions.D7} (p : PlF D) (T : ℕ) (hk : 1 ≤ D.R.k) :
    Real.exp (-(4 * ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ ^ D.R.k)) ≤ aPD p T ∧
      aPD p T ≤ Real.exp (4 * ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ ^ D.R.k) := by
  unfold aPD
  apply prod_bounds _ (absNorm_two_le p) _ (etaP_pm p) _ _ _ hk
  split_ifs <;> omega

/- English proof (translation)
Introduce `hk u u' p`. Use `set m := D.R.k - 2 * D.R.rS - 2 with hm`. Use `set q : ℝ := (Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ) with hq`. Establish `hN2 : 2 ≤ Ideal.absNorm p.asIdeal` using `absNorm_two_le p`. Establish `hq1 : (1 : ℝ) < q` using `by rw [hq]; exact_mod_cast one_lt_card_res (D.s.atP p)`.

Establish `hqN : q ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)` using `by rw [hq]; exact_mod_cast card_res_le (D.s.atP p)`. Use `set x : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ with hx`. Establish `hk1 : 1 ≤ D.R.k` using `by omega`. Establish `hkm : D.R.k = m + (2 * D.R.rS + 2)` using `by omega`. Establish `hx0 : 0 ≤ x` using `by positivity`.

Establish `hx2 : x ≤ 1 / 2`. Rewrite using `[hx, inv_le_comm₀ (by positivity) (by norm_num)]`. Establish `: (2 : ℝ) ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast hN2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkey : 8 * x ^ D.R.k ≤ 2 * (q ^ m)⁻¹`.

Establish `h1 : x ^ D.R.k = x ^ m * x ^ (2 * D.R.rS + 2)` using `by rw [← pow_add, ← hkm]`. Establish `h2 : x ^ (2 * D.R.rS + 2) ≤ x ^ 2` using `pow_le_pow_of_le_one hx0 (by linarith) (by omega)`. Establish `h3 : x ^ 2 ≤ 1 / 4` using `by nlinarith`. Establish `h4 : x ^ m ≤ (q ^ m)⁻¹`. Rewrite using `[hx, inv_pow]`.

Apply `inv_anti₀ (pow_pos (by linarith) m)` to reduce the goal to its premises. Conclude with `pow_le_pow_left₀ (by linarith) hqN m`. Establish `h5 : 0 ≤ x ^ m` using `pow_nonneg hx0 m`. Establish `h6 : x ^ m * x ^ (2 * D.R.rS + 2) ≤ x ^ m * (1 / 4)` using `mul_le_mul_of_nonneg_left (h2.trans h3) h5`. Rewrite using `[h1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA` using `aPD_bounds p (D.mem u).A.T hk1`. Establish `hA'` using `aPD_bounds p (D.mem u').A.T hk1`. Establish `hlow : Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k))` using `Real.exp_le_exp.2 (by linarith)`. Establish `hup : Real.exp (8 * x ^ D.R.k) ≤ Real.exp (2 * (q ^ m)⁻¹)` using `Real.exp_le_exp.2 hkey`.

Establish `hxk : 0 ≤ x ^ D.R.k` using `pow_nonneg hx0 _`. Unfold `alpD`. Use `split_ifs`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.

Use `_ ≤ aPD p (D.mem u).A.T * aPD p (D.mem u').A.T := mul_le_mul hA.1 hA'.1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hA.1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Use `_ ≤ Real.exp (2 * (q ^ m)⁻¹) := hup`.
-/
theorem alpBoundU (D : Formalism.BasicNotions.D7) :
    2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → ∀ (u u' : D.what₂.Word) (p : PlF D),
      Real.exp (-(2 * (((Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ)) ^
          (D.R.k - 2 * D.R.rS - 2))⁻¹)) ≤ alpD u u' p ∧
        alpD u u' p ≤ Real.exp (2 * (((Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ)) ^
          (D.R.k - 2 * D.R.rS - 2))⁻¹) := by
  intro hk u u' p
  set m := D.R.k - 2 * D.R.rS - 2 with hm
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ) with hq
  have hN2 : 2 ≤ Ideal.absNorm p.asIdeal := absNorm_two_le p
  have hq1 : (1 : ℝ) < q := by rw [hq]; exact_mod_cast one_lt_card_res (D.s.atP p)
  have hqN : q ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by rw [hq]; exact_mod_cast card_res_le (D.s.atP p)
  set x : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ with hx
  have hk1 : 1 ≤ D.R.k := by omega
  have hkm : D.R.k = m + (2 * D.R.rS + 2) := by omega
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx, inv_le_comm₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by exact_mod_cast hN2
    linarith
  have hkey : 8 * x ^ D.R.k ≤ 2 * (q ^ m)⁻¹ := by
    have h1 : x ^ D.R.k = x ^ m * x ^ (2 * D.R.rS + 2) := by rw [← pow_add, ← hkm]
    have h2 : x ^ (2 * D.R.rS + 2) ≤ x ^ 2 := pow_le_pow_of_le_one hx0 (by linarith) (by omega)
    have h3 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have h4 : x ^ m ≤ (q ^ m)⁻¹ := by
      rw [hx, inv_pow]
      apply inv_anti₀ (pow_pos (by linarith) m)
      exact pow_le_pow_left₀ (by linarith) hqN m
    have h5 : 0 ≤ x ^ m := pow_nonneg hx0 m
    have h6 : x ^ m * x ^ (2 * D.R.rS + 2) ≤ x ^ m * (1 / 4) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) h5
    rw [h1]
    linarith
  have hA := aPD_bounds p (D.mem u).A.T hk1
  have hA' := aPD_bounds p (D.mem u').A.T hk1
  have hlow : Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k)) := Real.exp_le_exp.2 (by linarith)
  have hup : Real.exp (8 * x ^ D.R.k) ≤ Real.exp (2 * (q ^ m)⁻¹) := Real.exp_le_exp.2 hkey
  have hxk : 0 ≤ x ^ D.R.k := pow_nonneg hx0 _
  unfold alpD
  split_ifs
  · constructor
    · calc Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k)) := hlow
        _ ≤ Real.exp (-(4 * x ^ D.R.k)) := Real.exp_le_exp.2 (by linarith)
        _ ≤ aPD p (D.mem u).A.T := hA.1
    · calc aPD p (D.mem u).A.T ≤ Real.exp (4 * x ^ D.R.k) := hA.2
        _ ≤ Real.exp (8 * x ^ D.R.k) := Real.exp_le_exp.2 (by linarith)
        _ ≤ Real.exp (2 * (q ^ m)⁻¹) := hup
  · constructor
    · calc Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k)) := hlow
        _ = Real.exp (-(4 * x ^ D.R.k)) * Real.exp (-(4 * x ^ D.R.k)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ aPD p (D.mem u).A.T * aPD p (D.mem u').A.T :=
            mul_le_mul hA.1 hA'.1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hA.1)
    · calc aPD p (D.mem u).A.T * aPD p (D.mem u').A.T ≤ Real.exp (4 * x ^ D.R.k) * Real.exp (4 * x ^ D.R.k) :=
            mul_le_mul hA.2 hA'.2 (le_trans (Real.exp_pos _).le hA'.1) (Real.exp_pos _).le
        _ = Real.exp (8 * x ^ D.R.k) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ Real.exp (2 * (q ^ m)⁻¹) := hup

end Formalism.L2.SG.IntegralApproximation
