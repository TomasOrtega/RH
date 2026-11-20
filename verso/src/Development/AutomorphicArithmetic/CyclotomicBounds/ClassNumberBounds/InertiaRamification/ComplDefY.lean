import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite

namespace KStar.Ram

open NumberField IsDedekindDomain IsLocalRing

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `w.valuation_of_algebraMap a`.
-/
private theorem cdy_val (a : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_of_algebraMap a

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Ideal.mem_span_singleton, (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Express the relevant statement in the definitionally equal form `¬ Valued.v (y : w.adicCompletion E) = 1 ↔ Valued.v (y : w.adicCompletion E) ≤ Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) π : w.adicCompletionIntegers E) : w.adicCompletion E)`. Rewrite using `[cdy_val, hπ]`. Establish `hy : Valued.v (y : w.adicCompletion E) ≤ 1` using `y.2`.

Generalize the expression as in `Valued.v (y : w.adicCompletion E) = t at hy`. Break down `eq_or_ne t 0 with rfl | ht` into its components or cases. Simplify using the standard rewrite rules. Rewrite `hy` using `[← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Rewrite using `[← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem cdy_max {π : 𝓞 E} (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (w.adicCompletionIntegers E) =
      Ideal.span {algebraMap (𝓞 E) (w.adicCompletionIntegers E) π} := by
  ext y
  rw [Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, mem_maximalIdeal,
    mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change ¬ Valued.v (y : w.adicCompletion E) = 1 ↔ Valued.v (y : w.adicCompletion E) ≤
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) π : w.adicCompletionIntegers E) :
      w.adicCompletion E)
  rw [cdy_val, hπ]
  have hy : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
  generalize Valued.v (y : w.adicCompletion E) = t at hy
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]
    omega

/- English proof (translation)
Rewrite using `[map_pow, hπ, ← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules.
-/
private theorem cdy_pow (π : 𝓞 E) (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  simp

/- English proof (translation)
Take `⟨π, hπ⟩` from `w.intValuation_exists_uniformizer`. Rewrite using `[cdy_max w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, ← map_pow, ← cdy_pow w π hπ n, ← cdy_val]`. Both sides reduce to the same expression.
-/
private theorem cdy_mem (n : ℕ) (y : w.adicCompletionIntegers E) :
    y ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n ↔
      Valued.v (y : w.adicCompletion E) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, ← map_pow,
    ← cdy_pow w π hπ n, ← cdy_val]
  rfl

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, cdy_mem, cdy_val, w.intValuation_le_pow_iff_mem]`.
-/
private theorem cdy_comap (n : ℕ) : (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
    (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n := by
  ext a
  rw [Ideal.mem_comap, cdy_mem, cdy_val, w.intValuation_le_pow_iff_mem]

/- English proof (translation)
Take `⟨p, hp⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp (-(n : ℤ)))`. Use `⟨‖p‖, norm_pos_iff.2 ?_, fun x => by rw [Valued.toNormedField.norm_le_iff, hp]⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hp` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hp.symm`.
-/
private theorem cdy_ball (n : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ x : w.adicCompletion E,
    Valued.v x ≤ WithZero.exp (-(n : ℤ)) ↔ ‖x‖ ≤ r := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
    (WithZero.exp (-(n : ℤ)))
  refine ⟨‖p‖, norm_pos_iff.2 ?_, fun x => by rw [Valued.toNormedField.norm_le_iff, hp]⟩
  rintro rfl
  rw [map_zero] at hp
  exact WithZero.exp_ne_zero hp.symm

/- English proof (translation)
Use `⟨?_, cdy_comap w n, fun y => ?_⟩` and prove the remaining obligations. Use `le_antisymm (Ideal.map_le_iff_le_comap.2 (cdy_comap w n).ge) ?_` and prove the remaining obligations. Take `⟨π, hπ⟩` from `w.intValuation_exists_uniformizer`. Rewrite using `[cdy_max w hπ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, ← map_pow]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations.

Rewrite using `[← w.intValuation_le_pow_iff_mem, cdy_pow w π hπ]`. Take `⟨r, hr, h⟩` from `cdy_ball w n`. Take `⟨t, ht⟩` from `(HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt (y : w.adicCompletion E) hr`. Rewrite `ht` using `[dist_eq_norm]`. Establish `ht'` using `(h _).2 ht.le`.

Establish `hv : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a` using `fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a`. Establish `hn : WithZero.exp (-(n : ℤ)) ≤ 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `ht1 : w.valuation E t ≤ 1`.

Rewrite using `[← hv, ← sub_sub_cancel (y : w.adicCompletion E) (algebraMap E (w.adicCompletion E) t)]`. Conclude with `Valuation.map_sub_le _ y.2 (ht'.trans hn)`. Take `⟨a, ha⟩` from `w.exists_valuation_sub_lt_of_integer ht1 (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[cdy_mem]`.

Establish `e : ((y - algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) : w.adicCompletion E) = ((y : w.adicCompletion E) - algebraMap E (w.adicCompletion E) t) - algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E a - t)`. Rewrite using `[map_sub, sub_sub, add_sub_cancel]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `Valuation.map_sub_le _ ht' ?_` and prove the remaining obligations.

Rewrite using `[hv]`. Conclude with `ha.le`.
-/
theorem complIntegers_quotient (n : ℕ) :
    (w.asIdeal ^ n).map (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) =
        maximalIdeal (w.adicCompletionIntegers E) ^ n ∧
      (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
        (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n ∧
      (∀ y : w.adicCompletionIntegers E, ∃ x : 𝓞 E,
        y - algebraMap (𝓞 E) _ x ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n) := by
  refine ⟨?_, cdy_comap w n, fun y => ?_⟩
  · refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cdy_comap w n).ge) ?_
    obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
    rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, ← map_pow]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← w.intValuation_le_pow_iff_mem, cdy_pow w π hπ]
  · obtain ⟨r, hr, h⟩ := cdy_ball w n
    obtain ⟨t, ht⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt
      (y : w.adicCompletion E) hr
    rw [dist_eq_norm] at ht
    have ht' := (h _).2 ht.le
    have hv : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
      fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
    have hn : WithZero.exp (-(n : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have ht1 : w.valuation E t ≤ 1 := by
      rw [← hv, ← sub_sub_cancel (y : w.adicCompletion E) (algebraMap E (w.adicCompletion E) t)]
      exact Valuation.map_sub_le _ y.2 (ht'.trans hn)
    obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer ht1
      (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
    refine ⟨a, ?_⟩
    rw [cdy_mem]
    have e : ((y - algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
        w.adicCompletion E) = ((y : w.adicCompletion E) - algebraMap E (w.adicCompletion E) t) -
        algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E a - t) := by
      rw [map_sub, sub_sub, add_sub_cancel]
      rfl
    rw [e]
    refine Valuation.map_sub_le _ ht' ?_
    rw [hv]
    exact ha.le

variable (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]

/- English proof (translation)
Set `p : Nat.Primes` to `⟨l, Fact.out⟩`. Set `u : HeightOneSpectrum (𝓞 ℚ)` to `(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p`. Establish `hl : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal`. Establish `: (l : ℤ) ∈ Ideal.span {(l : ℤ)}` using `Ideal.mem_span_singleton_self _`. Rewrite `this` using `[Ideal.mem_of_liesOver w.asIdeal]`.

Simplify using `using this`. Establish `hu : u.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)}`. Express the relevant statement in the definitionally equal form `(Ideal.span {(l : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `: w.asIdeal.LiesOver u.asIdeal`.

Use `⟨u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_⟩` and prove the remaining obligations. Rewrite using `[hu, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `hl`. Set `F : ℚ_[l] →+* w.adicCompletion E` to `(KStar.Choice.complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).toRingEquiv.toRingHom`. Establish `hF : Continuous F` using `(KStar.Choice.continuous_complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).continuous`.

Establish `hm : ∀ x : ℤ_[l], F.comp PadicInt.Coe.ringHom x ∈ w.adicCompletionIntegers E`. Introduce `x`. Use `KStar.Choice.complMap_mem u w ?_` and prove the remaining obligations. Use `(PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p x).2` as an intermediate fact. Rewrite `this` using `[PadicInt.coe_adicCompletionIntegersEquiv_apply]`.

Conclude with `this`. Set `f : ℤ_[l] →+* w.adicCompletionIntegers E` to `(F.comp PadicInt.Coe.ringHom).codRestrict (w.adicCompletionIntegers E) hm`. Use `⟨f, F, fun x y h => ?_, hF, fun x => rfl, fun f' => ?_, fun F' hF' => ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (F.injective (congrArg Subtype.val h))`. Establish `hlm : ((l : ℕ) : w.adicCompletionIntegers E) ∈ maximalIdeal (w.adicCompletionIntegers E)`.

Establish `h1` using `cdy_comap w 1`. Rewrite `h1` using `[pow_one, pow_one]`. Rewrite `hl` using `[← h1, Ideal.mem_comap, map_natCast]`. Conclude with `hl`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (w.adicCompletionIntegers E)) (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]`. Introduce `k`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton.1 (PadicInt.appr_spec k x)`. Establish `hx : x = (x.appr k : ℤ_[l]) + (l : ℤ_[l]) ^ k * z` using `by rw [← hz]; ring`. Establish `: f' x - f x = (l : w.adicCompletionIntegers E) ^ k * (f' z - f z)` using `by conv_lhs => rw [hx]`.

Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm k)`. Use `DFunLike.coe_injective ((Padic.denseRange_ratCast l).equalizer hF' hF ?_)` and prove the remaining obligations.

Use function extensionality and compare the values at `q`. Simplify using `only [Function.comp_apply, map_ratCast]`.
-/
theorem existsUnique_padic_hom :
    ∃ (f : ℤ_[l] →+* w.adicCompletionIntegers E) (F : ℚ_[l] →+* w.adicCompletion E),
      Function.Injective f ∧ Continuous F ∧ (∀ x : ℤ_[l], F x = f x) ∧ (∀ f', f' = f) ∧
        ∀ F' : ℚ_[l] →+* w.adicCompletion E, Continuous F' → F' = F := by
  let p : Nat.Primes := ⟨l, Fact.out⟩
  let u : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  have hl : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
    rw [Ideal.mem_of_liesOver w.asIdeal] at this
    simpa using this
  have hu : u.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    change (Ideal.span {(l : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have : w.asIdeal.LiesOver u.asIdeal := by
    refine ⟨u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_⟩
    rw [hu, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  let F : ℚ_[l] →+* w.adicCompletion E :=
    (KStar.Choice.complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).toRingEquiv.toRingHom
  have hF : Continuous F :=
    (KStar.Choice.continuous_complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).continuous
  have hm : ∀ x : ℤ_[l], F.comp PadicInt.Coe.ringHom x ∈ w.adicCompletionIntegers E := by
    intro x
    refine KStar.Choice.complMap_mem u w ?_
    have := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p x).2
    rw [PadicInt.coe_adicCompletionIntegersEquiv_apply] at this
    exact this
  let f : ℤ_[l] →+* w.adicCompletionIntegers E :=
    (F.comp PadicInt.Coe.ringHom).codRestrict (w.adicCompletionIntegers E) hm
  refine ⟨f, F, fun x y h => ?_, hF, fun x => rfl, fun f' => ?_, fun F' hF' => ?_⟩
  · exact Subtype.ext (F.injective (congrArg Subtype.val h))
  · have hlm : ((l : ℕ) : w.adicCompletionIntegers E) ∈
        maximalIdeal (w.adicCompletionIntegers E) := by
      have h1 := cdy_comap w 1
      rw [pow_one, pow_one] at h1
      rw [← h1, Ideal.mem_comap, map_natCast] at hl
      exact hl
    refine RingHom.ext fun x => ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (w.adicCompletionIntegers E))
        (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
    intro k
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + (l : ℤ_[l]) ^ k * z := by rw [← hz]; ring
    have : f' x - f x = (l : w.adicCompletionIntegers E) ^ k * (f' z - f z) := by
      conv_lhs => rw [hx]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm k)
  · refine DFunLike.coe_injective ((Padic.denseRange_ratCast l).equalizer hF' hF ?_)
    funext q
    simp only [Function.comp_apply, map_ratCast]

end KStar.Ram
