import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 ℚ)).isMaximal` as an intermediate fact. Conclude with `(Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 ℚ)).asIdeal w.asIdeal).symm`.
-/
private theorem norm_deg' (w : H.P E) : normV w = normV (w.under (𝓞 ℚ)) ^ w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 ℚ)).isMaximal
  exact (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 ℚ)).asIdeal w.asIdeal).symm

/- English proof (translation)
Use `v.isMaximal` as an intermediate fact. Establish `: Fintype (v.asIdeal.primesOver (𝓞 E))` using `(IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype`. Rewrite using `[← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 ℚ) ℚ (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]`. Use `(Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)` and prove the remaining obligations. Use `q.2.1` as an intermediate fact.

Conclude with `Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)`.
-/
private theorem deg_le (h2 : Module.finrank ℚ E = 2) (v : H.P ℚ)
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 ℚ) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 ℚ) ℚ (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

/- English proof (translation)
Use `w.isPrime` as an intermediate fact. Establish `hs` using `deg_le h2 (w.under (𝓞 ℚ)) {⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}`. Rewrite `hs` using `[Finset.sum_singleton]`. Establish `h3` using `w.asIdeal.inertiaDeg_pos (𝓞 ℚ)`. Establish `h4` using `norm_deg' w`.

Simplify using `only at hs`. Generalize the expression as in `w.asIdeal.inertiaDeg (𝓞 ℚ) = f at hs h3 h4`. Use `interval_cases f`. Conclude with `absurd (h4.trans (pow_one _)) h`. Conclude with `h4`.
-/
private theorem norm_sq (h2 : Module.finrank ℚ E = 2) {w : H.P E}
    (h : normV w ≠ normV (w.under (𝓞 ℚ))) : normV w = normV (w.under (𝓞 ℚ)) ^ 2 := by
  have := w.isPrime
  have hs := deg_le h2 (w.under (𝓞 ℚ)) {⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_singleton] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 ℚ)
  have h4 := norm_deg' w
  dsimp only at hs
  generalize w.asIdeal.inertiaDeg (𝓞 ℚ) = f at hs h3 h4
  interval_cases f
  · exact absurd (h4.trans (pow_one _)) h
  · exact h4

/- English proof (translation)
Use `(w.under (𝓞 ℚ)).isMaximal` as an intermediate fact. Use `w.isPrime` as an intermediate fact. Use `letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal`. Establish `: Finite (𝓞 E ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Set `φ : (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) →+* (𝓞 E ⧸ w.asIdeal)` to `Ideal.quotientMap w.asIdeal (algebraMap (𝓞 ℚ) (𝓞 E)) le_rfl`.

Establish `hb : Function.Bijective φ` using `(RingHom.injective φ).bijective_of_nat_card_le hn.le`. Take `⟨c, hc⟩` from `hb.2 (Ideal.Quotient.mk _ x)`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Use `⟨t, Ideal.Quotient.eq.1 (hc.symm.trans ?_ )⟩` and prove the remaining obligations. Conclude with `Ideal.quotientMap_mk`.
-/
private theorem res_surj (w : H.P E) (hn : normV w = normV (w.under (𝓞 ℚ))) (x : 𝓞 E) :
    ∃ t : 𝓞 ℚ, x - algebraMap (𝓞 ℚ) (𝓞 E) t ∈ w.asIdeal := by
  have := (w.under (𝓞 ℚ)).isMaximal
  have := w.isPrime
  letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  let φ : (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) →+* (𝓞 E ⧸ w.asIdeal) :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 ℚ) (𝓞 E)) le_rfl
  have hb : Function.Bijective φ := (RingHom.injective φ).bijective_of_nat_card_le hn.le
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ x)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, Ideal.Quotient.eq.1 (hc.symm.trans ?_ )⟩
  exact Ideal.quotientMap_mk

/- English proof (translation)
Establish `hmem : ∀ a : 𝓞 ℚ, a ∈ v.asIdeal ↔ v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a) < 1` using `fun a => (v.valuation_lt_one_iff_mem a).symm`. Establish `e : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.num : ℤ) : 𝓞 ℚ)) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.den : ℕ) : 𝓞 ℚ))`. Rewrite using `[map_intCast, map_natCast, ← Rat.mul_den_eq_num δ, map_mul, h, one_mul]`. Establish `hiff : ((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ↔ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal`. Rewrite using `[hmem, hmem, e]`.

Establish `hc : IsCoprime ((δ.num : ℤ) : 𝓞 ℚ) ((δ.den : ℕ) : 𝓞 ℚ)`. Establish `h1 : IsCoprime δ.num (δ.den : ℤ)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Conclude with `δ.reduced`. Simplify using `using h1.map (Int.castRingHom (𝓞 ℚ))`.

Establish `hnot : ¬ (((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)`. Introduce and unpack `⟨h1, h3⟩`. Take `⟨x, y, hxy⟩` from `hc`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left x h1) (v.asIdeal.mul_mem_left y h3)))`. Conclude with `⟨fun h1 => hnot ⟨h1, hiff.1 h1⟩, fun h3 => hnot ⟨hiff.2 h3, h3⟩⟩`.
-/
private theorem num_den (v : H.P ℚ) {δ : ℚ} (h : v.valuation ℚ δ = 1) :
    ((δ.num : ℤ) : 𝓞 ℚ) ∉ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  have hmem : ∀ a : 𝓞 ℚ, a ∈ v.asIdeal ↔ v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a) < 1 :=
    fun a => (v.valuation_lt_one_iff_mem a).symm
  have e : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.num : ℤ) : 𝓞 ℚ)) =
      v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.den : ℕ) : 𝓞 ℚ)) := by
    rw [map_intCast, map_natCast, ← Rat.mul_den_eq_num δ, map_mul, h, one_mul]
  have hiff : ((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ↔ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hmem, hmem, e]
  have hc : IsCoprime ((δ.num : ℤ) : 𝓞 ℚ) ((δ.den : ℕ) : 𝓞 ℚ) := by
    have h1 : IsCoprime δ.num (δ.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact δ.reduced
    simpa using h1.map (Int.castRingHom (𝓞 ℚ))
  have hnot : ¬ (((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) := by
    rintro ⟨h1, h3⟩
    obtain ⟨x, y, hxy⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left x h1) (v.asIdeal.mul_mem_left y h3)))
  exact ⟨fun h1 => hnot ⟨h1, hiff.1 h1⟩, fun h3 => hnot ⟨hiff.2 h3, h3⟩⟩

/- English proof (translation)
Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : K)).symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v (algebraMap K (H.Kv v) 2) = 1`. Rewrite using `[map_ofNat]`. Conclude with `h`.
-/
private theorem val_two {K : Type} [Field K] [NumberField K] (v : H.P K) (h : Valued.v (2 : H.Kv v) = 1) :
    v.valuation K (2 : K) = 1 := by
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : K)).symm.trans ?_
  change Valued.v (algebraMap K (H.Kv v) 2) = 1
  rw [map_ofNat]
  exact h

/- English proof (translation)
Establish `hδ : (w.under (𝓞 ℚ)).valuation ℚ D.δ = 1` using `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ D.δ).symm.trans hG.del`. Establish `h2v : ((2 : ℕ) : 𝓞 ℚ) ∉ (w.under (𝓞 ℚ)).asIdeal`. Establish `h` using `val_two _ hG.two`. Establish `hmem : ((2 : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal ↔ (w.under (𝓞 ℚ)).valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((2 : ℕ) : 𝓞 ℚ)) < 1` using `((w.under (𝓞 ℚ)).valuation_lt_one_iff_mem _).symm`. Rewrite using `[hmem, map_natCast, Nat.cast_ofNat, h]`.

Conclude with `lt_irrefl _`. Take `⟨ha, hb⟩` from `num_den _ hδ`. Use `set n : ℤ := D.δ.num with hnum`. Use `set d : ℕ := D.δ.den with hden`. Establish `hnd : (d : E) * algebraMap ℚ E D.δ = (n : E)`.

Use `congrArg (algebraMap ℚ E) (Rat.mul_den_eq_num D.δ)` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_intCast]`. Rewrite using `[mul_comm]`. Conclude with `this`. Establish `hsq : ((d : E) * D.θ) ^ 2 = ((d * n : ℤ) : E)`.

Rewrite using `[mul_pow, D.sq, pow_two, mul_assoc, hnd]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hint : IsIntegral ℤ ((d : E) * D.θ)` using `IsIntegral.of_pow two_pos (hsq ▸ isIntegral_algebraMap (R := ℤ) (x := (d * n : ℤ)))`. Take `⟨T, hT⟩ : ∃ T : 𝓞 E, (T : E) = (d : E) * D.θ` from `⟨⟨_, hint⟩, rfl⟩`.

Establish `hT2 : T ^ 2 = algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ))`. Use `RingOfIntegers.ext ?_` and prove the remaining obligations. Simplify using `only [map_pow, map_mul, map_natCast, map_intCast]`. Rewrite using `[show (algebraMap (𝓞 E) E) T = (T : E) from rfl, hT, hsq]`. Use `push_cast`.

Both sides reduce to the same expression. Set `e : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv D.σ.toRingEquiv`. Establish `hcomm : ∀ a : 𝓞 ℚ, e (algebraMap (𝓞 ℚ) (𝓞 E) a) = algebraMap (𝓞 ℚ) (𝓞 E) a` using `fun a => RingOfIntegers.ext (D.σ.commutes (a : ℚ))`. Establish `h1 : w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective = w`. Use `hu _ (HeightOneSpectrum.ext (Ideal.ext fun a => ?_))` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e (algebraMap (𝓞 ℚ) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) a ∈ w.asIdeal`. Rewrite using `[hcomm]`. Establish `he : ∀ x, x ∈ w.asIdeal → e x ∈ w.asIdeal`. Introduce `x hx`. Establish `h3 : x ∈ (w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal`.

Rewrite using `[h1]`. Conclude with `hx`. Conclude with `h3`. Establish `heT : e T = -T`. Use `RingOfIntegers.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `D.σ (T : E) = _`. Rewrite using `[hT, map_mul, map_natCast, D.conj]`. Simplify using `[hT]`. Take `⟨t, ht⟩` from `res_surj w hn T`. Establish `ht'` using `he _ ht`.

Rewrite `ht'` using `[map_sub, heT, hcomm]`. Establish `h2T : algebraMap (𝓞 ℚ) (𝓞 E) ((2 : ℕ) : 𝓞 ℚ) * T ∈ w.asIdeal`. Use `w.asIdeal.sub_mem ht ht'` as an intermediate fact. Rewrite using `[map_natCast]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `w.isPrime` as an intermediate fact. Break down `w.isPrime.mem_or_mem h2T with h | h` into its components or cases. Conclude with `h2v h`.

Establish `h5 : algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) ∈ w.asIdeal`. Rewrite using `[← hT2, pow_two]`. Conclude with `w.asIdeal.mul_mem_left _ h`. Break down `(w.under (𝓞 ℚ)).isPrime.mem_or_mem (show _ ∈ (w.under (𝓞 ℚ)).asIdeal from h5) with h6 | h6` into its components or cases. Conclude with `hb h6`.

Conclude with `ha h6`.
-/
private theorem no_ram (D : Dat ℚ E) (w : H.P E) (hG : H.Gd D.δ (w.under (𝓞 ℚ)))
    (hu : ∀ w' : H.P E, w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → w' = w)
    (hn : normV w = normV (w.under (𝓞 ℚ))) : False := by
  have hδ : (w.under (𝓞 ℚ)).valuation ℚ D.δ = 1 :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ D.δ).symm.trans hG.del
  have h2v : ((2 : ℕ) : 𝓞 ℚ) ∉ (w.under (𝓞 ℚ)).asIdeal := by
    have h := val_two _ hG.two
    have hmem : ((2 : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal ↔
        (w.under (𝓞 ℚ)).valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((2 : ℕ) : 𝓞 ℚ)) < 1 :=
      ((w.under (𝓞 ℚ)).valuation_lt_one_iff_mem _).symm
    rw [hmem, map_natCast, Nat.cast_ofNat, h]
    exact lt_irrefl _
  obtain ⟨ha, hb⟩ := num_den _ hδ
  set n : ℤ := D.δ.num with hnum
  set d : ℕ := D.δ.den with hden
  have hnd : (d : E) * algebraMap ℚ E D.δ = (n : E) := by
    have := congrArg (algebraMap ℚ E) (Rat.mul_den_eq_num D.δ)
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]
    exact this
  have hsq : ((d : E) * D.θ) ^ 2 = ((d * n : ℤ) : E) := by
    rw [mul_pow, D.sq, pow_two, mul_assoc, hnd]
    push_cast
    rfl
  have hint : IsIntegral ℤ ((d : E) * D.θ) :=
    IsIntegral.of_pow two_pos (hsq ▸ isIntegral_algebraMap (R := ℤ) (x := (d * n : ℤ)))
  obtain ⟨T, hT⟩ : ∃ T : 𝓞 E, (T : E) = (d : E) * D.θ := ⟨⟨_, hint⟩, rfl⟩
  have hT2 : T ^ 2 = algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) := by
    refine RingOfIntegers.ext ?_
    simp only [map_pow, map_mul, map_natCast, map_intCast]
    rw [show (algebraMap (𝓞 E) E) T = (T : E) from rfl, hT, hsq]
    push_cast
    rfl
  let e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv D.σ.toRingEquiv
  have hcomm : ∀ a : 𝓞 ℚ, e (algebraMap (𝓞 ℚ) (𝓞 E) a) = algebraMap (𝓞 ℚ) (𝓞 E) a :=
    fun a => RingOfIntegers.ext (D.σ.commutes (a : ℚ))
  have h1 : w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective = w := by
    refine hu _ (HeightOneSpectrum.ext (Ideal.ext fun a => ?_))
    change e (algebraMap (𝓞 ℚ) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) a ∈ w.asIdeal
    rw [hcomm]
  have he : ∀ x, x ∈ w.asIdeal → e x ∈ w.asIdeal := by
    intro x hx
    have h3 : x ∈ (w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := by
      rw [h1]
      exact hx
    exact h3
  have heT : e T = -T := by
    refine RingOfIntegers.ext ?_
    change D.σ (T : E) = _
    rw [hT, map_mul, map_natCast, D.conj]
    simp [hT]
  obtain ⟨t, ht⟩ := res_surj w hn T
  have ht' := he _ ht
  rw [map_sub, heT, hcomm] at ht'
  have h2T : algebraMap (𝓞 ℚ) (𝓞 E) ((2 : ℕ) : 𝓞 ℚ) * T ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem ht ht'
    rw [map_natCast]
    convert this using 1
    push_cast
    ring
  have := w.isPrime
  rcases w.isPrime.mem_or_mem h2T with h | h
  · exact h2v h
  · have h5 : algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) ∈ w.asIdeal := by
      rw [← hT2, pow_two]
      exact w.asIdeal.mul_mem_left _ h
    rcases (w.under (𝓞 ℚ)).isPrime.mem_or_mem (show _ ∈ (w.under (𝓞 ℚ)).asIdeal from h5) with h6 | h6
    · exact hb h6
    · exact ha h6

end

/- English proof (translation)
Introduce `E _ _ D v hG`. Establish `h2 : Module.finrank ℚ E = 2` using `by simpa using Module.finrank_eq_card_basis D.b`. Use `⟨?_, fun w hw => ?_⟩` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`.

Conclude with `⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩`. Substitute `hw` using the available equality. Distinguish the cases in `hn : normV w = normV (w.under (𝓞 ℚ))`. Use `Or.inl ⟨hn, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`.

Use `push_neg at hu`. Conclude with `no_ram D w hG (fun w' h => by_contra fun hne => hu w' hne h) hn`. Conclude with `Or.inr (norm_sq h2 hn)`.
-/
theorem UpperTheory.good_prime_split_or_inert_of_quadratic :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ), H.Gd D.δ v → (∃ w : H.P E, w.under (𝓞 ℚ) = v) ∧
        ∀ w : H.P E, w.under (𝓞 ℚ) = v → (normV w = normV v ∧ ∃ w' : H.P E, w' ≠ w ∧ w'.under (𝓞 ℚ) = v) ∨ normV w = normV v ^ 2 := by
  intro E _ _ D v hG
  have h2 : Module.finrank ℚ E = 2 := by simpa using Module.finrank_eq_card_basis D.b
  refine ⟨?_, fun w hw => ?_⟩
  · have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  · subst hw
    by_cases hn : normV w = normV (w.under (𝓞 ℚ))
    · refine Or.inl ⟨hn, ?_⟩
      by_contra hu
      push_neg at hu
      exact no_ram D w hG (fun w' h => by_contra fun hne => hu w' hne h) hn
    · exact Or.inr (norm_sq h2 hn)
