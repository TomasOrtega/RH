import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Nf

/- English proof (translation)
Simplify using `[Ohat, Subring.mem_iInf, HeightOneSpectrum.mem_adicCompletionIntegers]`.
-/
private theorem cv_mem {x : Af ℚ} : x ∈ Ohat ℚ ↔ ∀ w : Pl ℚ, Valued.v (pLoc ℚ w x) ≤ 1 := by
  simp [Ohat, Subring.mem_iInf, HeightOneSpectrum.mem_adicCompletionIntegers]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x`.
-/
private theorem cv_val (w : Pl ℚ) (x : ℚ) : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) x)) = w.valuation ℚ x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

/- English proof (translation)
Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]`. Conclude with `congrArg _ (map_natCast (algebraMap (𝓞 ℚ) ℚ) n).symm`.
-/
private theorem cv_nat (w : Pl ℚ) (n : ℕ) : w.valuation ℚ (n : ℚ) = w.intValuation (n : 𝓞 ℚ) := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]
  exact congrArg _ (map_natCast (algebraMap (𝓞 ℚ) ℚ) n).symm

/- English proof (translation)
Take `⟨hp, hI, -⟩` from `places w`. Rewrite using `[cv_nat]`. Use `le_antisymm (w.intValuation_le_one _) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `hn : (n : 𝓞 ℚ) ∈ w.asIdeal` using `(w.intValuation_lt_one_iff_mem _).1 hlt`. Establish `hq : ((normV w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal` using `by rw [hI]; exact Ideal.mem_span_singleton_self _`.

Take `⟨a, b, e⟩ : IsCoprime ((normV w : ℕ) : 𝓞 ℚ) (n : 𝓞 ℚ)` from `((Nat.Prime.coprime_iff_not_dvd hp).2 h).cast`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hn)))`.
-/
private theorem cv_one (w : Pl ℚ) (n : ℕ) (h : ¬ normV w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  obtain ⟨hp, hI, -⟩ := places w
  rw [cv_nat]
  refine le_antisymm (w.intValuation_le_one _) (not_lt.1 fun hlt => ?_)
  have hn : (n : 𝓞 ℚ) ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem _).1 hlt
  have hq : ((normV w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by rw [hI]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a, b, e⟩ : IsCoprime ((normV w : ℕ) : 𝓞 ℚ) (n : 𝓞 ℚ) := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).cast
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hn)))

/- English proof (translation)
Take `⟨hp, hI, -⟩` from `places w`. Rewrite using `[cv_nat]`. Conclude with `w.intValuation_singleton (by exact_mod_cast hp.ne_zero) hI`.
-/
private theorem cv_unif (w : Pl ℚ) : w.valuation ℚ ((normV w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨hp, hI, -⟩ := places w
  rw [cv_nat]
  exact w.intValuation_singleton (by exact_mod_cast hp.ne_zero) hI

/- English proof (translation)
Use `cv_one v _ fun hd => h (HeightOneSpectrum.ext ?_)` and prove the remaining obligations. Rewrite using `[(places v).2.1, (places w).2.1, (Nat.prime_dvd_prime_iff_eq (places v).1 (places w).1).1 hd]`.
-/
private theorem cv_ne {v w : Pl ℚ} (h : v ≠ w) : v.valuation ℚ ((normV w : ℕ) : ℚ) = 1 := by
  refine cv_one v _ fun hd => h (HeightOneSpectrum.ext ?_)
  rw [(places v).2.1, (places w).2.1, (Nat.prime_dvd_prime_iff_eq (places v).1 (places w).1).1 hd]

/- English proof (translation)
Establish `hM0 : (M : ℚ) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`. Use `⟨algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * x, cv_mem.2 fun v => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[map_mul, map_mul, cv_val, map_inv₀, cv_one v M hw, inv_one, one_mul]`.

Conclude with `h1`. Rewrite using `[map_mul, h0 v h, mul_zero, map_zero]`. Conclude with `zero_le_one`. Rewrite using `[← mul_assoc, ← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]`.
-/
private theorem cv_div {M : ℕ} (hM : 1 ≤ M) {w : Pl ℚ} (hw : ¬ normV w ∣ M) {x : Af ℚ}
    (h0 : ∀ v, v ≠ w → pLoc ℚ v x = 0) (h1 : Valued.v (pLoc ℚ w x) ≤ 1) : ∃ y ∈ Ohat ℚ, x = M * y := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  refine ⟨algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * x, cv_mem.2 fun v => ?_, ?_⟩
  · by_cases h : v = w
    · subst h
      rw [map_mul, map_mul, cv_val, map_inv₀, cv_one v M hw, inv_one, one_mul]; exact h1
    · rw [map_mul, h0 v h, mul_zero, map_zero]; exact zero_le_one
  · rw [← mul_assoc, ← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]

/- English proof (translation)
Use `⟨cv_mem.2 fun v => (h v).le, cv_mem.2 fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_units_inv, map_inv₀, h v, inv_one]`.
-/
private theorem cv_zu {u : (Af ℚ)ˣ} (h : ∀ v : Pl ℚ, Valued.v (pLoc ℚ v u) = 1) : IsZU u := by
  refine ⟨cv_mem.2 fun v => (h v).le, cv_mem.2 fun v => ?_⟩
  rw [map_units_inv, map_inv₀, h v, inv_one]

/- English proof (translation)
Conclude with `Pi.mulSingle_eq_same (M := fun v : Pl ℚ => v.adicCompletion ℚ) w x`.
-/
private theorem cv_same (w : Pl ℚ) (x : w.adicCompletion ℚ) : pLoc ℚ w (finiteSingle ℚ w x) = x := by
  classical
  exact Pi.mulSingle_eq_same (M := fun v : Pl ℚ => v.adicCompletion ℚ) w x

/- English proof (translation)
Conclude with `Pi.mulSingle_eq_of_ne (M := fun v : Pl ℚ => v.adicCompletion ℚ) h x`.
-/
private theorem cv_other {v w : Pl ℚ} (h : v ≠ w) (x : w.adicCompletion ℚ) : pLoc ℚ v (finiteSingle ℚ w x) = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun v : Pl ℚ => v.adicCompletion ℚ) h x

/- English proof (translation)
Use `Units.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing ℚ) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(1 : Af ℚ) - 1 + finiteSingle ℚ w x = finiteSingle ℚ w x`. Simplify using the standard rewrite rules.
-/
private theorem cv_loc (w : Pl ℚ) (x : (w.adicCompletion ℚ)ˣ) :
    finId ℚ (Units.map (finiteSingle ℚ w) x) = localIdele ℚ w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing ℚ) - 0 + 0 = 1
    simp
  · change (1 : Af ℚ) - 1 + finiteSingle ℚ w x = finiteSingle ℚ w x
    simp

/- English proof (translation)
Establish `h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x` using `fun x => (TR.infEq ℚ).symm_apply_apply x`. Establish `h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0` using `fun x => map_zero (TR.infEq ℚ).symm`. Establish `h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0` using `fun x => rfl`. Establish `h4 : ∀ x, pFin ℚ (sFin ℚ x) = x` using `fun x => rfl`. Use `Units.ext (TR.ad_ext ?_ ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _`. Simplify using `[h, h2]`. Express the relevant statement in the definitionally equal form `pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _`. Simplify using `[h3, h4]`.
-/
private theorem cv_split (x : Ideles ℚ) :
    TR.infId ℚ (Units.map (TR.pInf ℚ).toMonoidHom x) * finId ℚ (Units.map (pFin ℚ).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  have h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  have h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin ℚ (sFin ℚ x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h, h2]
  · change pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h3, h4]

/- English proof (translation)
Establish `h1` using `ω.2.2 r`. Rewrite `h1` using `[← cv_split (diagUnits ℚ r), map_mul, h.pos _ fun v => ?_, one_mul]`. Conclude with `h1`. Establish `e` using `eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))) (r : ℚ)`. Conclude with `lt_of_lt_of_eq (Rat.cast_pos.2 hr) e.symm`.
-/
private theorem cv_rat {M : ℕ} {χ : DirichletCharacter ℂ M} {ω : HChar ℚ} (h : IsDirOf χ ω) (r : ℚˣ) (hr : 0 < (r : ℚ)) :
    ω.1 (finId ℚ (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r)) = 1 := by
  have h1 := ω.2.2 r
  rw [← cv_split (diagUnits ℚ r), map_mul, h.pos _ fun v => ?_, one_mul] at h1
  · exact h1
  · have e := eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp
      ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))) (r : ℚ)
    exact lt_of_lt_of_eq (Rat.cast_pos.2 hr) e.symm

/- English proof (translation)
Introduce `M hM χ ω h`. Use `haveI : NeZero M := ⟨by omega⟩`. Use `⟨isOfFinOrder_iff_pow_eq_one.2 ⟨2 * Fintype.card (ZMod M)ˣ, by positivity, Subtype.ext (MonoidHom.ext fun z => ?_)⟩, fun w hw => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ω.1 z ^ (2 * Fintype.card (ZMod M)ˣ) = 1`. Take `⟨r, u, hr, hu, e⟩` from `ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)`.

Take `⟨d, hd⟩` from `ratAd.2.1 M hM _ hu.1`. Establish `h1` using `h.unit u hu d hd`. Establish `h2 : IsUnit (d : ZMod M)`. Assume the negation of the conclusion as `hn`. Rewrite `h1` using `[χ.map_nonunit hn, mul_zero]`.

Conclude with `zero_ne_one h1`. Take `⟨c, hc⟩` from `h2`. Establish `h3 : ω.1 (finId ℚ u) ^ Fintype.card (ZMod M)ˣ = 1`. Use `congrArg (· ^ Fintype.card (ZMod M)ˣ) h1` as an intermediate fact. Simplify using `only [mul_pow, one_pow] at this`.

Rewrite `this` using `[← hc, ← map_pow, ← Units.val_pow_eq_pow_val c, pow_card_eq_one, Units.val_one, map_one, mul_one]`. Conclude with `Units.ext this`. Establish `h4 : ∀ t, ω.1 (TR.infId ℚ t) ^ 2 = 1` using `fun t => by`. Rewrite using `[← map_pow, ← map_pow]`. Conclude with `h.pos _ fun v => by`.

Rewrite using `[Units.val_pow_eq_pow_val, Pi.pow_apply]`. Conclude with `sq_pos_of_ne_zero (by simpa using (Units.map (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).toMonoidHom t).ne_zero)`. Rewrite using `[← cv_split z, e, map_mul, map_mul, map_mul, cv_rat h r hr, one_mul, mul_pow, pow_mul, h4, one_pow, one_mul, mul_comm 2, pow_mul, h3, one_pow]`. Establish `hun : ω.UnrAt w` using `fun x hx => by`. Establish `h1` using `h.unit (Units.map (finiteSingle ℚ w) x) (cv_zu fun v => ?_) 1 (cv_div hM hw (fun v hv => ?_) ?_)`.

Rewrite `h1` using `[cv_loc, Int.cast_one, map_one, mul_one]`. Conclude with `Units.ext h1`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Conclude with `(congrArg _ (cv_same v x)).trans hx`.

Conclude with `(congrArg _ (cv_other hv x)).trans (map_one _)`. Rewrite using `[map_sub, Units.coe_map, cv_other hv, Int.cast_one, map_one, sub_self]`. Rewrite using `[map_sub, Units.coe_map, cv_same, Int.cast_one, map_one]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le (le_of_eq hx) (map_one _).le)`. Set `p : ℚˣ` to `Units.mk0 ((normV w : ℕ) : ℚ) (by exact_mod_cast (places w).1.ne_zero)`.

Establish `hp : 0 < (p : ℚ)`. Express the relevant statement in the definitionally equal form `0 < ((normV w : ℕ) : ℚ)`. Conclude with `(places w).1.pos` after adjusting the coercions. Establish `hU : IsUnifAt w (atFin w p)` using `(cv_val w p).trans (cv_unif w)`. Set `u : (Af ℚ)ˣ` to `Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom p * Units.map (finiteSingle ℚ w) (atFin w p)⁻¹`.

Establish `u1 : pLoc ℚ w u = 1`. Rewrite using `[Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_same]`. Conclude with `(atFin w p).mul_inv`. Establish `u2 : ∀ v, v ≠ w → pLoc ℚ v u = pLoc ℚ v (algebraMap ℚ (Af ℚ) p)` using `fun v hv => by`. Rewrite using `[Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_other hv, mul_one]`.

Both sides reduce to the same expression. Establish `e : (((normV w : ℕ) : ℤ) : Af ℚ) = algebraMap ℚ (Af ℚ) p`. Rewrite using `[Int.cast_natCast]`. Conclude with `(map_natCast _ _).symm`. Establish `h1` using `h.unit u (cv_zu fun v => ?_) (normV w : ℕ) (cv_div hM hw (fun v hv => ?_) ?_)`.

Rewrite `h1` using `[map_mul, map_mul, cv_rat h p hp, one_mul, cv_loc, map_inv, map_inv, Int.cast_natCast, Units.val_inv_eq_inv_val, inv_mul_eq_one₀ (Units.ne_zero _)]`. Rewrite using `[← ω.val_eq hun _ hU]`. Conclude with `h1`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Rewrite using `[u1, map_one]`. Rewrite using `[u2 v hv, cv_val]`. Conclude with `cv_ne hv`. Rewrite using `[map_sub, u2 v hv, e, sub_self]`. Rewrite using `[map_sub, u1, e]`.

Use `(Valuation.map_sub _ _ _).trans (max_le (map_one _).le ?_)` and prove the remaining obligations. Rewrite using `[cv_val]`. Conclude with `(cv_nat w _).trans_le (w.intValuation_le_one _)`.
-/
theorem UpperTheory.V.Af.Nf.charVal :
    UpperTheory.V.Af.Nf.CharVal := by
  intro M hM χ ω h
  haveI : NeZero M := ⟨by omega⟩
  refine ⟨isOfFinOrder_iff_pow_eq_one.2 ⟨2 * Fintype.card (ZMod M)ˣ, by positivity, Subtype.ext (MonoidHom.ext fun z => ?_)⟩,
    fun w hw => ?_⟩
  · change ω.1 z ^ (2 * Fintype.card (ZMod M)ˣ) = 1
    obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)
    obtain ⟨d, hd⟩ := ratAd.2.1 M hM _ hu.1
    have h1 := h.unit u hu d hd
    have h2 : IsUnit (d : ZMod M) := by
      by_contra hn
      rw [χ.map_nonunit hn, mul_zero] at h1
      exact zero_ne_one h1
    obtain ⟨c, hc⟩ := h2
    have h3 : ω.1 (finId ℚ u) ^ Fintype.card (ZMod M)ˣ = 1 := by
      have := congrArg (· ^ Fintype.card (ZMod M)ˣ) h1
      simp only [mul_pow, one_pow] at this
      rw [← hc, ← map_pow, ← Units.val_pow_eq_pow_val c, pow_card_eq_one, Units.val_one, map_one, mul_one] at this
      exact Units.ext this
    have h4 : ∀ t, ω.1 (TR.infId ℚ t) ^ 2 = 1 := fun t => by
      rw [← map_pow, ← map_pow]
      exact h.pos _ fun v => by
        rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
        exact sq_pos_of_ne_zero (by simpa using (Units.map (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).toMonoidHom t).ne_zero)
    rw [← cv_split z, e, map_mul, map_mul, map_mul, cv_rat h r hr, one_mul, mul_pow, pow_mul, h4, one_pow, one_mul,
      mul_comm 2, pow_mul, h3, one_pow]
  · have hun : ω.UnrAt w := fun x hx => by
      have h1 := h.unit (Units.map (finiteSingle ℚ w) x) (cv_zu fun v => ?_) 1 (cv_div hM hw (fun v hv => ?_) ?_)
      · rw [cv_loc, Int.cast_one, map_one, mul_one] at h1
        exact Units.ext h1
      · by_cases hv : v = w
        · subst hv; exact (congrArg _ (cv_same v x)).trans hx
        · exact (congrArg _ (cv_other hv x)).trans (map_one _)
      · rw [map_sub, Units.coe_map, cv_other hv, Int.cast_one, map_one, sub_self]
      · rw [map_sub, Units.coe_map, cv_same, Int.cast_one, map_one]
        exact (Valuation.map_sub _ _ _).trans (max_le (le_of_eq hx) (map_one _).le)
    let p : ℚˣ := Units.mk0 ((normV w : ℕ) : ℚ) (by exact_mod_cast (places w).1.ne_zero)
    have hp : 0 < (p : ℚ) := by
      change 0 < ((normV w : ℕ) : ℚ)
      exact_mod_cast (places w).1.pos
    have hU : IsUnifAt w (atFin w p) := (cv_val w p).trans (cv_unif w)
    let u : (Af ℚ)ˣ := Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom p * Units.map (finiteSingle ℚ w) (atFin w p)⁻¹
    have u1 : pLoc ℚ w u = 1 := by
      rw [Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_same]
      exact (atFin w p).mul_inv
    have u2 : ∀ v, v ≠ w → pLoc ℚ v u = pLoc ℚ v (algebraMap ℚ (Af ℚ) p) := fun v hv => by
      rw [Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_other hv, mul_one]
      rfl
    have e : (((normV w : ℕ) : ℤ) : Af ℚ) = algebraMap ℚ (Af ℚ) p := by
      rw [Int.cast_natCast]; exact (map_natCast _ _).symm
    have h1 := h.unit u (cv_zu fun v => ?_) (normV w : ℕ) (cv_div hM hw (fun v hv => ?_) ?_)
    · rw [map_mul, map_mul, cv_rat h p hp, one_mul, cv_loc, map_inv, map_inv, Int.cast_natCast, Units.val_inv_eq_inv_val,
        inv_mul_eq_one₀ (Units.ne_zero _)] at h1
      rw [← ω.val_eq hun _ hU]
      exact h1
    · by_cases hv : v = w
      · subst hv; rw [u1, map_one]
      · rw [u2 v hv, cv_val]; exact cv_ne hv
    · rw [map_sub, u2 v hv, e, sub_self]
    · rw [map_sub, u1, e]
      refine (Valuation.map_sub _ _ _).trans (max_le (map_one _).le ?_)
      rw [cv_val]
      exact (cv_nat w _).trans_le (w.intValuation_le_one _)
