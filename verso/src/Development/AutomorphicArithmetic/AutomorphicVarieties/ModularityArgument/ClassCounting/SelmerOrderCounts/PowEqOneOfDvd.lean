import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TorsionExponentBound
import Development.EtaleCohomology.CyclotomicDiscriminants.SFewOfCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {l c ν : ℕ} {ζ : (𝓞 F)ˣ}
  {γ : F ≃ₐ[L] F}

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h.act, map_pow, ih, ← pow_mul, ← pow_succ]`.
-/
theorem UpperTheory.V.ZK.Ct.pow_act (h : Lay l c ν ζ γ) (j : ℕ) :
    (γ ^ j) ((ζ : 𝓞 F) : F) = ((ζ : 𝓞 F) : F) ^ (1 + l ^ c) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h.act, map_pow, ih, ← pow_mul, ← pow_succ]

/- English proof (translation)
Establish `hpl : Prime l` using `hl.prime`. Establish `hndvd : ¬ l ∣ 1 + l ^ c` using `fun h => hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left (dvd_pow_self l (by omega))).mp h))`. Establish `key : emultiplicity l ((1 + l ^ c) ^ j - 1) = c + emultiplicity l j`. Break down `hl.eq_two_or_odd' with rfl | hodd` into its components or cases. Establish `hc2` using `h2 rfl`.

Establish `hle : 1 ≤ (1 + 2 ^ c) ^ j` using `Nat.one_le_pow _ _ (by positivity)`. Use `Int.two_pow_sub_pow' (x := 1 + 2 ^ c) (y := 1) j ?_ ?_` as an intermediate fact. Rewrite `this` using `[one_pow, add_sub_cancel_left]`. Rewrite using `[← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity, Nat.cast_sub hle]`. Use `push_cast`.

Rewrite using `[this, emultiplicity_pow_self_of_prime Int.prime_two]`. Rewrite using `[add_sub_cancel_left]`. Conclude with `(pow_dvd_pow 2 hc2 : (2:ℤ) ^ 2 ∣ 2 ^ c)`. Introduce `h`. Apply `hndvd` to reduce the goal to its premises.

Conclude with `h` after adjusting the coercions. Use `Nat.emultiplicity_pow_sub_pow hl hodd (x := 1 + l ^ c) (y := 1) (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self l (by omega)) hndvd j` as an intermediate fact. Rewrite `this` using `[one_pow, Nat.add_sub_cancel_left, emultiplicity_pow_self_of_prime hpl]`. Conclude with `this`. Establish `hν` using `(pow_dvd_iff_le_emultiplicity.mp hj)`.

Rewrite `hν` using `[key]`. Apply `pow_dvd_iff_le_emultiplicity.mpr` to reduce the goal to its premises. Establish `e : ((ν : ℕ) : ℕ∞) = (c : ℕ∞) + ((ν - c : ℕ) : ℕ∞)`. Rewrite using `[← Nat.cast_add, Nat.add_sub_cancel' hcν]`. Rewrite `hν` using `[e]`.

Conclude with `(WithTop.add_le_add_iff_left (ENat.coe_ne_top c)).mp hν`.
-/
private theorem pow_sub_dvd_of_pow_dvd_one_add_pow_pow_sub_one (l c ν j : ℕ) (hl : l.Prime) (h1 : 1 ≤ c) (h2 : l = 2 → 2 ≤ c)
    (hcν : c ≤ ν) (hj : l ^ ν ∣ (1 + l ^ c) ^ j - 1) : l ^ (ν - c) ∣ j := by
  have hpl : Prime l := hl.prime
  have hndvd : ¬ l ∣ 1 + l ^ c := fun h =>
    hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left (dvd_pow_self l (by omega))).mp h))
  have key : emultiplicity l ((1 + l ^ c) ^ j - 1) = c + emultiplicity l j := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have hc2 := h2 rfl
      have hle : 1 ≤ (1 + 2 ^ c) ^ j := Nat.one_le_pow _ _ (by positivity)
      have := Int.two_pow_sub_pow' (x := 1 + 2 ^ c) (y := 1) j ?_ ?_
      · rw [one_pow, add_sub_cancel_left] at this
        rw [← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity, Nat.cast_sub hle]
        push_cast
        rw [this, emultiplicity_pow_self_of_prime Int.prime_two]
      · rw [add_sub_cancel_left]
        exact (pow_dvd_pow 2 hc2 : (2:ℤ) ^ 2 ∣ 2 ^ c)
      · intro h
        apply hndvd
        exact_mod_cast h
    · have := Nat.emultiplicity_pow_sub_pow hl hodd (x := 1 + l ^ c) (y := 1)
        (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self l (by omega)) hndvd j
      rw [one_pow, Nat.add_sub_cancel_left, emultiplicity_pow_self_of_prime hpl] at this
      exact this
  have hν := (pow_dvd_iff_le_emultiplicity.mp hj)
  rw [key] at hν
  apply pow_dvd_iff_le_emultiplicity.mpr
  have e : ((ν : ℕ) : ℕ∞) = (c : ℕ∞) + ((ν - c : ℕ) : ℕ∞) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hcν]
  rw [e] at hν
  exact (WithTop.add_le_add_iff_left (ENat.coe_ne_top c)).mp hν

/- English proof (translation)
Rewrite using `[← orderOf_dvd_iff_pow_eq_one, h.ord]`. Conclude with `pow_sub_dvd_of_pow_dvd_one_add_pow_pow_sub_one l c ν j hl h.c_pos h.c_two h.c_le hj`.
-/
theorem UpperTheory.V.ZK.Ct.pow_eq_one_of_dvd (hl : l.Prime) (h : Lay l c ν ζ γ) (j : ℕ)
    (hj : l ^ ν ∣ (1 + l ^ c) ^ j - 1) : γ ^ j = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, h.ord]
  exact pow_sub_dvd_of_pow_dvd_one_add_pow_pow_sub_one l c ν j hl h.c_pos h.c_two h.c_le hj

/- English proof (translation)
Establish `hG` using `h.gal`. Establish `: FiniteDimensional L F` using `Module.Finite.of_restrictScalars_finite ℚ L F`. Use `haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hPp : P.asIdeal.IsPrime` using `P.isPrime`. Establish `hPne : P.asIdeal ≠ ⊥` using `P.ne_bot`.

Use `haveI : NeZero P.asIdeal := ⟨hPne⟩`. Establish `hz : IsPrimitiveRoot (ζ : 𝓞 F) (l ^ ν)` using `IsPrimitiveRoot.coe_units_iff.mpr h.prim`. Establish `hn1 : Ideal.absNorm P.asIdeal ≠ 1` using `fun e => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp e)`. Establish `hcop : (Ideal.absNorm P.asIdeal).Coprime (l ^ ν)`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises.

Establish `hq` using `Nat.absNorm_under_prime P.asIdeal`. Rewrite using `[Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal hq]`. Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_primes hq hl]`. Introduce `e`.

Apply `hP` to reduce the goal to its premises. Use `Int.absNorm_under_mem P.asIdeal` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this` after adjusting the coercions. Establish `hzq` using `hz.idealQuotient_mk hn1 hcop`.

Rewrite using `[eq_bot_iff]`. Introduce `σ hσ`. Take `⟨j, rfl⟩` from `(mem_powers_iff_mem_zpowers.mpr (h.gen σ))`. Rewrite using `[Subgroup.mem_bot]`. Apply `UpperTheory.V.ZK.Ct.pow_eq_one_of_dvd hl h j` to reduce the goal to its premises.

Establish `hm` using `AddSubgroup.mem_inertia.mp hσ (ζ : 𝓞 F)`. Establish `hact : (γ ^ j) • (ζ : 𝓞 F) = (ζ : 𝓞 F) ^ (1 + l ^ c) ^ j`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Conclude with `UpperTheory.V.ZK.Ct.pow_act h j`. Rewrite `hm` using `[hact]`.

Establish `hq : Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) ^ (1 + l ^ c) ^ j = Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F)`. Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hm`. Establish `hpos : 1 ≤ (1 + l ^ c) ^ j` using `Nat.one_le_pow _ _ (by positivity)`. Establish `hne : Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) ≠ 0` using `hzq.ne_zero (pow_ne_zero _ hl.ne_zero)`.

Apply `hzq.dvd_of_pow_eq_one` to reduce the goal to its premises. Rewrite `hq` using `[← Nat.sub_add_cancel hpos, pow_succ]`. Conclude with `mul_left_cancel₀ hne (by rw [mul_one]; exact (mul_comm _ _).trans hq)`.
-/
theorem UpperTheory.V.ZK.Ct.inertia_eq_bot (hl : l.Prime) (h : Lay l c ν ζ γ) (P : HeightOneSpectrum (𝓞 F))
    (hP : (l : 𝓞 F) ∉ P.asIdeal) : P.asIdeal.inertia (F ≃ₐ[L] F) = ⊥ := by
  have hG := h.gal
  have : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hPp : P.asIdeal.IsPrime := P.isPrime
  have hPne : P.asIdeal ≠ ⊥ := P.ne_bot
  haveI : NeZero P.asIdeal := ⟨hPne⟩
  have hz : IsPrimitiveRoot (ζ : 𝓞 F) (l ^ ν) := IsPrimitiveRoot.coe_units_iff.mpr h.prim
  have hn1 : Ideal.absNorm P.asIdeal ≠ 1 := fun e => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp e)
  have hcop : (Ideal.absNorm P.asIdeal).Coprime (l ^ ν) := by
    apply Nat.Coprime.pow_right
    have hq := Nat.absNorm_under_prime P.asIdeal
    rw [Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal hq]
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_primes hq hl]
    intro e
    apply hP
    have := Int.absNorm_under_mem P.asIdeal
    rw [e] at this
    exact_mod_cast this
  have hzq := hz.idealQuotient_mk hn1 hcop
  rw [eq_bot_iff]
  intro σ hσ
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr (h.gen σ))
  rw [Subgroup.mem_bot]
  apply UpperTheory.V.ZK.Ct.pow_eq_one_of_dvd hl h j
  have hm := AddSubgroup.mem_inertia.mp hσ (ζ : 𝓞 F)
  have hact : (γ ^ j) • (ζ : 𝓞 F) = (ζ : 𝓞 F) ^ (1 + l ^ c) ^ j := by
    apply RingOfIntegers.coe_injective
    exact UpperTheory.V.ZK.Ct.pow_act h j
  rw [hact] at hm
  have hq : Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) ^ (1 + l ^ c) ^ j =
      Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hpos : 1 ≤ (1 + l ^ c) ^ j := Nat.one_le_pow _ _ (by positivity)
  have hne : Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) ≠ 0 := hzq.ne_zero (pow_ne_zero _ hl.ne_zero)
  apply hzq.dvd_of_pow_eq_one
  rw [← Nat.sub_add_cancel hpos, pow_succ] at hq
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact (mul_comm _ _).trans hq)

end

/- English proof (translation)
Introduce `L F _ _ _ _ _ l c ν ζ γ hl h x P p hlp hlies`. Establish `hG` using `h.gal`. Establish `: FiniteDimensional L F` using `Module.Finite.of_restrictScalars_finite ℚ L F`. Establish `hlP : (l : 𝓞 F) ∉ P.asIdeal`. Introduce `hm`.

Apply `hlp` to reduce the goal to its premises. Rewrite using `[Ideal.over_def P.asIdeal p.asIdeal]`. Apply `Ideal.mem_comap.mpr` to reduce the goal to its premises. Simplify using `using hm`. Establish `hI` using `UpperTheory.V.ZK.Ct.inertia_eq_bot hl h P hlP`.

Establish `he : p.asIdeal.ramificationIdx' P.asIdeal = 1`. Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.asIdeal p.ne_bot, ← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal (F ≃ₐ[L] F), ← Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[L] F) p.asIdeal P.asIdeal, hI]`. Simplify using the standard rewrite rules. Establish `hv` using `HeightOneSpectrum.valuation_liesOver F p P (x : L)`. Rewrite `hv` using `[he, pow_one]`.

Simplify using `only [ordP, Units.coe_map, MonoidHom.coe_coe, ← hv]`.
-/
theorem UpperTheory.V.ZK.Ct.unram :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l c ν : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), l.Prime → Lay l c ν ζ γ → ∀ (x : Lˣ) (P : HeightOneSpectrum (𝓞 F)) (p : HeightOneSpectrum (𝓞 L)), (l : 𝓞 L) ∉ p.asIdeal → P.asIdeal.LiesOver p.asIdeal → ordP P (Units.map (algebraMap L F : L →* F) x) = ordP p x := by
  intro L F _ _ _ _ _ l c ν ζ γ hl h x P p hlp hlies
  have hG := h.gal
  have : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  have hlP : (l : 𝓞 F) ∉ P.asIdeal := by
    intro hm
    apply hlp
    rw [Ideal.over_def P.asIdeal p.asIdeal]
    apply Ideal.mem_comap.mpr
    simpa using hm
  have hI := UpperTheory.V.ZK.Ct.inertia_eq_bot hl h P hlP
  have he : p.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.asIdeal p.ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal (F ≃ₐ[L] F),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[L] F) p.asIdeal P.asIdeal, hI]
    simp
  have hv := HeightOneSpectrum.valuation_liesOver F p P (x : L)
  rw [he, pow_one] at hv
  simp only [ordP, Units.coe_map, MonoidHom.coe_coe, ← hv]
