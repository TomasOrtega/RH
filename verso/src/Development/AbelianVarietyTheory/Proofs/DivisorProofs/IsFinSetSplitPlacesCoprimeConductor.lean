import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfVal
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.InhabK

section General

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce `σ`. Use `⟨InfinitePlace.mk σ, ?_, ?_⟩` and prove the remaining obligations. Break down `InfinitePlace.embedding_mk_eq σ with h | h` into its components or cases. Conclude with `Or.inl h.symm`. Use `right`.

Simplify using `only [h]`. Use extensionality with `x`. Simplify using the standard rewrite rules. Introduce and unpack `w (h | h)`. Rewrite using `[h, InfinitePlace.mk_embedding]`.

Rewrite using `[h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`.
-/
theorem isCMType_places : IsCMType (fun w : InfinitePlace E => w.embedding) := by
  intro σ
  refine ⟨InfinitePlace.mk σ, ?_, ?_⟩
  · rcases InfinitePlace.embedding_mk_eq σ with h | h
    · exact Or.inl h.symm
    · right; simp only [h]; ext x; simp
  · rintro w (h | h)
    · rw [h, InfinitePlace.mk_embedding]
    · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

/- English proof (translation)
The claim follows from `multiplicity_eq_zero`.
-/
theorem expIn_eq_zero {𝔣 : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} : expIn 𝔣 v = 0 ↔ ¬ v.asIdeal ∣ 𝔣 :=
  multiplicity_eq_zero

/- English proof (translation)
The claim follows from `multiplicity_pow_self v.ne_bot (fun h => v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) n`.
-/
theorem expIn_pow (v : HeightOneSpectrum (OF E)) (n : ℕ) : expIn (v.asIdeal ^ n) v = n :=
  multiplicity_pow_self v.ne_bot (fun h => v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) n

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Take `⟨⟨P, hP, hl⟩⟩` from `v.asIdeal.nonempty_primesOver (S := 𝓞 E)`. Conclude with `⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl.over.symm⟩`.
-/
theorem exists_over (v : HeightOneSpectrum (OF E)) : ∃ P : HeightOneSpectrum (𝓞 E), Over P v := by
  have := v.isPrime
  obtain ⟨⟨P, hP, hl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
  exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl.over.symm⟩

end General

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local notation "cj" => IsCMField.ringOfIntegersComplexConj E

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Set `P' : HeightOneSpectrum (𝓞 E)` to `⟨P.asIdeal.comap (cj).toRingEquiv.toRingHom, Ideal.comap_isPrime _ _, fun h => by`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Establish `: (cj).symm y ∈ P.asIdeal.comap (cj).toRingEquiv.toRingHom`. Rewrite using `[Ideal.mem_comap]`.

Simplify using `using hy`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `hy0 (by simpa using this)⟩`. Use `⟨P, P', fun e => hx ?_, hv, ?_⟩` and prove the remaining obligations. Use `haveI : Fact (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime := ⟨by`.

Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]`. Conclude with `hl⟩`. Establish `htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal) = ⊤`. Break down `(AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal)).eq_bot_or_eq_top_of_prime_card with h | h` into its components or cases. Conclude with `absurd (AddSubgroup.zmultiples_eq_bot.1 h) one_ne_zero`.

Conclude with `h`. Take `⟨n, hn⟩` from `AddSubgroup.mem_zmultiples_iff.1 (htop ▸ AddSubgroup.mem_top (Ideal.Quotient.mk P.asIdeal x))`. Establish `h1 : x - n ∈ P.asIdeal`. Rewrite using `[← Ideal.Quotient.eq, ← hn]`. Simplify using the standard rewrite rules.

Establish `h2 : x - n ∈ P'.asIdeal` using `e ▸ h1`. Establish `h3 : cj x - n ∈ P.asIdeal`. Establish `: cj (x - n) ∈ P.asIdeal` using `h2`. Simplify using `using this`. Use `P.asIdeal.sub_mem h1 h3` as an intermediate fact.

Simplify using `using this`. Unfold `Over at hv ⊢`. Rewrite using `[← hv]`. Use extensionality with `y`. Express the relevant statement in the definitionally equal form `cj (algebraMap (OF E) (𝓞 E) y) ∈ P.asIdeal ↔ algebraMap (OF E) (𝓞 E) y ∈ P.asIdeal`.

Rewrite using `[AlgEquiv.commutes]`.
-/
theorem splits_of_absNorm {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E))
    (hv : Over P v) (hN : Ideal.absNorm P.asIdeal = l) (x : 𝓞 E) (hx : x - cj x ∉ P.asIdeal) : Splits v := by
  have := P.isPrime
  let P' : HeightOneSpectrum (𝓞 E) := ⟨P.asIdeal.comap (cj).toRingEquiv.toRingHom, Ideal.comap_isPrime _ _, fun h => by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have : (cj).symm y ∈ P.asIdeal.comap (cj).toRingEquiv.toRingHom := by
      rw [Ideal.mem_comap]; simpa using hy
    rw [h, Ideal.mem_bot] at this
    exact hy0 (by simpa using this)⟩
  refine ⟨P, P', fun e => hx ?_, hv, ?_⟩
  · haveI : Fact (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime := ⟨by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]; exact hl⟩
    have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal) = ⊤ := by
      rcases (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal)).eq_bot_or_eq_top_of_prime_card with h | h
      · exact absurd (AddSubgroup.zmultiples_eq_bot.1 h) one_ne_zero
      · exact h
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (htop ▸ AddSubgroup.mem_top (Ideal.Quotient.mk P.asIdeal x))
    have h1 : x - n ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq, ← hn]; simp
    have h2 : x - n ∈ P'.asIdeal := e ▸ h1
    have h3 : cj x - n ∈ P.asIdeal := by
      have : cj (x - n) ∈ P.asIdeal := h2
      simpa using this
    have := P.asIdeal.sub_mem h1 h3
    simpa using this
  · unfold Over at hv ⊢
    rw [← hv]
    ext y
    change cj (algebraMap (OF E) (𝓞 E) y) ∈ P.asIdeal ↔ algebraMap (OF E) (𝓞 E) y ∈ P.asIdeal
    rw [AlgEquiv.commutes]

/- English proof (translation)
Introduce `h`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hpow : z ^ 21 = 1` using `hz.pow_eq_one`. Establish `hc : cj z * z = 1`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Apply `σ.injective` to reduce the goal to its premises. Establish `hn : ‖σ (z : E)‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (n := 21) (by`. Rewrite using `[← map_pow]`. Establish `: (z : E) ^ 21 = 1` using `by exact_mod_cast congrArg (algebraMap (𝓞 E) E) hpow`. Rewrite using `[this, map_one]) (by norm_num)`.

Express the relevant statement in the definitionally equal form `σ (IsCMField.complexConj E (z : E) * (z : E)) = σ 1`. Rewrite using `[map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.conj_mul', hn]`. Simplify using the standard rewrite rules. Use `set q := Ideal.Quotient.mk P`. Establish `h1 : q z = q (cj z)` using `Ideal.Quotient.eq.2 h`.

Establish `h2 : q z ^ 2 = 1` using `by rw [sq]; nth_rw 1 [h1]; rw [← map_mul, hc, map_one]`. Establish `h3 : q z ^ 21 = 1` using `by rw [← map_pow, hpow, map_one]`. Establish `h4 : q z = 1`. Establish `: q z ^ 21 = (q z ^ 2) ^ 10 * q z` using `by ring`. Rewrite `h3` using `[this, h2]`.

Simplify using `using h3`. Establish `a3` using `congrArg q ((hz.pow (by norm_num) (show 21 = 7 * 3 by norm_num)).geom_sum_eq_zero (by norm_num))`. Establish `a7` using `congrArg q ((hz.pow (by norm_num) (show 21 = 3 * 7 by norm_num)).geom_sum_eq_zero (by norm_num))`. Simplify using `[h4] at a3 a7`. Establish `: (1 : 𝓞 E ⧸ P) = 0` using `by linear_combination a7 - 2 * a3`.

Conclude with `hP (Ideal.Quotient.zero_eq_one_iff.1 this.symm)`.
-/
theorem sub_conj_notMem {z : 𝓞 E} (hz : IsPrimitiveRoot z 21) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) : z - cj z ∉ P := by
  intro h
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hpow : z ^ 21 = 1 := hz.pow_eq_one
  have hc : cj z * z = 1 := by
    apply RingOfIntegers.ext
    apply σ.injective
    have hn : ‖σ (z : E)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := 21) (by
      rw [← map_pow]
      have : (z : E) ^ 21 = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 E) E) hpow
      rw [this, map_one]) (by norm_num)
    change σ (IsCMField.complexConj E (z : E) * (z : E)) = σ 1
    rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.conj_mul', hn]; simp
  set q := Ideal.Quotient.mk P
  have h1 : q z = q (cj z) := Ideal.Quotient.eq.2 h
  have h2 : q z ^ 2 = 1 := by rw [sq]; nth_rw 1 [h1]; rw [← map_mul, hc, map_one]
  have h3 : q z ^ 21 = 1 := by rw [← map_pow, hpow, map_one]
  have h4 : q z = 1 := by
    have : q z ^ 21 = (q z ^ 2) ^ 10 * q z := by ring
    rw [this, h2] at h3; simpa using h3
  have a3 := congrArg q ((hz.pow (by norm_num) (show 21 = 7 * 3 by norm_num)).geom_sum_eq_zero (by norm_num))
  have a7 := congrArg q ((hz.pow (by norm_num) (show 21 = 3 * 7 by norm_num)).geom_sum_eq_zero (by norm_num))
  simp [h4] at a3 a7
  have : (1 : 𝓞 E ⧸ P) = 0 := by linear_combination a7 - 2 * a3
  exact hP (Ideal.Quotient.zero_eq_one_iff.1 this.symm)

end CM

section Cyclotomic

abbrev K : Type := CyclotomicField 21 ℚ

instance : IsCyclotomicExtension {21} ℚ K := CyclotomicField.isCyclotomicExtension 21 ℚ

instance : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {21}) ⟨21, rfl, by norm_num⟩

/- English proof (translation)
The claim follows from `(IsCyclotomicExtension.zeta_spec 21 ℚ K).toInteger_isPrimitiveRoot`.
-/
theorem zeta_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta_spec 21 ℚ K).toInteger 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ K).toInteger_isPrimitiveRoot

attribute [local instance] FractionRing.liftAlgebra in

/- English proof (translation)
Establish `hu` using `Formalism.L2.Pj.unramBridge_holds K (fun P hP => ⟨_, sub_conj_notMem zeta_prim hP.ne_top⟩)`. Establish `hsep : Algebra.IsSeparable (FractionRing (OF K)) (FractionRing (𝓞 K))`. Use `Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm.toRingEquiv (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_` and prove the remaining obligations. Use extensionality with `_`. Conclude with `IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm (FractionRing.algEquiv (𝓞 K) K).symm _`.

Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Use `hM.isPrime` as an intermediate fact. Conclude with `(not_dvd_differentIdeal_iff (A := OF K) (P := M)).2 inferInstance (Ideal.dvd_iff_le.2 hle)`.
-/
theorem unramFin_K : UnramFin K := by
  have hu := Formalism.L2.Pj.unramBridge_holds K (fun P hP => ⟨_, sub_conj_notMem zeta_prim hP.ne_top⟩)
  have hsep : Algebra.IsSeparable (FractionRing (OF K)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have := hM.isPrime
  exact (not_dvd_differentIdeal_iff (A := OF K) (P := M)).2 inferInstance (Ideal.dvd_iff_le.2 hle)

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩`. Use `P.isPrime` as an intermediate fact. Use `haveI : P.asIdeal.LiesOver (Ideal.span {((43 : ℕ) : ℤ)}) := by`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime 43`.

Use `hmax.eq_of_le (Ideal.IsPrime.under ℤ P.asIdeal).ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 K) ((43 : ℕ) : ℤ) ∈ P.asIdeal`. Simplify using `using h`. Rewrite using `[← Ideal.pow_inertiaDeg 43 P.asIdeal, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 21) 43 K P.asIdeal (by norm_num)]`.

Establish `: ((43 : ℕ) : ZMod 21) = 1` using `by decide`. Rewrite using `[this, orderOf_one, pow_one]`.
-/
theorem absNorm_of_mem (P : HeightOneSpectrum (𝓞 K)) (h : ((43 : ℕ) : 𝓞 K) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = 43 := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have := P.isPrime
  haveI : P.asIdeal.LiesOver (Ideal.span {((43 : ℕ) : ℤ)}) := by
    refine ⟨?_⟩
    have hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 43
    refine hmax.eq_of_le (Ideal.IsPrime.under ℤ P.asIdeal).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) ((43 : ℕ) : ℤ) ∈ P.asIdeal
    simpa using h
  rw [← Ideal.pow_inertiaDeg 43 P.asIdeal,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 21) 43 K P.asIdeal (by norm_num)]
  have : ((43 : ℕ) : ZMod 21) = 1 := by decide
  rw [this, orderOf_one, pow_one]

/- English proof (translation)
Introduce `h` and use `by have h0 : (discr K).natAbs ∣ 21 ^ Nat.totient 21 := IsCyclotomicExtension.Rat.natAbs_discr 21 K ▸ Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (by norm_num)) have h₂ := (by norm_num : Nat.Prime 43).dvd_of_dvd_pow ((Int.natCast_dvd.1 h).trans h0) omega`.
-/
theorem not_dvd_discr : ¬ ((43 : ℕ) : ℤ) ∣ discr K := fun h => by
  have h0 : (discr K).natAbs ∣ 21 ^ Nat.totient 21 :=
    IsCyclotomicExtension.Rat.natAbs_discr 21 K ▸
      Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (by norm_num))
  have h₂ := (by norm_num : Nat.Prime 43).dvd_of_dvd_pow ((Int.natCast_dvd.1 h).trans h0)
  omega

/- English proof (translation)
Take `⟨P, hP⟩` from `exists_over v`. Use `splits_of_absNorm (by norm_num : Nat.Prime 43) P v hP (absNorm_of_mem P ?_) _ (sub_conj_notMem zeta_prim P.isPrime.ne_top)` and prove the remaining obligations. Rewrite `h` using `[← hP, Ideal.mem_comap, map_natCast]`. Conclude with `h`.
-/
theorem splits_of_mem (v : HeightOneSpectrum (OF K)) (h : ((43 : ℕ) : OF K) ∈ v.asIdeal) : Splits v := by
  obtain ⟨P, hP⟩ := exists_over v
  refine splits_of_absNorm (by norm_num : Nat.Prime 43) P v hP (absNorm_of_mem P ?_) _
    (sub_conj_notMem zeta_prim P.isPrime.ne_top)
  rw [← hP, Ideal.mem_comap, map_natCast] at h
  exact h

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩`. Establish `hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime 43`. Take `⟨⟨P, hP, hl⟩⟩` from `(Ideal.span {((43 : ℕ) : ℤ)}).nonempty_primesOver (S := OF K)`. Use `⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {((43 : ℕ) : ℤ)}) (by simp) P⟩, ?_⟩` and prove the remaining obligations. Establish `: ((43 : ℕ) : ℤ) ∈ P.under ℤ` using `hl.over ▸ Ideal.mem_span_singleton_self _`.

Simplify `this` using `[Ideal.mem_comap]`.
-/
theorem exists_place : ∃ v : HeightOneSpectrum (OF K), ((43 : ℕ) : OF K) ∈ v.asIdeal := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 43
  obtain ⟨⟨P, hP, hl⟩⟩ := (Ideal.span {((43 : ℕ) : ℤ)}).nonempty_primesOver (S := OF K)
  refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {((43 : ℕ) : ℤ)}) (by simp) P⟩, ?_⟩
  have : ((43 : ℕ) : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
  simpa [Ideal.mem_comap] using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h1, h2⟩`. Establish `hn : n ≠ 0` using `by rintro rfl; exact h1 (by simp)`. Use `(h2 v (dvd_pow_self _ hn)).2.1` as an intermediate fact. Rewrite `this` using `[expIn_pow]`.

Use linear arithmetic over natural numbers and integers. Introduce `hn`. Establish `hn0 : n ≠ 0` using `by omega`. Use `⟨pow_ne_zero _ v.ne_bot, fun e => v.isPrime.ne_top ?_, fun w hw => ?_⟩` and prove the remaining obligations. Conclude with `top_le_iff.1 (e ▸ Ideal.pow_le_self hn0)`.

Establish `hwv : w = v`. Use `Ideal.dvd_iff_le.1 (w.prime.dvd_of_dvd_pow hw)` as an intermediate fact. Conclude with `HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top this).symm`. Substitute `hwv` using the available equality. Use `⟨splits_of_mem w h, by rw [expIn_pow]; omega, 43, by norm_num, by norm_num, h, not_dvd_discr, absNorm_of_mem⟩` and prove the remaining obligations.
-/
theorem isBaseCond_pow (v : HeightOneSpectrum (OF K)) (h : ((43 : ℕ) : OF K) ∈ v.asIdeal) (n : ℕ) :
    IsBaseCond (v.asIdeal ^ n) ↔ n = 1 ∨ n = 2 := by
  constructor
  · rintro ⟨-, h1, h2⟩
    have hn : n ≠ 0 := by rintro rfl; exact h1 (by simp)
    have := (h2 v (dvd_pow_self _ hn)).2.1
    rw [expIn_pow] at this
    omega
  · intro hn
    have hn0 : n ≠ 0 := by omega
    refine ⟨pow_ne_zero _ v.ne_bot, fun e => v.isPrime.ne_top ?_, fun w hw => ?_⟩
    · exact top_le_iff.1 (e ▸ Ideal.pow_le_self hn0)
    · have hwv : w = v := by
        have := Ideal.dvd_iff_le.1 (w.prime.dvd_of_dvd_pow hw)
        exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top this).symm
      subst hwv
      refine ⟨splits_of_mem w h, by rw [expIn_pow]; omega, 43, by norm_num, by norm_num, h, not_dvd_discr, absNorm_of_mem⟩

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_place`. Use `⟨unramFin_K, isCMType_places, v, splits_of_mem v hv, ?_, (isBaseCond_pow v hv 2).2 (Or.inr rfl), ?_, by simp [IsFinSetSplitPlacesCoprimeConductor], fun h => (h v (by simp)).2 dvd_rfl, fun q hq => ?_⟩` and prove the remaining obligations. Simplify using `using (isBaseCond_pow v hv 1).2 (Or.inl rfl)`. Rewrite using `[isBaseCond_pow v hv]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.mem_singleton.1 hq]`. Conclude with `⟨splits_of_mem v hv, fun h => v.isPrime.ne_top (by rwa [Ideal.dvd_iff_le, top_le_iff] at h)⟩`.
-/
theorem inhabited_K : UnramFin K ∧ IsCMType (fun w : InfinitePlace K => w.embedding) ∧
    ∃ v : HeightOneSpectrum (OF K), Splits v ∧ IsBaseCond v.asIdeal ∧ IsBaseCond (v.asIdeal ^ 2) ∧
      ¬ IsBaseCond (v.asIdeal ^ 3) ∧ IsFinSetSplitPlacesCoprimeConductor v.asIdeal ∅ ∧ ¬ IsFinSetSplitPlacesCoprimeConductor v.asIdeal {v} ∧ IsFinSetSplitPlacesCoprimeConductor ⊤ {v} := by
  obtain ⟨v, hv⟩ := exists_place
  refine ⟨unramFin_K, isCMType_places, v, splits_of_mem v hv, ?_, (isBaseCond_pow v hv 2).2 (Or.inr rfl), ?_, by simp [IsFinSetSplitPlacesCoprimeConductor],
    fun h => (h v (by simp)).2 dvd_rfl, fun q hq => ?_⟩
  · simpa using (isBaseCond_pow v hv 1).2 (Or.inl rfl)
  · rw [isBaseCond_pow v hv]; omega
  · rw [Finset.mem_singleton.1 hq]
    exact ⟨splits_of_mem v hv, fun h => v.isPrime.ne_top (by rwa [Ideal.dvd_iff_le, top_le_iff] at h)⟩

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_place`. Establish `hb` using `(isBaseCond_pow v hv 2).2 (Or.inr rfl)`. Take `⟨χ, hχ⟩` from `ValEx.exists_isValChar K _ isCMType_places s κ v hb`. Take `⟨P, hP⟩` from `exists_over v`. Use `⟨v, hb, χ, hχ, P, fun hu => ?_⟩` and prove the remaining obligations.

Establish `h` using `(hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)`. Rewrite `h` using `[expIn_pow]`. Establish `h0` using `(h 0).1 (((expAt_zero_iff χ P).2 hu 0).2 le_rfl)`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_isValChar_K (s : ℕ) (κ : InfinitePlace K → ℕ) :
    ∃ v : HeightOneSpectrum (OF K), IsBaseCond (v.asIdeal ^ 2) ∧ ∃ χ : HChar K,
      IsValChar (fun w : InfinitePlace K => w.embedding) s κ (v.asIdeal ^ 2) ∅ χ ∧ ∃ P, ¬ χ.UnrAt P := by
  obtain ⟨v, hv⟩ := exists_place
  have hb := (isBaseCond_pow v hv 2).2 (Or.inr rfl)
  obtain ⟨χ, hχ⟩ := ValEx.exists_isValChar K _ isCMType_places s κ v hb
  obtain ⟨P, hP⟩ := exists_over v
  refine ⟨v, hb, χ, hχ, P, fun hu => ?_⟩
  have h := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
  rw [expIn_pow] at h
  have h0 := (h 0).1 (((expAt_zero_iff χ P).2 hu 0).2 le_rfl)
  omega

end Cyclotomic

end GlobalTheory.CMVal.InhabK
