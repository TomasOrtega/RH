import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ConjCurve

/- English proof (translation)
Distinguish the cases in `hKt : K = ⊤`. Take `⟨a, haJ, ha⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hJ`. Take `⟨A, hA⟩ : J ∣ Ideal.span {a}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)`. Use `⟨a, A, ha, hA, ?_⟩` and prove the remaining obligations. Rewrite using `[hKt, top_sup_eq]`.

Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (I := J * K) (J := J) Ideal.mul_le_left (mul_ne_zero hJ hK)`. Take `⟨A, hA⟩ : J ∣ Ideal.span {a}` from `Ideal.dvd_iff_le.mpr (le_sup_right.trans ha.le)`. Establish `hsup : K ⊔ A = ⊤`. Apply `mul_left_cancel₀ (a := J) hJ` to reduce the goal to its premises. Rewrite using `[Ideal.mul_sup, ← hA, ha, Ideal.mul_top]`.

Use `⟨a, A, ?_, hA, hsup⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hA` using `[Ideal.span_singleton_eq_bot.mpr rfl]`. Establish `hA0 : A = ⊥` using `(mul_eq_zero.mp hA.symm).resolve_left hJ`. Rewrite `hsup` using `[hA0, sup_bot_eq]`.

Conclude with `hKt hsup`.
-/
theorem exists_span_eq_mul {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J K : Ideal R) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a : R) (A : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * A ∧ K ⊔ A = ⊤ := by
  by_cases hKt : K = ⊤
  · obtain ⟨a, haJ, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    obtain ⟨A, hA⟩ : J ∣ Ideal.span {a} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)
    refine ⟨a, A, ha, hA, ?_⟩
    rw [hKt, top_sup_eq]
  · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := J * K) (J := J)
      Ideal.mul_le_left (mul_ne_zero hJ hK)
    obtain ⟨A, hA⟩ : J ∣ Ideal.span {a} :=
      Ideal.dvd_iff_le.mpr (le_sup_right.trans ha.le)
    have hsup : K ⊔ A = ⊤ := by
      apply mul_left_cancel₀ (a := J) hJ
      rw [Ideal.mul_sup, ← hA, ha, Ideal.mul_top]
    refine ⟨a, A, ?_, hA, hsup⟩
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hA
    have hA0 : A = ⊥ := (mul_eq_zero.mp hA.symm).resolve_left hJ
    rw [hA0, sup_bot_eq] at hsup
    exact hKt hsup

/- English proof (translation)
Take `⟨a, A, ha, hA, -⟩` from `exists_span_eq_mul I K hI hK`. Establish `hA0 : A ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hA` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha hA`.

Take `⟨a', B, ha', hB, hK'⟩` from `exists_span_eq_mul A K hA0 hK`. Use `⟨a, a', B, ha, ha', ?_, hK', ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hB` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha' hB`.

Rewrite using `[hA, hB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_equiv_comaximal {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I K : Ideal R) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a a' : R) (B : Ideal R), a ≠ 0 ∧ a' ≠ 0 ∧ B ≠ ⊥ ∧ K ⊔ B = ⊤ ∧
      Ideal.span {a} * B = Ideal.span {a'} * I := by
  obtain ⟨a, A, ha, hA, -⟩ := exists_span_eq_mul I K hI hK
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hA
    exact ha hA
  obtain ⟨a', B, ha', hB, hK'⟩ := exists_span_eq_mul A K hA0 hK
  refine ⟨a, a', B, ha, ha', ?_, hK', ?_⟩
  · rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hB
    exact ha' hB
  · rw [hA, hB]; ring

/- English proof (translation)
Apply `Nat.Coprime.symm` to reduce the goal to its premises. Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `p hp hpN hpB`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : Finite (𝓞 K ⧸ B) := Ideal.finiteQuotientOfFreeOfNeBot B hB`.

Rewrite `hpB` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ B) p hpB`. Establish `hN : N • x = 0`. Rewrite using `[← addOrderOf_dvd_iff_nsmul_eq_zero, hx]`. Conclude with `hpN`.

Establish `h1 : (1 : 𝓞 K) ∈ Ideal.span {(N : 𝓞 K)} ⊔ B` using `by rw [h]; trivial`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp h1`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Establish `h2 : Ideal.Quotient.mk B u * (N : 𝓞 K ⧸ B) = 1`. Use `congrArg (Ideal.Quotient.mk B) hyz` as an intermediate fact.

Rewrite `this` using `[map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hz, add_zero, map_mul, map_natCast, map_one]`. Conclude with `this`. Establish `hx0 : x = 0`. Rewrite using `[← one_mul x, ← h2, mul_assoc, ← nsmul_eq_mul, hN, mul_zero]`. Rewrite `hx` using `[hx0, addOrderOf_zero]`.

Conclude with `hp.one_lt.ne hx`.
-/
theorem coprime_absNorm {K : Type*} [Field K] [NumberField K] (B : Ideal (𝓞 K)) (hB : B ≠ ⊥) (N : ℕ)
    (h : Ideal.span {(N : 𝓞 K)} ⊔ B = ⊤) : Nat.Coprime (Ideal.absNorm B) N := by
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro p hp hpN hpB
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (𝓞 K ⧸ B) := Ideal.finiteQuotientOfFreeOfNeBot B hB
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpB
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ B) p hpB
  have hN : N • x = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hx]; exact hpN
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {(N : 𝓞 K)} ⊔ B := by rw [h]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have h2 : Ideal.Quotient.mk B u * (N : 𝓞 K ⧸ B) = 1 := by
    have := congrArg (Ideal.Quotient.mk B) hyz
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hz, add_zero, map_mul, map_natCast, map_one] at this
    exact this
  have hx0 : x = 0 := by
    rw [← one_mul x, ← h2, mul_assoc, ← nsmul_eq_mul, hN, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

/- English proof (translation)
Establish `h1 : w₁ ∈ Λ` using `(hΛ _).mpr ⟨1, 0, by simp⟩`. Take `⟨a, b, hab⟩` from `(hΛ _).mp (hst s _ h1)`. Establish `hb : (b : ℂ) ≠ 0`. Introduce `hb`. Rewrite `hab` using `[hb, zero_mul, add_zero]`.

Conclude with `hs a (mul_right_cancel₀ hw hab).symm`. Set `I : Ideal R` to `{ carrier := {r | w₁ / b * f r ∈ Λ} add_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_add, mul_add] at *`. Conclude with `Λ.add_mem hx hy`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := fun c x hx => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *`. Use `hst c _ hx` as an intermediate fact. Rewrite using `[mul_left_comm] at this }` and apply the resulting hypothesis. Establish `hI : ∀ r, r ∈ I ↔ w₁ / b * f r ∈ Λ` using `fun r => Iff.rfl`.

Use `⟨I, w₁ / b, ?_, div_ne_zero hw hb, fun z => ⟨fun hz => ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `h0`. Establish `: (b : R) ∈ I`. Rewrite using `[hI, map_intCast, div_mul_cancel₀ _ hb]`. Conclude with `h1`.

Rewrite `this` using `[h0, Ideal.mem_bot]`. Apply `hb` to reduce the goal to its premises. Rewrite using `[← map_intCast f b, this, map_zero]`. Take `⟨m, n, hmn⟩` from `(hΛ _).mp hz`. Establish `: z = w₁ / b * f (m * b + n * (s - a))`.

Simplify using `only [map_add, map_mul, map_sub, map_intCast]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-b) * hmn + n * hab`. Conclude with `⟨_, (hI _).mpr (this ▸ hz), this⟩`. Introduce and unpack `⟨c, hc, rfl⟩`.

Conclude with `(hI _).mp hc`.
-/
theorem exists_ideal {R : Type*} [CommRing R] (f : R →+* ℂ) (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ)
    (hw : w₁ ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, m * w₁ + n * w₂ = z)
    (hst : ∀ r : R, ∀ z ∈ Λ, f r * z ∈ Λ) (s : R) (hs : ∀ a : ℤ, f s ≠ a) :
    ∃ (I : Ideal R) (δ : ℂ), I ≠ ⊥ ∧ δ ≠ 0 ∧ ∀ z, z ∈ Λ ↔ ∃ c ∈ I, z = δ * f c := by
  have h1 : w₁ ∈ Λ := (hΛ _).mpr ⟨1, 0, by simp⟩
  obtain ⟨a, b, hab⟩ := (hΛ _).mp (hst s _ h1)
  have hb : (b : ℂ) ≠ 0 := by
    intro hb
    rw [hb, zero_mul, add_zero] at hab
    exact hs a (mul_right_cancel₀ hw hab).symm
  let I : Ideal R :=
    { carrier := {r | w₁ / b * f r ∈ Λ}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add, mul_add] at *
        exact Λ.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        have := hst c _ hx
        rwa [mul_left_comm] at this }
  have hI : ∀ r, r ∈ I ↔ w₁ / b * f r ∈ Λ := fun r => Iff.rfl
  refine ⟨I, w₁ / b, ?_, div_ne_zero hw hb, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · intro h0
    have : (b : R) ∈ I := by
      rw [hI, map_intCast, div_mul_cancel₀ _ hb]; exact h1
    rw [h0, Ideal.mem_bot] at this
    apply hb
    rw [← map_intCast f b, this, map_zero]
  · obtain ⟨m, n, hmn⟩ := (hΛ _).mp hz
    have : z = w₁ / b * f (m * b + n * (s - a)) := by
      simp only [map_add, map_mul, map_sub, map_intCast]
      field_simp
      linear_combination (-b) * hmn + n * hab
    exact ⟨_, (hI _).mpr (this ▸ hz), this⟩
  · rintro ⟨c, hc, rfl⟩
    exact (hI _).mp hc

/- English proof (translation)
Unfold `eisG`. Set `e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ' ∧ w ≠ 0}` to `(Equiv.mulLeft₀ δ hδ).subtypeEquiv fun w => by`. Simplify using `[h, hδ]`. Rewrite using `[← e.tsum_eq, ← tsum_mul_left]`. Use `congr 1`.

Use extensionality with `w`. Establish `: ((e w : {w : ℂ // w ∈ Λ' ∧ w ≠ 0}) : ℂ) = δ * w` using `rfl`. Rewrite using `[this, mul_pow]`. Use `w.2.2` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem eisG_smul (Λ Λ' : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (h : ∀ z, δ * z ∈ Λ' ↔ z ∈ Λ) (k : ℕ) :
    eisG Λ k = δ ^ (2 * k) * eisG Λ' k := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ' ∧ w ≠ 0} :=
    (Equiv.mulLeft₀ δ hδ).subtypeEquiv fun w => by
      simp [h, hδ]
  rw [← e.tsum_eq, ← tsum_mul_left]
  congr 1
  ext w
  have : ((e w : {w : ℂ // w ∈ Λ' ∧ w ≠ 0}) : ℂ) = δ * w := rfl
  rw [this, mul_pow]
  have := w.2.2
  field_simp

/- English proof (translation)
Unfold `TaylorLogMetric.discr g2 g3`. Rewrite using `[eisG_smul Λ Λ' δ hδ h 2, eisG_smul Λ Λ' δ hδ h 3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem discr_smul (Λ Λ' : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (h : ∀ z, δ * z ∈ Λ' ↔ z ∈ Λ) :
    TaylorLogMetric.discr Λ = δ ^ 12 * TaylorLogMetric.discr Λ' := by
  unfold TaylorLogMetric.discr g2 g3
  rw [eisG_smul Λ Λ' δ hδ h 2, eisG_smul Λ Λ' δ hδ h 3]
  ring

noncomputable def embK (D : D7) : 𝓞 D.host.K →+* ℂ :=
  D.host.φ₀.comp ((D.host.K.val.toRingHom).comp (algebraMap (𝓞 D.host.K) D.host.K))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embK_apply (D : D7) (c : 𝓞 D.host.K) :
    embK D c = D.host.φ₀ (((c : D.host.K) : D.host.E)) := rfl

/- English proof (translation)
Introduce `_ _ h` and use `IsFractionRing.injective (𝓞 D.host.K) D.host.K (D.host.K.val.toRingHom.injective (D.host.φ₀.injective h))`.
-/
theorem embK_injective (D : D7) : Function.Injective (embK D) := fun _ _ h =>
  IsFractionRing.injective (𝓞 D.host.K) D.host.K
    (D.host.K.val.toRingHom.injective (D.host.φ₀.injective h))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, cc.zero_mem, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, rfl⟩` from `hx`. Take `⟨c', hc', rfl⟩` from `hy`. Conclude with `⟨c + c', cc.add_mem hc hc', by rw [map_add, mul_add]⟩`. Consider the case `neg x _ hx`.

Take `⟨c, hc, rfl⟩` from `hx`. Conclude with `⟨-c, cc.neg_mem hc, by rw [map_neg, mul_neg]⟩`. Introduce `hz`. Conclude with `AddSubgroup.subset_closure hz`.
-/
theorem mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ z : ℂ) :
    z ∈ lamOf D cc δ ↔ ∃ c ∈ cc, z = δ * embK D c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by rw [map_add, mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by rw [map_neg, mul_neg]⟩
  · intro hz
    exact AddSubgroup.subset_closure hz

/- English proof (translation)
Establish `hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqrtMinusD_sq`. Establish `hm : D.host.sqrtMinusD ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Establish `hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hm⟩ : D.host.K)`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Establish `: (⟨D.host.sqrtMinusD, hm⟩ : D.host.K) ^ 2 = algebraMap ℤ _ (-(D.host.d : ℤ))`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hb`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Use `⟨⟨_, hi⟩, fun a ha => ?_⟩` and prove the remaining obligations.

Establish `h1 : D.host.φ₀ D.host.sqrtMinusD = a` using `ha`. Establish `h2` using `congrArg D.host.φ₀ hb`. Rewrite `h2` using `[map_pow, h1, map_neg, map_natCast]`. Establish `h3 : a ^ 2 = -(D.host.d : ℤ)` using `by exact_mod_cast h2`. Establish `hd : (0 : ℤ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`.

Use polynomial arithmetic with `[sq_nonneg a]`.
-/
theorem exists_not_int (D : D7) : ∃ s : 𝓞 D.host.K, ∀ a : ℤ, embK D s ≠ a := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hm : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hm⟩ : D.host.K) := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    have : (⟨D.host.sqrtMinusD, hm⟩ : D.host.K) ^ 2 = algebraMap ℤ _ (-(D.host.d : ℤ)) := by
      apply Subtype.ext
      simpa using hb
    rw [this]
    exact isIntegral_algebraMap
  refine ⟨⟨_, hi⟩, fun a ha => ?_⟩
  have h1 : D.host.φ₀ D.host.sqrtMinusD = a := ha
  have h2 := congrArg D.host.φ₀ hb
  rw [map_pow, h1, map_neg, map_natCast] at h2
  have h3 : a ^ 2 = -(D.host.d : ℤ) := by exact_mod_cast h2
  have hd : (0 : ℤ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  nlinarith [sq_nonneg a]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_not_int D`. Take `⟨I, δ, hI, hδ, hmem⟩` from `exists_ideal (embK D) Λ w₁ w₂ hw hΛ hst s hs`. Establish `hN : 2 * D.host.d * n ≠ 0`. Use `D.host.hyp.2.1.pos` as an intermediate fact. Check the signs of the components of the expression.

Take `⟨a, a', B, ha, ha', hB, hsup, hEq⟩` from `exists_equiv_comaximal I (Ideal.span {((2 * D.host.d * n : ℕ) : 𝓞 D.host.K)}) hI (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.mpr hN)`. Establish `hco` using `coprime_absNorm B hB _ hsup`. Establish `hfa : embK D a ≠ 0` using `(map_ne_zero_iff _ (embK_injective D)).mpr ha`. Establish `hfa' : embK D a' ≠ 0` using `(map_ne_zero_iff _ (embK_injective D)).mpr ha'`. Use `set δ' := δ * embK D a / embK D a' with hδ'`.

Establish `hδ0 : δ' ≠ 0` using `div_ne_zero (mul_ne_zero hδ hfa) hfa'`. Establish `hL : Λ = lamOf D B δ'`. Use extensionality with `z`. Rewrite using `[hmem, mem_lamOf]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, rfl⟩`. Establish `: a' * c ∈ Ideal.span {a} * B`. Rewrite using `[hEq]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨c, hc, rfl⟩`. Take `⟨b, hb, hab⟩` from `Ideal.mem_span_singleton_mul.mp this`.

Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Use `congrArg (embK D) hab` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Rewrite using `[hδ']`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-this`. Introduce and unpack `⟨b, hb, rfl⟩`. Establish `: a * b ∈ Ideal.span {a'} * I`. Rewrite using `[← hEq]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨b, hb, rfl⟩`.

Take `⟨c, hc, hac⟩` from `Ideal.mem_span_singleton_mul.mp this`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Use `congrArg (embK D) hac` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Rewrite using `[hδ']`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-this`. Use `⟨B, δ', ⟨⟨hB, Nat.Coprime.coprime_mul_right_right hco⟩, ?_⟩, Nat.Coprime.coprime_mul_left_right hco, hL⟩` and prove the remaining obligations. Unfold `IsDiscriminantTwelfthRootOfIdealLattice`. Rewrite using `[discr_smul (lamOf D B 1) Λ δ' hδ0, hd, mul_one]`.

Introduce `z`. Rewrite using `[hL, mem_lamOf, mem_lamOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, h⟩`. Conclude with `⟨c, hc, by rw [one_mul]; exact mul_left_cancel₀ hδ0 h⟩`.

Introduce and unpack `⟨c, hc, h⟩`. Conclude with `⟨c, hc, by rw [h, one_mul]⟩`.
-/
theorem exists_crv (D : D7) (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ)
    (hw : w₁ ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, m * w₁ + n * w₂ = z)
    (hst : ∀ r, ∀ z ∈ Λ, embK D r * z ∈ Λ) (hd : TaylorLogMetric.discr Λ = 1) (n : ℕ) (hn : 0 < n) :
    ∃ (cc' : Ideal (𝓞 D.host.K)) (δ' : ℂ), Crv D cc' δ' ∧ Nat.Coprime (Ideal.absNorm cc') n ∧
      Λ = lamOf D cc' δ' := by
  obtain ⟨s, hs⟩ := exists_not_int D
  obtain ⟨I, δ, hI, hδ, hmem⟩ := exists_ideal (embK D) Λ w₁ w₂ hw hΛ hst s hs
  have hN : 2 * D.host.d * n ≠ 0 := by
    have := D.host.hyp.2.1.pos
    positivity
  obtain ⟨a, a', B, ha, ha', hB, hsup, hEq⟩ := exists_equiv_comaximal I
    (Ideal.span {((2 * D.host.d * n : ℕ) : 𝓞 D.host.K)}) hI
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.mpr hN)
  have hco := coprime_absNorm B hB _ hsup
  have hfa : embK D a ≠ 0 := (map_ne_zero_iff _ (embK_injective D)).mpr ha
  have hfa' : embK D a' ≠ 0 := (map_ne_zero_iff _ (embK_injective D)).mpr ha'
  set δ' := δ * embK D a / embK D a' with hδ'
  have hδ0 : δ' ≠ 0 := div_ne_zero (mul_ne_zero hδ hfa) hfa'
  have hL : Λ = lamOf D B δ' := by
    ext z
    rw [hmem, mem_lamOf]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have : a' * c ∈ Ideal.span {a} * B := by
        rw [hEq]; exact Ideal.mem_span_singleton_mul.mpr ⟨c, hc, rfl⟩
      obtain ⟨b, hb, hab⟩ := Ideal.mem_span_singleton_mul.mp this
      refine ⟨b, hb, ?_⟩
      have := congrArg (embK D) hab
      rw [map_mul, map_mul] at this
      rw [hδ']
      field_simp
      linear_combination -this
    · rintro ⟨b, hb, rfl⟩
      have : a * b ∈ Ideal.span {a'} * I := by
        rw [← hEq]; exact Ideal.mem_span_singleton_mul.mpr ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac⟩ := Ideal.mem_span_singleton_mul.mp this
      refine ⟨c, hc, ?_⟩
      have := congrArg (embK D) hac
      rw [map_mul, map_mul] at this
      rw [hδ']
      field_simp
      linear_combination -this
  refine ⟨B, δ', ⟨⟨hB, Nat.Coprime.coprime_mul_right_right hco⟩, ?_⟩,
    Nat.Coprime.coprime_mul_left_right hco, hL⟩
  unfold IsDiscriminantTwelfthRootOfIdealLattice
  rw [discr_smul (lamOf D B 1) Λ δ' hδ0, hd, mul_one]
  intro z
  rw [hL, mem_lamOf, mem_lamOf]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [one_mul]; exact mul_left_cancel₀ hδ0 h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [h, one_mul]⟩

/- English proof (translation)
Introduce `D cc δ hc M ρ hK h2 h3 n hn`. Take `⟨⟨w₁, w₂, hli, hcl⟩, -, hdisc, -, hO⟩` from `GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc`. Establish `hstar` using `(GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc M ρ hK h2 h3).2.2.2.2.1`. Use `set Λ := lamOf D cc δ with hΛ`. Set `L : PeriodPair` to `⟨w₁, w₂, hli⟩`.

Establish `hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice`. Introduce `z`. Rewrite using `[hcl, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`. Simplify using `[L]`. Establish `hρ : (ρ (TaylorLogMetric.liftM M (g2 Λ))) ^ 3 - 27 * (ρ (TaylorLogMetric.liftM M (g3 Λ))) ^ 2 = 1`.

Establish `: (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Unfold `TaylorLogMetric.liftM`. Rewrite using `[dif_pos h2, dif_pos h3]`. Conclude with `hdisc`.

Establish `h` using `congrArg ρ this`. Simplify `h` using `[map_ofNat]`. Take `⟨L', hL2, hL3⟩` from `(GlobalTheory.T.latticeInvariants_periodPair_dictionary L Λ hL).2.2.2.2.2.2 _ _ (by rw [hρ]; exact one_ne_zero)`. Establish `hP` using `GlobalTheory.T.latticeInvariants_periodPair_dictionary L' L'.lattice.toAddSubgroup (fun z => Iff.rfl)`. Establish `hspec : g2 (lamConj M ρ Λ) = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 (lamConj M ρ Λ) = ρ (TaylorLogMetric.liftM M (g3 Λ))` using `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨L'.lattice.toAddSubgroup, hP.1.trans hL2, hP.2.1.trans hL3⟩`.

Establish `hEq : lamConj M ρ Λ = L'.lattice.toAddSubgroup` using `hP.2.2.2.2.2.1 _ (hspec.1.trans (hP.1.trans hL2).symm) (hspec.2.trans (hP.2.1.trans hL3).symm)`. Use `exists_crv D _ L'.ω₁ L'.ω₂ ?_ ?_ ?_ ?_ n hn` and prove the remaining obligations. Simplify using `using L'.indep.ne_zero 0`. Introduce `z`. Rewrite using `[hEq]`.

Conclude with `PeriodPair.mem_lattice`. Introduce `r z hz`. Break down `hstar r 0 z (Or.inl ⟨Λ.zero_mem, hz⟩) with h | h` into its components or cases. Conclude with `h.2`. Conclude with `absurd (by rw [mul_zero]; exact Λ.zero_mem) h.1`.

Unfold `TaylorLogMetric.discr`. Rewrite using `[hspec.1, hspec.2, hρ]`.
-/
theorem galCurve_holds : ∀ D : D7, galCurve D := by
  intro D cc δ hc M ρ hK h2 h3 n hn
  obtain ⟨⟨w₁, w₂, hli, hcl⟩, -, hdisc, -, hO⟩ := GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc
  have hstar := (GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc M ρ hK h2 h3).2.2.2.2.1
  set Λ := lamOf D cc δ with hΛ
  let L : PeriodPair := ⟨w₁, w₂, hli⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hcl, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  have hρ : (ρ (TaylorLogMetric.liftM M (g2 Λ))) ^ 3 - 27 * (ρ (TaylorLogMetric.liftM M (g3 Λ))) ^ 2 = 1 := by
    have : (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 = 1 := by
      apply Subtype.ext
      unfold TaylorLogMetric.liftM
      rw [dif_pos h2, dif_pos h3]
      exact hdisc
    have h := congrArg ρ this
    simpa [map_ofNat] using h
  obtain ⟨L', hL2, hL3⟩ := (GlobalTheory.T.latticeInvariants_periodPair_dictionary L Λ hL).2.2.2.2.2.2 _ _ (by rw [hρ]; exact one_ne_zero)
  have hP := GlobalTheory.T.latticeInvariants_periodPair_dictionary L' L'.lattice.toAddSubgroup (fun z => Iff.rfl)
  have hspec : g2 (lamConj M ρ Λ) = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 (lamConj M ρ Λ) = ρ (TaylorLogMetric.liftM M (g3 Λ)) :=
    Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ)))
      ⟨L'.lattice.toAddSubgroup, hP.1.trans hL2, hP.2.1.trans hL3⟩
  have hEq : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    hP.2.2.2.2.2.1 _ (hspec.1.trans (hP.1.trans hL2).symm) (hspec.2.trans (hP.2.1.trans hL3).symm)
  refine exists_crv D _ L'.ω₁ L'.ω₂ ?_ ?_ ?_ ?_ n hn
  · simpa using L'.indep.ne_zero 0
  · intro z
    rw [hEq]
    exact PeriodPair.mem_lattice
  · intro r z hz
    rcases hstar r 0 z (Or.inl ⟨Λ.zero_mem, hz⟩) with h | h
    · exact h.2
    · exact absurd (by rw [mul_zero]; exact Λ.zero_mem) h.1
  · unfold TaylorLogMetric.discr
    rw [hspec.1, hspec.2, hρ]

end GlobalTheory.ConjCurve
