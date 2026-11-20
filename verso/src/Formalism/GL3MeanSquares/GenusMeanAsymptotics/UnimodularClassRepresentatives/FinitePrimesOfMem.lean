import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SummableSqGeom

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)`.
-/
theorem ne_bot_of_max {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

/- English proof (translation)
The claim follows from `(IdealNormInequalities.resChar_prime h𝔭).two_le.trans (IdealNormInequalities.resChar_le_absNorm h𝔭)`.
-/
theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 :=
  (IdealNormInequalities.resChar_prime h𝔭).two_le.trans (IdealNormInequalities.resChar_le_absNorm h𝔭)

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun 𝔭 => by positivity) (fun 𝔭 => ?_) (IdealNormInequalities.summable_resChar_sq (K := F))` and prove the remaining obligations. Establish `h1 : (0 : ℝ) < (IdealNormInequalities.resChar 𝔭.1 : ℝ)`. Conclude with `(IdealNormInequalities.resChar_prime 𝔭.2).pos` after adjusting the coercions. Establish `h2 : (IdealNormInequalities.resChar 𝔭.1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ)`. Conclude with `IdealNormInequalities.resChar_le_absNorm 𝔭.2` after adjusting the coercions.

Conclude with `inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)`.
-/
theorem summable_inv_absNorm_sq :
    Summable fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => ((Ideal.absNorm 𝔭.1 : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun 𝔭 => by positivity) (fun 𝔭 => ?_)
    (IdealNormInequalities.summable_resChar_sq (K := F))
  have h1 : (0 : ℝ) < (IdealNormInequalities.resChar 𝔭.1 : ℝ) := by
    exact_mod_cast (IdealNormInequalities.resChar_prime 𝔭.2).pos
  have h2 : (IdealNormInequalities.resChar 𝔭.1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    exact_mod_cast IdealNormInequalities.resChar_le_absNorm 𝔭.2
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)

/- English proof (translation)
Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hn`.
-/
theorem absNorm_span_ne_zero {n : 𝓞 F} (hn : n ≠ 0) : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hn

/- English proof (translation)
Establish `h1 : Ideal.span {n} ≤ 𝔭 ^ e` using `(Ideal.span_singleton_le_iff_mem _).mpr he`. Establish `h2` using `Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn)) (Ideal.absNorm_dvd_absNorm_of_le h1)`. Rewrite `h2` using `[map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lt_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {e : ℕ}
    (he : n ∈ 𝔭 ^ e) : e < Ideal.absNorm (Ideal.span {n}) := by
  have h1 : Ideal.span {n} ≤ 𝔭 ^ e := (Ideal.span_singleton_le_iff_mem _).mpr he
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le h1)
  rw [map_pow] at h2
  calc e < 2 ^ e := Nat.lt_two_pow_self
    _ ≤ Ideal.absNorm 𝔭 ^ e := Nat.pow_le_pow_left (two_le_absNorm h𝔭) e
    _ ≤ _ := h2

/- English proof (translation)
Establish `hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e}` using `⟨Ideal.absNorm (Ideal.span {n}), fun e he => (lt_of_mem_pow h𝔭 hn he).le⟩`. Prove the components needed by the constructor for the conclusion. Introduce `he`. Conclude with `le_csSup hb he`. Introduce `he`.

Establish `hm : vF 𝔭 n ∈ {e : ℕ | n ∈ 𝔭 ^ e}` using `Nat.sSup_mem ⟨0, by simp⟩ hb`. Conclude with `Ideal.pow_le_pow_right he hm`.
-/
theorem mem_pow_iff_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} :=
    ⟨Ideal.absNorm (Ideal.span {n}), fun e he => (lt_of_mem_pow h𝔭 hn he).le⟩
  constructor
  · intro he
    exact le_csSup hb he
  · intro he
    have hm : vF 𝔭 n ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem ⟨0, by simp⟩ hb
    exact Ideal.pow_le_pow_right he hm

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn` and prove the remaining obligations. Use `(Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm (Ideal.span {n}))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨𝔭, h𝔭, rfl⟩`. Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn)) (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h𝔭))`.
-/
theorem finite_primes_of_mem {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | n ∈ 𝔭.1}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm (Ideal.span {n}))).subset ?_
  rintro _ ⟨𝔭, h𝔭, rfl⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h𝔭))

open scoped Classical in

def valF (n : 𝓞 F) : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ :=
  if hn : n ≠ 0 then
    Finsupp.onFinset (finite_primes_of_mem hn).toFinset (fun 𝔭 => vF 𝔭.1 n) (fun 𝔭 h => by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := (mem_pow_iff_le_vF 𝔭.2 hn 1).mpr (Nat.one_le_iff_ne_zero.mpr h)
      simpa using this)
  else 0

/- English proof (translation)
Unfold `valF`. Rewrite using `[dif_pos hn]`. Both sides reduce to the same expression.
-/
theorem valF_apply {n : 𝓞 F} (hn : n ≠ 0) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    valF n 𝔭 = vF 𝔭.1 n := by
  unfold valF
  rw [dif_pos hn]
  rfl

def bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : Ideal (𝓞 F) := v.prod fun 𝔭 e => 𝔭.1 ^ e

/- English proof (translation)
Unfold `bId Finsupp.prod`. Rewrite using `[← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Conclude with `fun 𝔭 _ => pow_ne_zero _ (ne_bot_of_max 𝔭.2)`.
-/
theorem bId_ne_bot (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : bId v ≠ ⊥ := by
  unfold bId Finsupp.prod
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun 𝔭 _ => pow_ne_zero _ (ne_bot_of_max 𝔭.2)

/- English proof (translation)
Unfold `bId nrm Finsupp.prod`. Rewrite using `[map_prod]`. Use `push_cast`. Simplify using `only [map_pow, Nat.cast_pow]`.
-/
theorem absNorm_bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    (Ideal.absNorm (bId v) : ℝ) = nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  unfold bId nrm Finsupp.prod
  rw [map_prod]
  push_cast
  simp only [map_pow, Nat.cast_pow]

/- English proof (translation)
Unfold `bId Finsupp.prod`. Rewrite using `[← IsDedekindDomain.inf_pow_eq_prod_of_prime v.support (fun 𝔭 => 𝔭.1) v (fun 𝔭 _ => Ideal.prime_of_isPrime (ne_bot_of_max 𝔭.2) 𝔭.2.isPrime) (fun 𝔭 _ 𝔮 _ h => fun h' => h (Subtype.ext h')), Submodule.mem_finsetInf]`. Prove the components needed by the constructor for the conclusion. Introduce `h 𝔭`. Distinguish the cases in `h𝔭 : 𝔭 ∈ v.support`.

Rewrite using `[valF_apply hn]`. Conclude with `(mem_pow_iff_le_vF 𝔭.2 hn _).mp (h 𝔭 h𝔭)`. Rewrite using `[Finsupp.notMem_support_iff.mp h𝔭]`. Conclude with `Nat.zero_le _`. Introduce `h 𝔭 _`.

Use `h 𝔭` as an intermediate fact. Rewrite `this` using `[valF_apply hn]`. Conclude with `(mem_pow_iff_le_vF 𝔭.2 hn _).mpr this`.
-/
theorem mem_bId_iff {n : 𝓞 F} (hn : n ≠ 0) (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    n ∈ bId v ↔ v ≤ valF n := by
  unfold bId Finsupp.prod
  rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime v.support (fun 𝔭 => 𝔭.1) v
    (fun 𝔭 _ => Ideal.prime_of_isPrime (ne_bot_of_max 𝔭.2) 𝔭.2.isPrime)
    (fun 𝔭 _ 𝔮 _ h => fun h' => h (Subtype.ext h')), Submodule.mem_finsetInf]
  constructor
  · intro h 𝔭
    by_cases h𝔭 : 𝔭 ∈ v.support
    · rw [valF_apply hn]
      exact (mem_pow_iff_le_vF 𝔭.2 hn _).mp (h 𝔭 h𝔭)
    · rw [Finsupp.notMem_support_iff.mp h𝔭]; exact Nat.zero_le _
  · intro h 𝔭 _
    have := h 𝔭
    rw [valF_apply hn] at this
    exact (mem_pow_iff_le_vF 𝔭.2 hn _).mpr this

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hle : bId v ≤ 𝔭.1`. Establish `h1 : 𝔭.1 ≤ bId v ⊔ 𝔭.1` using `le_sup_right`. Establish `h2` using `𝔭.2.eq_of_le hne h1`. Rewrite using `[h2]`.

Conclude with `le_sup_left`. Unfold `bId Finsupp.prod at hle`. Take `⟨𝔮, h𝔮, hle'⟩` from `(Ideal.IsPrime.prod_le 𝔭.2.isPrime).mp hle`. Use `𝔭.2.isPrime` as an intermediate fact. Establish `h3 : 𝔮.1 ≤ 𝔭.1` using `Ideal.IsPrime.le_of_pow_le hle'`.

Establish `h4 : 𝔮.1 = 𝔭.1` using `𝔮.2.eq_of_le 𝔭.2.ne_top h3`. Conclude with `h𝔭 (Subtype.ext h4 ▸ h𝔮)`.
-/
theorem bId_sup_eq_top {v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ}
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ v.support) : bId v ⊔ 𝔭.1 = ⊤ := by
  by_contra hne
  have hle : bId v ≤ 𝔭.1 := by
    have h1 : 𝔭.1 ≤ bId v ⊔ 𝔭.1 := le_sup_right
    have h2 := 𝔭.2.eq_of_le hne h1
    rw [h2]
    exact le_sup_left
  unfold bId Finsupp.prod at hle
  obtain ⟨𝔮, h𝔮, hle'⟩ := (Ideal.IsPrime.prod_le 𝔭.2.isPrime).mp hle
  have := 𝔭.2.isPrime
  have h3 : 𝔮.1 ≤ 𝔭.1 := Ideal.IsPrime.le_of_pow_le hle'
  have h4 : 𝔮.1 = 𝔭.1 := 𝔮.2.eq_of_le 𝔭.2.ne_top h3
  exact h𝔭 (Subtype.ext h4 ▸ h𝔮)

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨n, hn, hn'⟩` from `SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot_of_max h𝔭) j)`. Establish `h0 : n ≠ 0` using `fun h => hn' (h ▸ Ideal.zero_mem _)`. Use `⟨n, h0, le_antisymm ?_ ((mem_pow_iff_le_vF h𝔭 h0 j).mp hn)⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Conclude with `hn' ((mem_pow_iff_le_vF h𝔭 h0 (j + 1)).mpr (by omega))`.
-/
theorem exists_vF_eq {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (j : ℕ) :
    ∃ n : 𝓞 F, n ≠ 0 ∧ vF 𝔭 n = j := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hn'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot_of_max h𝔭) j)
  have h0 : n ≠ 0 := fun h => hn' (h ▸ Ideal.zero_mem _)
  refine ⟨n, h0, le_antisymm ?_ ((mem_pow_iff_le_vF h𝔭 h0 j).mp hn)⟩
  by_contra hlt
  exact hn' ((mem_pow_iff_le_vF h𝔭 h0 (j + 1)).mpr (by omega))

end Formalism.HermitianLattices.Ext.L3.A5
