import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.DenSum

variable {F : Type} [Field F] [NumberField F]

noncomputable def dI (b : F) : Ideal (𝓞 F) :=
  Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F b) (1 : Submodule (𝓞 F) F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem den_eq (b : F) : den b = Ideal.absNorm (dI b) := rfl

/- English proof (translation)
Simplify using `only [dI, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one, Algebra.smul_def]`.
-/
theorem mem_dI {b : F} {x : 𝓞 F} : x ∈ dI b ↔ ∃ t : 𝓞 F, (t : F) = (x : F) * b := by
  simp only [dI, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
    Algebra.smul_def]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_dI, mem_dI]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩`. Conclude with `⟨t - x * r, by push_cast; linear_combination ht⟩`.

Introduce and unpack `⟨t, ht⟩`. Conclude with `⟨t + x * r, by push_cast; linear_combination ht⟩`.
-/
theorem dI_add (b : F) (r : 𝓞 F) : dI (b + (r : F)) = dI b := by
  ext x
  rw [mem_dI, mem_dI]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t - x * r, by push_cast; linear_combination ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t + x * r, by push_cast; linear_combination ht⟩

/- English proof (translation)
Introduce `h`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 F)) b`. Establish `hmem : (s : 𝓞 F) ∈ dI b` using `mem_dI.mpr ⟨a, by rw [mul_comm]; exact hs.symm⟩`. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.coe_ne_zero s hmem`.
-/
theorem dI_ne_bot (b : F) : dI b ≠ ⊥ := by
  intro h
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) b
  have hmem : (s : 𝓞 F) ∈ dI b := mem_dI.mpr ⟨a, by rw [mul_comm]; exact hs.symm⟩
  rw [h, Ideal.mem_bot] at hmem
  exact nonZeroDivisors.coe_ne_zero s hmem

/- English proof (translation)
Take `⟨a, ha_def⟩ : ∃ a : ℕ, a = Ideal.absNorm I` from `⟨_, rfl⟩`. Establish `ha0 : a ≠ 0` using `by rw [ha_def, Ne, Ideal.absNorm_eq_zero_iff]; exact hI`. Establish `haI : (a : 𝓞 F) ∈ I` using `by rw [ha_def]; exact Ideal.absNorm_mem I`. Take `⟨C, hC⟩ : I ∣ Ideal.span {(a : 𝓞 F)}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr haI)`. Establish `hspan_ne : Ideal.span {(a : 𝓞 F)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `ha0` after adjusting the coercions. Establish `hC0 : C ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hC` using `[Ideal.mul_bot]`.

Conclude with `hspan_ne hC`. Establish `hex : ∀ b : {b : s // dI (b : F) = I}, ∃ t : 𝓞 F, (t : F) = (a : F) * ((b : s) : F)`. Introduce and unpack `⟨b, hb⟩`. Establish `hm : (a : 𝓞 F) ∈ dI (b : F)` using `by rw [hb]; exact haI`. Take `⟨t, ht⟩` from `mem_dI.mp hm`.

Conclude with `⟨t, by rw [ht]; push_cast; rfl⟩`. Use `choose t ht using hex`. Establish `htC : ∀ b, t b ∈ C`. Introduce `b`. Establish `hle : Ideal.span {t b} * I ≤ I * C`.

Rewrite using `[← hC, Ideal.span_singleton_mul_le_iff]`. Introduce `z hz`. Establish `hz' : z ∈ dI ((b : s) : F)` using `by rw [b.2]; exact hz`. Take `⟨u, hu⟩` from `mem_dI.mp hz'`. Rewrite using `[Ideal.mem_span_singleton']`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective (𝓞 F) F` to reduce the goal to its premises. Establish `hu' : algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F z * ((b : s) : F)` using `hu`. Establish `ht' : algebraMap (𝓞 F) F (t b) = (a : F) * ((b : s) : F)` using `ht b`. Rewrite using `[map_mul, map_mul, map_natCast, hu', ht']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdvd : I * C ∣ I * Ideal.span {t b}`. Rewrite using `[mul_comm I (Ideal.span _)]`. Conclude with `Ideal.dvd_iff_le.mpr hle`. Establish `h2` using `(mul_dvd_mul_iff_left hI).mp hdvd`.

Conclude with `(Ideal.span_singleton_le_iff_mem C).mp (Ideal.dvd_iff_le.mp h2)`. Set `H : AddSubgroup (𝓞 F)` to `(Ideal.span {((a * N : ℕ) : 𝓞 F)}).toAddSubgroup`. Set `K : AddSubgroup (𝓞 F)` to `C.toAddSubgroup`. Establish `haC : (a : 𝓞 F) ∈ C`. Establish `h1 : (a : 𝓞 F) ∈ I * C` using `by rw [← hC]; exact Ideal.mem_span_singleton_self _`.

Conclude with `(Ideal.mul_le_left : C * I ≤ C) (by rwa [mul_comm] at h1)`. Establish `hHK : H ≤ K`. Introduce `x hx`. Establish `hle : Ideal.span {((a * N : ℕ) : 𝓞 F)} ≤ C`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`.

Use `push_cast`. Conclude with `C.mul_mem_right _ haC`. Conclude with `hle hx`. Set `Φ : {b : s // dI (b : F) = I} → K ⧸ H.addSubgroupOf K` to `fun b => QuotientAddGroup.mk ⟨t b, htC b⟩`. Establish `hΦ : Function.Injective Φ`.

Introduce `b b' hbb`. Establish `hmem` using `QuotientAddGroup.eq.mp hbb`. Rewrite `hmem` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hr' : r * ((a * N : ℕ) : 𝓞 F) = -t b + t b'` using `by simpa using hr`.

Establish `h1` using `congrArg (algebraMap (𝓞 F) F) hr'`. Establish `htb : algebraMap (𝓞 F) F (t b) = (a : F) * ((b.1 : s) : F)` using `ht b`. Establish `htb' : algebraMap (𝓞 F) F (t b') = (a : F) * ((b'.1 : s) : F)` using `ht b'`. Simplify using `only [map_mul, map_add, map_neg, map_natCast, Nat.cast_mul, htb, htb'] at h1`. Establish `hrF : algebraMap (𝓞 F) F r = (r : F)` using `rfl`.

Rewrite `h1` using `[hrF]`. Establish `ha' : (a : F) ≠ 0` using `by exact_mod_cast ha0`. Establish `key : ((b'.1 : s) : F) - ((b.1 : s) : F) = (N : F) * (r : F)`. Apply `mul_left_cancel₀ ha'` to reduce the goal to its premises. Take the linear combination `-h1`.

Use `hs _ b'.1.2 _ b.1.2 ⟨r, key⟩` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext this.symm)`. Establish `hnormNat : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F)`. Introduce `m`. Rewrite using `[Ideal.absNorm_span_singleton]`.

Establish `hm : (m : 𝓞 F) = algebraMap ℤ (𝓞 F) (m : ℤ)` using `by simp`. Rewrite using `[hm, Algebra.norm_algebraMap]`. Simplify using `[Int.natAbs_pow]`. Establish `hrel : H.relIndex K = N ^ Module.finrank ℤ (𝓞 F) * a`. Establish `h1` using `AddSubgroup.relIndex_mul_index hHK`.

Establish `hKi : K.index = Ideal.absNorm C` using `by rw [Ideal.absNorm_apply]; rfl`. Establish `hHi : H.index = (a * N) ^ Module.finrank ℤ (𝓞 F)`. Establish `h3 : H.index = Ideal.absNorm (Ideal.span {((a * N : ℕ) : 𝓞 F)})` using `by rw [Ideal.absNorm_apply]; rfl`. Rewrite using `[h3, hnormNat]`. Establish `hmul : Ideal.absNorm (Ideal.span {(a : 𝓞 F)}) = a * Ideal.absNorm C` using `by rw [hC, map_mul, ha_def]`.

Establish `hC0' : Ideal.absNorm C ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Rewrite `h1` using `[hKi, hHi]`. Apply `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hC0')` to reduce the goal to its premises. Rewrite using `[h1, mul_pow, ← hnormNat a, hmul]`. Expand and normalize the polynomial expressions, which then agree.

Use `haveI hfinQ : Finite (K ⧸ H.addSubgroupOf K) := Nat.finite_of_card_ne_zero (by show H.relIndex K ≠ 0`. Rewrite using `[hrel]`. Conclude with `Nat.mul_ne_zero (pow_ne_zero _ hN.ne') ha0)`. Use `⟨Finite.of_injective Φ hΦ, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hrel, ha_def]`.
-/
theorem fibre_bound (N : ℕ) (hN : 0 < N) (s : Set F)
    (hs : ∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b')
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Finite {b : s // dI (b : F) = I} ∧
      Nat.card {b : s // dI (b : F) = I} ≤ N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
  classical
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = Ideal.absNorm I := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha_def, Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have haI : (a : 𝓞 F) ∈ I := by rw [ha_def]; exact Ideal.absNorm_mem I
  obtain ⟨C, hC⟩ : I ∣ Ideal.span {(a : 𝓞 F)} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr haI)
  have hspan_ne : Ideal.span {(a : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast ha0
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hC
    exact hspan_ne hC
  have hex : ∀ b : {b : s // dI (b : F) = I}, ∃ t : 𝓞 F, (t : F) = (a : F) * ((b : s) : F) := by
    rintro ⟨b, hb⟩
    have hm : (a : 𝓞 F) ∈ dI (b : F) := by rw [hb]; exact haI
    obtain ⟨t, ht⟩ := mem_dI.mp hm
    exact ⟨t, by rw [ht]; push_cast; rfl⟩
  choose t ht using hex
  have htC : ∀ b, t b ∈ C := by
    intro b
    have hle : Ideal.span {t b} * I ≤ I * C := by
      rw [← hC, Ideal.span_singleton_mul_le_iff]
      intro z hz
      have hz' : z ∈ dI ((b : s) : F) := by rw [b.2]; exact hz
      obtain ⟨u, hu⟩ := mem_dI.mp hz'
      rw [Ideal.mem_span_singleton']
      refine ⟨u, ?_⟩
      apply IsFractionRing.injective (𝓞 F) F
      have hu' : algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F z * ((b : s) : F) := hu
      have ht' : algebraMap (𝓞 F) F (t b) = (a : F) * ((b : s) : F) := ht b
      rw [map_mul, map_mul, map_natCast, hu', ht']
      ring
    have hdvd : I * C ∣ I * Ideal.span {t b} := by
      rw [mul_comm I (Ideal.span _)]
      exact Ideal.dvd_iff_le.mpr hle
    have h2 := (mul_dvd_mul_iff_left hI).mp hdvd
    exact (Ideal.span_singleton_le_iff_mem C).mp (Ideal.dvd_iff_le.mp h2)
  let H : AddSubgroup (𝓞 F) := (Ideal.span {((a * N : ℕ) : 𝓞 F)}).toAddSubgroup
  let K : AddSubgroup (𝓞 F) := C.toAddSubgroup
  have haC : (a : 𝓞 F) ∈ C := by
    have h1 : (a : 𝓞 F) ∈ I * C := by rw [← hC]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : C * I ≤ C) (by rwa [mul_comm] at h1)
  have hHK : H ≤ K := by
    intro x hx
    have hle : Ideal.span {((a * N : ℕ) : 𝓞 F)} ≤ C := by
      rw [Ideal.span_singleton_le_iff_mem]
      push_cast
      exact C.mul_mem_right _ haC
    exact hle hx
  let Φ : {b : s // dI (b : F) = I} → K ⧸ H.addSubgroupOf K := fun b => QuotientAddGroup.mk ⟨t b, htC b⟩
  have hΦ : Function.Injective Φ := by
    intro b b' hbb
    have hmem := QuotientAddGroup.eq.mp hbb
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hr' : r * ((a * N : ℕ) : 𝓞 F) = -t b + t b' := by simpa using hr
    have h1 := congrArg (algebraMap (𝓞 F) F) hr'
    have htb : algebraMap (𝓞 F) F (t b) = (a : F) * ((b.1 : s) : F) := ht b
    have htb' : algebraMap (𝓞 F) F (t b') = (a : F) * ((b'.1 : s) : F) := ht b'
    simp only [map_mul, map_add, map_neg, map_natCast, Nat.cast_mul, htb, htb'] at h1
    have hrF : algebraMap (𝓞 F) F r = (r : F) := rfl
    rw [hrF] at h1
    have ha' : (a : F) ≠ 0 := by exact_mod_cast ha0
    have key : ((b'.1 : s) : F) - ((b.1 : s) : F) = (N : F) * (r : F) := by
      apply mul_left_cancel₀ ha'
      linear_combination -h1
    have := hs _ b'.1.2 _ b.1.2 ⟨r, key⟩
    exact Subtype.ext (Subtype.ext this.symm)
  have hnormNat : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
    intro m
    rw [Ideal.absNorm_span_singleton]
    have hm : (m : 𝓞 F) = algebraMap ℤ (𝓞 F) (m : ℤ) := by simp
    rw [hm, Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  have hrel : H.relIndex K = N ^ Module.finrank ℤ (𝓞 F) * a := by
    have h1 := AddSubgroup.relIndex_mul_index hHK
    have hKi : K.index = Ideal.absNorm C := by rw [Ideal.absNorm_apply]; rfl
    have hHi : H.index = (a * N) ^ Module.finrank ℤ (𝓞 F) := by
      have h3 : H.index = Ideal.absNorm (Ideal.span {((a * N : ℕ) : 𝓞 F)}) := by rw [Ideal.absNorm_apply]; rfl
      rw [h3, hnormNat]
    have hmul : Ideal.absNorm (Ideal.span {(a : 𝓞 F)}) = a * Ideal.absNorm C := by rw [hC, map_mul, ha_def]
    have hC0' : Ideal.absNorm C ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [hKi, hHi] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hC0')
    rw [h1, mul_pow, ← hnormNat a, hmul]
    ring
  haveI hfinQ : Finite (K ⧸ H.addSubgroupOf K) := Nat.finite_of_card_ne_zero (by
    show H.relIndex K ≠ 0
    rw [hrel]
    exact Nat.mul_ne_zero (pow_ne_zero _ hN.ne') ha0)
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card {b : s // dI (b : F) = I} ≤ Nat.card (K ⧸ H.addSubgroupOf K) := Nat.card_le_card_of_injective Φ hΦ
    _ = N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
      show H.relIndex K = _
      rw [hrel, ha_def]

/- English proof (translation)
Introduce `F _ _ M hM N hN`. Use `⟨fun b r => by rw [den_eq, den_eq, dI_add], fun b => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[den_eq]`. Conclude with `Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dI_ne_bot b)`. Establish `hsum2` using `((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).1`.

Establish `hfin : ∀ I : Ideal (𝓞 F), Finite {b : s // dI (b : F) = I}`. Introduce `I`. Distinguish the cases in `hI : I = ⊥`. Substitute `hI haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩ infer_instance` using the available equality. Conclude with `(fibre_bound N hN s hs I hI).1`.

Set `f : s → ℝ` to `fun b => ((den (b : F) : ℝ) ^ M)⁻¹`. Use `show Summable f`. Rewrite using `[← (Equiv.sigmaFiberEquiv (fun b : s => dI (b : F))).summable_iff]`. Use `(summable_sigma_of_nonneg (fun _ => by simp only [Function.comp, f]; positivity)).mpr ⟨fun I => ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hfin I`.

Conclude with `Summable.of_finite`. Use `Summable.of_nonneg_of_le (fun I => tsum_nonneg (fun _ => by simp only [Function.comp, f]; positivity)) (fun I => ?_) (hsum2.mul_left ((N : ℝ) ^ Module.finrank ℤ (𝓞 F)))` and prove the remaining obligations. Distinguish the cases in `hI : I = ⊥`. Substitute `hI haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩` using the available equality. Rewrite using `[tsum_empty]`.

Check the signs of the components of the expression. Establish `hterm : ∀ y : {b : s // dI (b : F) = I}, (f ∘ ⇑(Equiv.sigmaFiberEquiv fun b : s => dI (b : F))) ⟨I, y⟩ = ((Ideal.absNorm I : ℝ) ^ M)⁻¹`. Introduce and unpack `⟨b, hb⟩`. Simplify using `[f, den_eq, hb]`. Rewrite using `[tsum_congr hterm, tsum_const, nsmul_eq_mul]`.

Establish `hc` using `(fibre_bound N hN s hs I hI).2`. Establish `hn1 : (1 : ℝ) ≤ Ideal.absNorm I`. Conclude with `Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Conclude with `hc` after adjusting the coercions.

Use `_ ≤ (N : ℝ) ^ Module.finrank ℤ (𝓞 F) * (Ideal.absNorm I : ℝ) ^ (-(2:ℝ)) := by`. Rewrite using `[Real.rpow_neg (by positivity), mul_assoc]`. Use `gcongr`. Rewrite using `[show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]`. Establish `ha : (0:ℝ) < Ideal.absNorm I` using `by linarith`.

Establish `hM1 : (Ideal.absNorm I : ℝ) ^ M = (Ideal.absNorm I : ℝ) * (Ideal.absNorm I : ℝ) ^ (M - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hM1, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]`.

Conclude with `inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 (by omega))`.
-/
theorem summable_den :
    ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  intro F _ _ M hM N hN
  refine ⟨fun b r => by rw [den_eq, den_eq, dI_add], fun b => ?_, fun s hs => ?_⟩
  · rw [den_eq]
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dI_ne_bot b)
  · have hsum2 := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).1
    have hfin : ∀ I : Ideal (𝓞 F), Finite {b : s // dI (b : F) = I} := by
      intro I
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        infer_instance
      · exact (fibre_bound N hN s hs I hI).1
    let f : s → ℝ := fun b => ((den (b : F) : ℝ) ^ M)⁻¹
    show Summable f
    rw [← (Equiv.sigmaFiberEquiv (fun b : s => dI (b : F))).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ => by simp only [Function.comp, f]; positivity)).mpr ⟨fun I => ?_, ?_⟩
    · haveI := hfin I
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le (fun I => tsum_nonneg (fun _ => by simp only [Function.comp, f]; positivity)) (fun I => ?_)
        (hsum2.mul_left ((N : ℝ) ^ Module.finrank ℤ (𝓞 F)))
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        rw [tsum_empty]
        positivity
      · have hterm : ∀ y : {b : s // dI (b : F) = I},
            (f ∘ ⇑(Equiv.sigmaFiberEquiv fun b : s => dI (b : F))) ⟨I, y⟩ = ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
          rintro ⟨b, hb⟩
          simp [f, den_eq, hb]
        rw [tsum_congr hterm, tsum_const, nsmul_eq_mul]
        have hc := (fibre_bound N hN s hs I hI).2
        have hn1 : (1 : ℝ) ≤ Ideal.absNorm I := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
        calc (Nat.card {b : s // dI (b : F) = I} : ℝ) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹
            ≤ ((N : ℝ) ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
              gcongr
              exact_mod_cast hc
          _ ≤ (N : ℝ) ^ Module.finrank ℤ (𝓞 F) * (Ideal.absNorm I : ℝ) ^ (-(2:ℝ)) := by
              rw [Real.rpow_neg (by positivity), mul_assoc]
              gcongr
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              have ha : (0:ℝ) < Ideal.absNorm I := by linarith
              have hM1 : (Ideal.absNorm I : ℝ) ^ M = (Ideal.absNorm I : ℝ) * (Ideal.absNorm I : ℝ) ^ (M - 1) := by
                rw [← pow_succ']
                congr 1
                omega
              rw [hM1, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
              exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 (by omega))

end GlobalTheory.CompanionTheory.SW.DenSum
