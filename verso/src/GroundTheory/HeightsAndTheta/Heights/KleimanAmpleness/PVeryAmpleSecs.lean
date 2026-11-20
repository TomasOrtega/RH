import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSecsSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace VeryAmpleSecs

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs j hj`. Establish `hsj` using `(Submodule.mem_iInf _).mp hs (singleChart hj)`. Take `⟨b, hb⟩` from `Submodule.mem_span_singleton.mp (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hsj)`. Rewrite `hb` using `[chartRing_smul_def]`.

Rewrite using `[← hb, mul_div_cancel_right₀ _ (pow_ne_zero n hj)]`. Conclude with `mem_ampleBase_of_mem_chartRing hj b.2`. Introduce `H`. Rewrite using `[SubSystem.secs, Submodule.mem_iInf]`. Introduce `I`.

Take `⟨i, hi⟩` from `I.2.1`. Establish `hhi : h i ≠ 0` using `(mem_support h).mp (I.2.2 hi)`. Establish `hbase : ampleBase (S` using `k) h i ≤ chartRing k h (singleChart hhi) := by`. Rewrite using `[ampleBase, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Conclude with `(ratio (S := k) hhi l).2`. Establish `hmem : s / h i ^ n ∈ chartRing k h I` using `chartRing_mono (Finset.singleton_subset_iff.mpr hi) (hbase (H i hhi))`. Rewrite using `[Submodule.restrictScalars_mem, SubSystem.pow_sub]`. Establish `hs : s = (⟨s / h i ^ n, hmem⟩ : chartRing k h I) • h i ^ n`. Rewrite using `[chartRing_smul_def, div_mul_cancel₀ _ (pow_ne_zero n hhi)]`.

Rewrite using `[hs]`. Conclude with `Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (mem_twistMod_one I i) n)`.
-/
theorem mem_secs_pow_twistSys_one_iff {r : ℕ} (h : Fin (r + 1) → Ω) (n : ℕ) (s : Ω) :
    s ∈ ((twistSys k h 1).pow n).secs ↔ ∀ j, h j ≠ 0 → s / h j ^ n ∈ ampleBase (S := k) h j := by
  constructor
  · intro hs j hj
    have hsj := (Submodule.mem_iInf _).mp hs (singleChart hj)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hsj)
    rw [chartRing_smul_def] at hb
    rw [← hb, mul_div_cancel_right₀ _ (pow_ne_zero n hj)]
    exact mem_ampleBase_of_mem_chartRing hj b.2
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hhi : h i ≠ 0 := (mem_support h).mp (I.2.2 hi)
    have hbase : ampleBase (S := k) h i ≤ chartRing k h (singleChart hhi) := by
      rw [ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      exact (ratio (S := k) hhi l).2
    have hmem : s / h i ^ n ∈ chartRing k h I :=
      chartRing_mono (Finset.singleton_subset_iff.mpr hi) (hbase (H i hhi))
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    have hs : s = (⟨s / h i ^ n, hmem⟩ : chartRing k h I) • h i ^ n := by
      rw [chartRing_smul_def, div_mul_cancel₀ _ (pow_ne_zero n hhi)]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (mem_twistMod_one I i) n)

/- English proof (translation)
Use `set C : Ideal A := (L ^ n).colon {s}`. Establish `key : ∀ j, ∀ q ∈ Q, ∀ a : A, algebraMap A Ω a = h j * q → a ∈ C.radical`. Introduce `j q hq a ha`. Take `⟨e, he⟩` from `hs j`. Use `⟨e, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha]`. Establish `hm` using `Submodule.mul_mem_mul (Submodule.pow_mem_pow Q hq e) he`. Establish `hQL : Q ^ e * L ^ (n + e) = L ^ n`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hm` using `[hQL]`.

Use `hm using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (1 : Submodule A Ω) ≤ Submodule.map (Algebra.linearMap A Ω) (C.radical : Submodule A A)`. Rewrite using `[← hLQ, ← hL, ← Submodule.span_eq Q, Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, q, hq, rfl⟩`.

Establish `hjq : h j * q ∈ L * Q` using `Submodule.mul_mem_mul (hL ▸ Submodule.subset_span ⟨j, rfl⟩) hq`. Rewrite `hjq` using `[hLQ, Submodule.mem_one]`. Take `⟨a, ha⟩` from `hjq`. Conclude with `⟨a, key j q hq a ha, ha⟩`. Take `⟨a, ⟨m, hm⟩, ha1⟩` from `h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)`.

Establish `ha1' : algebraMap A Ω a = 1` using `ha1`. Rewrite `hm` using `[Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha1', one_pow, one_mul]`. Conclude with `hm`.
-/
theorem mem_pow_of_pow_mul_mem {A : Type*} [CommRing A] [Algebra A Ω] {L Q : Submodule A Ω}
    (hLQ : L * Q = 1) {r : ℕ} {h : Fin (r + 1) → Ω} (hL : Submodule.span A (Set.range h) = L)
    {s : Ω} {n : ℕ} (hs : ∀ j, ∃ e, h j ^ e * s ∈ L ^ (n + e)) : s ∈ L ^ n := by
  set C : Ideal A := (L ^ n).colon {s}
  have key : ∀ j, ∀ q ∈ Q, ∀ a : A, algebraMap A Ω a = h j * q → a ∈ C.radical := by
    intro j q hq a ha
    obtain ⟨e, he⟩ := hs j
    refine ⟨e, ?_⟩
    rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha]
    have hm := Submodule.mul_mem_mul (Submodule.pow_mem_pow Q hq e) he
    have hQL : Q ^ e * L ^ (n + e) = L ^ n := by
      calc Q ^ e * L ^ (n + e) = L ^ n * (L * Q) ^ e := by ring
        _ = L ^ n := by rw [hLQ, one_pow, mul_one]
    rw [hQL] at hm
    convert hm using 1
    ring
  have h1 : (1 : Submodule A Ω) ≤ Submodule.map (Algebra.linearMap A Ω) (C.radical : Submodule A A) := by
    rw [← hLQ, ← hL, ← Submodule.span_eq Q, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, q, hq, rfl⟩
    have hjq : h j * q ∈ L * Q := Submodule.mul_mem_mul (hL ▸ Submodule.subset_span ⟨j, rfl⟩) hq
    rw [hLQ, Submodule.mem_one] at hjq
    obtain ⟨a, ha⟩ := hjq
    exact ⟨a, key j q hq a ha, ha⟩
  obtain ⟨a, ⟨m, hm⟩, ha1⟩ := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have ha1' : algebraMap A Ω a = 1 := ha1
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha1', one_pow, one_mul] at hm
  exact hm

/- English proof (translation)
Proceed by induction on `ht using Algebra.adjoin_induction with`. Consider the case `mem t ht`. Take `⟨l, rfl⟩` from `ht`. Conclude with `⟨1, by rw [pow_one, pow_one, mul_div_cancel₀ _ hj]; exact hL l⟩`. Consider the case `algebraMap c`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, pow_zero, one_mul, Submodule.mem_one]`. Conclude with `⟨⟨_, Subalgebra.algebraMap_mem A c⟩, rfl⟩`. Consider the case `add t₁ t₂ _ _ h₁ h₂`. Take `⟨e₁, he₁⟩` from `h₁`.

Take `⟨e₂, he₂⟩` from `h₂`. Use `⟨e₁ + e₂, ?_⟩` and prove the remaining obligations. Establish `hs : h j ^ (e₁ + e₂) * (t₁ + t₂) = h j ^ e₂ * (h j ^ e₁ * t₁) + h j ^ e₁ * (h j ^ e₂ * t₂)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, pow_add]`.

Conclude with `Submodule.add_mem _ (by rw [mul_comm (L ^ e₁)]; exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₁) (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₂)`. Consider the case `mul t₁ t₂ _ _ h₁ h₂`. Take `⟨e₁, he₁⟩` from `h₁`. Take `⟨e₂, he₂⟩` from `h₂`. Use `⟨e₁ + e₂, ?_⟩` and prove the remaining obligations.

Establish `hs : h j ^ (e₁ + e₂) * (t₁ * t₂) = (h j ^ e₁ * t₁) * (h j ^ e₂ * t₂)` using `by ring`. Rewrite using `[hs, pow_add]`. Conclude with `Submodule.mul_mem_mul he₁ he₂`.
-/
theorem exists_pow_mul_mem_pow {A : Subalgebra k Ω} {L : Submodule A Ω} {r : ℕ}
    {h : Fin (r + 1) → Ω} (hL : ∀ l, h l ∈ L) {j : Fin (r + 1)} (hj : h j ≠ 0) {t : Ω}
    (ht : t ∈ ampleBase (S := k) h j) : ∃ e, h j ^ e * t ∈ L ^ e := by
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨l, rfl⟩ := ht
    exact ⟨1, by rw [pow_one, pow_one, mul_div_cancel₀ _ hj]; exact hL l⟩
  | algebraMap c =>
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_zero, one_mul, Submodule.mem_one]
    exact ⟨⟨_, Subalgebra.algebraMap_mem A c⟩, rfl⟩
  | add t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ + t₂) = h j ^ e₂ * (h j ^ e₁ * t₁) + h j ^ e₁ * (h j ^ e₂ * t₂) := by
      ring
    rw [hs, pow_add]
    exact Submodule.add_mem _
      (by rw [mul_comm (L ^ e₁)]; exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₁)
      (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₂)
  | mul t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ * t₂) = (h j ^ e₁ * t₁) * (h j ^ e₂ * t₂) := by ring
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul he₁ he₂

end VeryAmpleSecs

open VeryAmpleSecs in

/- English proof (translation)
Introduce `k _ Ω _ _ N x Nb r h hv n`. Use extensionality with `s`. Rewrite using `[mem_secs_pow_twistSys_one_iff]`. Establish `hL : ∀ I l, h l ∈ Nb.sub I` using `fun I l => (Submodule.mem_iInf _).mp (hv.mem_secs l) I`. Prove the components needed by the constructor for the conclusion.

Introduce `hs j hj`. Use `hv.closed j hj (Set.mem_iInter.mpr fun I => ⟨n, ?_⟩)` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀ _ (pow_ne_zero n hj), one_mul]`. Conclude with `(Submodule.mem_iInf _).mp hs I`. Introduce `H`.

Rewrite using `[SubSystem.secs, Submodule.mem_iInf]`. Introduce `I`. Rewrite using `[Submodule.restrictScalars_mem, SubSystem.pow_sub]`. Take `⟨Q, hQ⟩` from `Nb.invertible I`. Use `mem_pow_of_pow_mul_mem hQ (hv.generates I) fun j => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : h j = 0`. Conclude with `⟨1, by rw [hj, pow_one, zero_mul]; exact Submodule.zero_mem _⟩`. Take `⟨e, he⟩` from `exists_pow_mul_mem_pow (hL I) hj (H j hj)`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `hs : h j ^ e * s = h j ^ n * (h j ^ e * (s / h j ^ n))`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hs, pow_add]`. Conclude with `Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL I j) n) he`.
-/
theorem VeryAmpleSecs.proof : VeryAmpleSecs.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hv n
  ext s
  rw [mem_secs_pow_twistSys_one_iff]
  have hL : ∀ I l, h l ∈ Nb.sub I := fun I l => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  constructor
  · intro hs j hj
    refine hv.closed j hj (Set.mem_iInter.mpr fun I => ⟨n, ?_⟩)
    rw [div_mul_cancel₀ _ (pow_ne_zero n hj), one_mul]
    exact (Submodule.mem_iInf _).mp hs I
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    obtain ⟨Q, hQ⟩ := Nb.invertible I
    refine mem_pow_of_pow_mul_mem hQ (hv.generates I) fun j => ?_
    by_cases hj : h j = 0
    · exact ⟨1, by rw [hj, pow_one, zero_mul]; exact Submodule.zero_mem _⟩
    obtain ⟨e, he⟩ := exists_pow_mul_mem_pow (hL I) hj (H j hj)
    refine ⟨e, ?_⟩
    have hs : h j ^ e * s = h j ^ n * (h j ^ e * (s / h j ^ n)) := by
      field_simp
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL I j) n) he

end

end GroundTheory.Heights₂.Heights.Kleiman
