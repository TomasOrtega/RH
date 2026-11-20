import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPowReductionCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Establish `hprop : ∀ t, I ^ (n₀ + t + k) = Ideal.span {y} * I ^ (n₀ + t)`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simpa using h`. Consider the case `succ t ih`.

Rewrite using `[show n₀ + (t + 1) + k = n₀ + t + k + 1 by omega, pow_succ, ih, show n₀ + (t + 1) = n₀ + t + 1 by omega, pow_succ, mul_assoc]`. Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Rewrite using `[show n₀ + k * (s + 1) = n₀ + k * s + k by ring, hprop, ih, ← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← pow_succ']`.
-/
theorem pow_add_mul_eq_span_pow_mul {A : Type*} [CommRing A] {I : Ideal A} {k n₀ : ℕ} {y : A}
    (h : I ^ (n₀ + k) = Ideal.span {y} * I ^ n₀) (s : ℕ) :
    I ^ (n₀ + k * s) = Ideal.span {y ^ s} * I ^ n₀ := by
  have hprop : ∀ t, I ^ (n₀ + t + k) = Ideal.span {y} * I ^ (n₀ + t) := by
    intro t
    induction t with
    | zero => simpa using h
    | succ t ih =>
      rw [show n₀ + (t + 1) + k = n₀ + t + k + 1 by omega, pow_succ, ih,
        show n₀ + (t + 1) = n₀ + t + 1 by omega, pow_succ, mul_assoc]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show n₀ + k * (s + 1) = n₀ + k * s + k by ring, hprop, ih, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ']

/- English proof (translation)
Rewrite `hf`, the goal using `[Submodule.mem_div_iff_forall_mul_mem]`. Introduce `z hz`. Use `Submodule.mul_induction_on hz (fun p hp q hq => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `Submodule.mul_mem_mul (hf p hp) hq`.

Rewrite using `[mul_add]`. Conclude with `add_mem ha hb`.
-/
theorem mem_div_self_mul_of_mem_div_self {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    {P : Submodule A L} (Q : Submodule A L) {f : L} (hf : f ∈ P / P) : f ∈ (P * Q) / (P * Q) := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hf ⊢
  intro z hz
  refine Submodule.mul_induction_on hz (fun p hp q hq => ?_) (fun a b ha hb => ?_)
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (hf p hp) hq
  · rw [mul_add]
    exact add_mem ha hb

/- English proof (translation)
Introduce `A _ _ _ _ L _ _ hinj _hdim I hI`. Take `⟨k, hk, y, hy, n₀, hred⟩` from `h₂ A I (h₁ A _hdim I)`. Establish `hlin : Algebra.linearMap A L = (Algebra.ofId A L).toLinearMap` using `LinearMap.ext fun _ => rfl`. Establish `hmap : ∀ (J : Ideal A) (n : ℕ), (Submodule.map (Algebra.linearMap A L) J) ^ n = Submodule.map (Algebra.linearMap A L) (J ^ n)` using `fun J n => by`. Rewrite using `[hlin]`.

Conclude with `(Submodule.map_pow _ _ n).symm`. Use `set 𝓘 := Submodule.map (Algebra.linearMap A L) I with h𝓘`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Establish `: I ^ (n₀ + k) = ⊥`.

Rewrite using `[hred, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]`. Conclude with `pow_ne_zero _ hI this`. Establish `hy' : algebraMap A L y ≠ 0` using `fun h => hy0 (hinj (by rw [h, map_zero]))`. Establish `hkey : ∀ s, 𝓘 ^ (n₀ + k * s) = Submodule.span A {algebraMap A L y ^ s} * 𝓘 ^ n₀`. Introduce `s`.

Rewrite using `[h𝓘, hmap, hmap, pow_add_mul_eq_span_pow_mul hred s, hlin, Submodule.map_mul, ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton, AlgHom.toLinearMap_apply, map_pow, Algebra.ofId_apply]`. Establish `hle : ∀ n, 𝓘 ^ n / 𝓘 ^ n ≤ 𝓘 ^ n₀ / 𝓘 ^ n₀`. Introduce `n f hf`. Establish `hn : n ≤ n₀ + k * n` using `by nlinarith`. Establish `hf'` using `mem_div_self_mul_of_mem_div_self (𝓘 ^ (n₀ + k * n - n)) hf`.

Rewrite `hf'` using `[← pow_add, Nat.add_sub_cancel' hn, hkey]`. Rewrite `hf'`, the goal using `[Submodule.mem_div_iff_forall_mul_mem]`. Introduce `z hz`. Take `⟨w, hw, hweq⟩` from `Submodule.mem_span_singleton_mul.mp (hf' _ (Submodule.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩))`. Establish `: f * z = w`.

Apply `mul_left_cancel₀ (pow_ne_zero n hy')` to reduce the goal to its premises. Rewrite using `[hweq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hw`.

Take `⟨a, haI, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Use `set c := algebraMap A L (a ^ n₀) with hc`. Establish `hc0 : c ≠ 0` using `fun h => pow_ne_zero n₀ ha0 (hinj (by rw [← hc, h, map_zero]))`. Establish `hcI : c ∈ 𝓘 ^ n₀`. Rewrite using `[h𝓘, hmap]`.

Conclude with `Submodule.mem_map_of_mem (Ideal.pow_mem_pow haI n₀)`. Establish `hfg : (𝓘 ^ n₀).FG`. Rewrite using `[h𝓘, hmap]`. Conclude with `(IsNoetherian.noetherian (I ^ n₀)).map _`. Establish `hcol : (𝓘 ^ n₀ / 𝓘 ^ n₀).FG`.

Use `Submodule.fg_of_fg_map_injective (LinearMap.mulLeft A c) (fun x x' h => mul_left_cancel₀ hc0 h) (hfg.of_le ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Rewrite `hf` using `[SetLike.mem_coe, Submodule.mem_div_iff_forall_mul_mem]`. Rewrite using `[LinearMap.mulLeft_apply, mul_comm]`. Conclude with `hf c hcI`.

Conclude with `hcol.of_le (iSup_le hle)`.
-/
theorem BlowUpColonFinite.proof (h₁ : PowSpanFinrankBounded.Statement.{u})
    (h₂ : PrincipalReductionOfBoundedGens.Statement.{u}) : BlowUpColonFinite.Statement.{u} := by
  intro A _ _ _ _ L _ _ hinj _hdim I hI
  obtain ⟨k, hk, y, hy, n₀, hred⟩ := h₂ A I (h₁ A _hdim I)
  have hlin : Algebra.linearMap A L = (Algebra.ofId A L).toLinearMap := LinearMap.ext fun _ => rfl
  have hmap : ∀ (J : Ideal A) (n : ℕ), (Submodule.map (Algebra.linearMap A L) J) ^ n =
      Submodule.map (Algebra.linearMap A L) (J ^ n) := fun J n => by
    rw [hlin]; exact (Submodule.map_pow _ _ n).symm
  set 𝓘 := Submodule.map (Algebra.linearMap A L) I with h𝓘

  have hy0 : y ≠ 0 := by
    rintro rfl
    have : I ^ (n₀ + k) = ⊥ := by
      rw [hred, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]
    exact pow_ne_zero _ hI this
  have hy' : algebraMap A L y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))

  have hkey : ∀ s, 𝓘 ^ (n₀ + k * s) = Submodule.span A {algebraMap A L y ^ s} * 𝓘 ^ n₀ := by
    intro s
    rw [h𝓘, hmap, hmap, pow_add_mul_eq_span_pow_mul hred s, hlin, Submodule.map_mul,
      ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton,
      AlgHom.toLinearMap_apply, map_pow, Algebra.ofId_apply]

  have hle : ∀ n, 𝓘 ^ n / 𝓘 ^ n ≤ 𝓘 ^ n₀ / 𝓘 ^ n₀ := by
    intro n f hf
    have hn : n ≤ n₀ + k * n := by nlinarith
    have hf' := mem_div_self_mul_of_mem_div_self (𝓘 ^ (n₀ + k * n - n)) hf
    rw [← pow_add, Nat.add_sub_cancel' hn, hkey] at hf'
    rw [Submodule.mem_div_iff_forall_mul_mem] at hf' ⊢
    intro z hz
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_span_singleton_mul.mp
      (hf' _ (Submodule.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩))
    have : f * z = w := by
      apply mul_left_cancel₀ (pow_ne_zero n hy')
      rw [hweq]; ring
    rw [this]; exact hw

  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set c := algebraMap A L (a ^ n₀) with hc
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n₀ ha0 (hinj (by rw [← hc, h, map_zero]))
  have hcI : c ∈ 𝓘 ^ n₀ := by
    rw [h𝓘, hmap]; exact Submodule.mem_map_of_mem (Ideal.pow_mem_pow haI n₀)
  have hfg : (𝓘 ^ n₀).FG := by
    rw [h𝓘, hmap]; exact (IsNoetherian.noetherian (I ^ n₀)).map _
  have hcol : (𝓘 ^ n₀ / 𝓘 ^ n₀).FG := by
    refine Submodule.fg_of_fg_map_injective (LinearMap.mulLeft A c)
      (fun x x' h => mul_left_cancel₀ hc0 h) (hfg.of_le ?_)
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_div_iff_forall_mul_mem] at hf
    rw [LinearMap.mulLeft_apply, mul_comm]
    exact hf c hcI
  exact hcol.of_le (iSup_le hle)

end GroundTheory.Heights₂.Heights.NumbersDVR
