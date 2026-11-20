import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.DetBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Growth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsFurther
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.LteNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.NormVal

open UpperTheory.V UpperTheory.V.PropA

namespace UpperTheory.V.PropA

variable {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module ℤ_[l] X]

/- English proof (translation)
Establish `h1` using `(lteNorm l u c hu).2.1`. Establish `hd : (l : ℤ_[l]) ∣ u ^ e - 1` using `h1.trans (by simpa using sub_dvd_pow_sub_pow u 1 e)`. Conclude with `growth l X R _ hX (twist l X γ _ hd hγ) m`.
-/
theorem twLen_le_growth {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ) (hu : IsLevel l u c)
    (e m : ℕ) : twLen γ u e m ≤ twLen γ u e (jZero l R) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
  have h1 := (lteNorm l u c hu).2.1
  have hd : (l : ℤ_[l]) ∣ u ^ e - 1 := h1.trans (by simpa using sub_dvd_pow_sub_pow u 1 e)
  exact growth l X R _ hX (twist l X γ _ hd hγ) m

/- English proof (translation)
Take `⟨S, hS⟩` from `lift l X R (γ ^ l ^ j) hX`. Take `⟨s, hs⟩` from `detBound l u c hu j R S`. Use `⟨s, fun e => ?_⟩` and prove the remaining obligations. Establish `hpow : (u ^ e • γ) ^ l ^ j = (u ^ l ^ j) ^ e • γ ^ l ^ j`. Rewrite using `[smul_pow, ← pow_mul, ← pow_mul, mul_comm]`.

Use `show cokLen ((u ^ e • γ) ^ l ^ j - 1) ≤ _`. Rewrite using `[hpow]`. Conclude with `(hS _).trans (hs e)`.
-/
theorem exists_centres_level {R c : ℕ} (γ : Module.End ℤ_[l] X) {u : ℤ_[l]} (hX : GenBy l R X) (hu : IsLevel l u c) (j : ℕ) :
    ∃ s : Fin R → ℤ_[l], ∀ e : ℕ, twLen γ u e j ≤ ∑ i, (((j + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  obtain ⟨S, hS⟩ := lift l X R (γ ^ l ^ j) hX
  obtain ⟨s, hs⟩ := detBound l u c hu j R S
  refine ⟨s, fun e => ?_⟩
  have hpow : (u ^ e • γ) ^ l ^ j = (u ^ l ^ j) ^ e • γ ^ l ^ j := by
    rw [smul_pow, ← pow_mul, ← pow_mul, mul_comm]
  show cokLen ((u ^ e • γ) ^ l ^ j - 1) ≤ _
  rw [hpow]
  exact (hS _).trans (hs e)

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_centres_level γ hX hu (jZero l R)`. Use `⟨s, fun e m => ?_⟩` and prove the remaining obligations. Use `(twLen_le_growth hX hγ hu e m).trans ?_` and prove the remaining obligations. Establish `hm : max m (jZero l R) + c = (jZero l R + c) + (m - jZero l R)` using `by omega`. Establish `key : ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e)) = ∑ i, (((jZero l R + c : ℕ) : ℕ∞) + vl l (s i - e)) + ((R * (m - jZero l R) : ℕ) : ℕ∞)`.

Rewrite using `[hm]`. Simplify using `only [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Use `gcongr`.

Conclude with `hs e`.
-/
theorem exists_centres {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ) (hu : IsLevel l u c) :
    ∃ s : Fin R → ℤ_[l], ∀ e m : ℕ,
      twLen γ u e m ≤ ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  obtain ⟨s, hs⟩ := exists_centres_level γ hX hu (jZero l R)
  refine ⟨s, fun e m => ?_⟩
  refine (twLen_le_growth hX hγ hu e m).trans ?_
  have hm : max m (jZero l R) + c = (jZero l R + c) + (m - jZero l R) := by omega
  have key : ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e))
      = ∑ i, (((jZero l R + c : ℕ) : ℕ∞) + vl l (s i - e)) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
    rw [hm]
    simp only [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key]
  gcongr
  exact hs e

/- English proof (translation)
Establish `h' : ∏ _i : Fin 1, ((l : ℝ) ^ B)⁻¹ * ‖(1 : ℤ_[l])‖ ≤ ‖x‖`. Simplify `h` using `[zpow_neg, zpow_natCast]`. Use `normVal l 1 B x (fun _ => 1) h'` as an intermediate fact. Simplify `this` using `[vl]`.
-/
theorem vl_le_of_norm {x : ℤ_[l]} {B : ℕ} (h : (l : ℝ) ^ (-(B : ℤ)) ≤ ‖x‖) : vl l x ≤ B := by
  have h' : ∏ _i : Fin 1, ((l : ℝ) ^ B)⁻¹ * ‖(1 : ℤ_[l])‖ ≤ ‖x‖ := by
    simpa [zpow_neg, zpow_natCast] using h
  have := normVal l 1 B x (fun _ => 1) h'
  simpa [vl] using this

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_centres hX hγ hu`. Use `⟨s, fun e m B hB => (hs e m).trans ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_add _ B]`.

Use `gcongr`. Conclude with `vl_le_of_norm (hB i)`. Use `_ = _ := by`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]`.
-/
theorem exists_centres_norm {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ)
    (hu : IsLevel l u c) : ∃ s : Fin R → ℤ_[l], ∀ e m B : ℕ, (∀ i, (l : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - e‖) →
      twLen γ u e m ≤ ((R * (max m (jZero l R) + c + B) : ℕ) : ℕ∞) := by
  obtain ⟨s, hs⟩ := exists_centres hX hγ hu
  refine ⟨s, fun e m B hB => (hs e m).trans ?_⟩
  calc ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e))
        ≤ ∑ _i : Fin R, (((max m (jZero l R) + c + B : ℕ) : ℕ∞)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Nat.cast_add _ B]
          gcongr
          exact vl_le_of_norm (hB i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

end UpperTheory.V.PropA
