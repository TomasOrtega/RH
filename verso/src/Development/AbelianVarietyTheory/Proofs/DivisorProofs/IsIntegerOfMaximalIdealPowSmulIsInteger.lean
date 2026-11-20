import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Take `⟨hD, hI⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S`. Establish `hinj : Function.Injective (algebraMap S (FractionRing S))` using `IsFractionRing.injective S (FractionRing S)`. Distinguish the cases in `hA : ∀ a ∈ maximalIdeal S, ∃ y ∈ maximalIdeal S, algebraMap S (FractionRing S) y = a • c`. Set `N : Submodule S (FractionRing S)` to `Submodule.map (Algebra.linearMap S (FractionRing S)) (maximalIdeal S)`. Establish `hne : maximalIdeal S ≠ ⊥`.

Introduce `h`. Establish `hF : IsField S` using `(isField_iff_maximalIdeal_eq).2 h`. Use `ringKrullDim_eq_zero_of_isField hF` as an intermediate fact. Rewrite `hdim` using `[this]`. Conclude with `absurd hdim (by decide)`.

Establish `hN : N ≠ ⊥`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Establish `: Algebra.linearMap S (FractionRing S) x ∈ N` using `Submodule.mem_map_of_mem hx`. Rewrite `this` using `[h, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `hinj (by simpa using this)`. Establish `hFG : N.FG` using `Submodule.FG.map _ (IsNoetherian.noetherian _)`.

Establish `hint : IsIntegral S c`. Use `isIntegral_of_smul_mem_submodule N hN hFG c ?_` and prove the remaining obligations. Introduce `n hn`. Take `⟨a, ha, rfl⟩` from `Submodule.mem_map.1 hn`. Take `⟨y, hy, hy'⟩` from `hA a ha`.

Use `Submodule.mem_map.2 ⟨y, hy, ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.linearMap_apply, smul_eq_mul]`. Rewrite using `[hy', Algebra.smul_def, mul_comm]`. Conclude with `(IsIntegrallyClosed.isIntegral_iff).1 hint`. Use `exfalso push_neg at hA`.

Take `⟨a, ha, hy⟩` from `hA`. Take `⟨y, hy'⟩` from `hc a ha`. Establish `hyu : y ∉ maximalIdeal S` using `fun h => hy y h hy'`. Establish `hyunit : IsUnit y` using `by simpa [mem_maximalIdeal, mem_nonunits_iff] using hyu`. Establish `hspan : maximalIdeal S = Ideal.span {a}`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `b hb`. Take `⟨z, hz⟩` from `hc b hb`. Establish `key : b * y = a * z`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, hy', hz, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]`. Rewrite using `[Ideal.mem_span_singleton']`. Take `⟨u, rfl⟩` from `hyunit`. Use `⟨z * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Ideal.span_le]`. Simplify using `using ha`. Establish `h1 : (maximalIdeal S).spanFinrank ≤ 1`. Rewrite using `[hspan]`. Use `(Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `h2` using `ringKrullDim_le_spanFinrank_maximalIdeal S`. Establish `h3 : ringKrullDim S ≤ 1` using `h2.trans (by exact_mod_cast h1)`. Use `hdim.trans h3` as an intermediate fact. Conclude with `absurd this (by decide)`.
-/
theorem isInteger_of_maximalIdeal_smul_isInteger (S : Type) [CommRing S] [IsRegularLocalRing S]
    (hdim : 2 ≤ ringKrullDim S) (c : FractionRing S)
    (hc : ∀ a ∈ maximalIdeal S, IsLocalization.IsInteger S (a • c)) :
    IsLocalization.IsInteger S c := by
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have hinj : Function.Injective (algebraMap S (FractionRing S)) := IsFractionRing.injective S (FractionRing S)
  by_cases hA : ∀ a ∈ maximalIdeal S, ∃ y ∈ maximalIdeal S, algebraMap S (FractionRing S) y = a • c
  ·
    let N : Submodule S (FractionRing S) := Submodule.map (Algebra.linearMap S (FractionRing S)) (maximalIdeal S)
    have hne : maximalIdeal S ≠ ⊥ := by
      intro h
      have hF : IsField S := (isField_iff_maximalIdeal_eq).2 h
      have := ringKrullDim_eq_zero_of_isField hF
      rw [this] at hdim
      exact absurd hdim (by decide)
    have hN : N ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : Algebra.linearMap S (FractionRing S) x ∈ N := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by simpa using this)
    have hFG : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hint : IsIntegral S c := by
      refine isIntegral_of_smul_mem_submodule N hN hFG c ?_
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨y, hy, hy'⟩ := hA a ha
      refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hy', Algebra.smul_def, mul_comm]
    exact (IsIntegrallyClosed.isIntegral_iff).1 hint
  · exfalso
    push_neg at hA
    obtain ⟨a, ha, hy⟩ := hA
    obtain ⟨y, hy'⟩ := hc a ha
    have hyu : y ∉ maximalIdeal S := fun h => hy y h hy'
    have hyunit : IsUnit y := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hyu
    have hspan : maximalIdeal S = Ideal.span {a} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨z, hz⟩ := hc b hb
        have key : b * y = a * z := by
          apply hinj
          rw [map_mul, map_mul, hy', hz, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]
        rw [Ideal.mem_span_singleton']
        obtain ⟨u, rfl⟩ := hyunit
        refine ⟨z * ↑u⁻¹, ?_⟩
        calc z * ↑u⁻¹ * a = (a * z) * ↑u⁻¹ := by ring
          _ = (b * ↑u) * ↑u⁻¹ := by rw [key]
          _ = b := by simp [mul_assoc]
      · rw [Ideal.span_le]
        simpa using ha
    have h1 : (maximalIdeal S).spanFinrank ≤ 1 := by
      rw [hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans ?_
      simp
    have h2 := ringKrullDim_le_spanFinrank_maximalIdeal S
    have h3 : ringKrullDim S ≤ 1 := h2.trans (by exact_mod_cast h1)
    have := hdim.trans h3
    exact absurd this (by decide)

/- English proof (translation)
Introduce `S _ _ hdim k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `c hc`. Simplify using `using hc 1 (by simp)`.

Consider the case `succ k ih`. Introduce `c hc`. Apply `isInteger_of_maximalIdeal_smul_isInteger S hdim c` to reduce the goal to its premises. Introduce `a ha`. Apply `ih` to reduce the goal to its premises.

Introduce `b hb`. Rewrite using `[smul_smul]`. Apply `hc` to reduce the goal to its premises. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hb ha`.
-/
theorem isInteger_of_maximalIdeal_pow_smul_isInteger :
    ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S →
      ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k,
        IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  intro S _ _ hdim k
  induction k with
  | zero =>
    intro c hc
    simpa using hc 1 (by simp)
  | succ k ih =>
    intro c hc
    apply isInteger_of_maximalIdeal_smul_isInteger S hdim c
    intro a ha
    apply ih
    intro b hb
    rw [smul_smul]
    apply hc
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb ha

end GlobalTheory
