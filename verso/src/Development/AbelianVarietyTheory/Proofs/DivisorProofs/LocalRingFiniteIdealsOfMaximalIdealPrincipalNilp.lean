import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory

/- English proof (translation)
Introduce `S _ _ hprin hnil`. Take `⟨x, hx⟩` from `hprin.principal`. Take `⟨M, hM⟩` from `hnil`. Use `set m := IsLocalRing.maximalIdeal S with hm`. Establish `hM' : m ^ M = ⊥` using `hM`.

Establish `hpow : ∀ n : ℕ, m ^ n = Ideal.span {x ^ n}`. Introduce `n`. Rewrite using `[hx]`. Conclude with `Ideal.span_singleton_pow x n`. Apply `((Set.finite_Iic M).image fun n => m ^ n).subset` to reduce the goal to its premises.

Introduce `I _`. Distinguish the cases in `hI : I = ⊥`. Conclude with `⟨M, Set.mem_Iic.mpr le_rfl, by simp only [hM', hI]⟩`. Establish `hnot : ¬ I ≤ m ^ M`. Rewrite using `[hM']`.

Conclude with `fun h => hI (le_bot_iff.mp h)`. Establish `hex : ∃ k, ¬ I ≤ m ^ k` using `⟨M, hnot⟩`. Establish `hk` using `Nat.find_spec hex`. Establish `hkM : Nat.find hex ≤ M` using `Nat.find_min' hex hnot`. Establish `hk0 : Nat.find hex ≠ 0`.

Introduce `h`. Apply `hk` to reduce the goal to its premises. Rewrite using `[h, pow_zero]`. Rewrite using `[Ideal.one_eq_top]`. Conclude with `le_top`.

Take `⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1` from `Nat.exists_eq_succ_of_ne_zero hk0`. Establish `hIn : I ≤ m ^ n`. Assume the negation of the conclusion as `h`. Conclude with `Nat.find_min hex (show n < Nat.find hex by omega) h`. Rewrite `hk` using `[hn]`.

Take `⟨a, haI, ha⟩` from `SetLike.not_le_iff_exists.mp hk`. Establish `ha' : a ∈ m ^ n` using `hIn haI`. Rewrite `ha'` using `[hpow, Ideal.mem_span_singleton']`. Take `⟨y, rfl⟩` from `ha'`. Establish `hy : IsUnit y`.

Assume the negation of the conclusion as `hy`. Apply `ha` to reduce the goal to its premises. Establish `hym : y ∈ m` using `(IsLocalRing.mem_maximalIdeal y).mpr hy`. Rewrite `hym` using `[hx, Ideal.mem_span_singleton']`. Take `⟨z, rfl⟩` from `hym`.

Rewrite using `[hpow, Ideal.mem_span_singleton']`. Conclude with `⟨z, by ring⟩`. Use `⟨n, Set.mem_Iic.mpr (by omega), ?_⟩` and prove the remaining obligations. Use `show m ^ n = I`. Apply `le_antisymm _ hIn` to reduce the goal to its premises.

Rewrite using `[hpow, Ideal.span_le, Set.singleton_subset_iff]`. Use `I.mul_mem_left ((hy.unit⁻¹ : Sˣ) : S) haI` as an intermediate fact. Rewrite `this` using `[← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul]`. Then use the resulting hypothesis.
-/
theorem localRing_finite_ideals_of_maximalIdeal_principal_nilpotent :
    ∀ (S : Type) [CommRing S] [IsLocalRing S], (IsLocalRing.maximalIdeal S).IsPrincipal →
    IsNilpotent (IsLocalRing.maximalIdeal S) → (Set.univ : Set (Ideal S)).Finite := by
  intro S _ _ hprin hnil
  classical
  obtain ⟨x, hx⟩ := hprin.principal
  obtain ⟨M, hM⟩ := hnil
  set m := IsLocalRing.maximalIdeal S with hm
  have hM' : m ^ M = ⊥ := hM
  have hpow : ∀ n : ℕ, m ^ n = Ideal.span {x ^ n} := by
    intro n
    rw [hx]
    exact Ideal.span_singleton_pow x n
  apply ((Set.finite_Iic M).image fun n => m ^ n).subset
  intro I _
  by_cases hI : I = ⊥
  · exact ⟨M, Set.mem_Iic.mpr le_rfl, by simp only [hM', hI]⟩
  · have hnot : ¬ I ≤ m ^ M := by
      rw [hM']; exact fun h => hI (le_bot_iff.mp h)
    have hex : ∃ k, ¬ I ≤ m ^ k := ⟨M, hnot⟩
    have hk := Nat.find_spec hex
    have hkM : Nat.find hex ≤ M := Nat.find_min' hex hnot
    have hk0 : Nat.find hex ≠ 0 := by
      intro h; apply hk; rw [h, pow_zero]; rw [Ideal.one_eq_top]; exact le_top
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hIn : I ≤ m ^ n := by
      by_contra h
      exact Nat.find_min hex (show n < Nat.find hex by omega) h
    rw [hn] at hk
    obtain ⟨a, haI, ha⟩ := SetLike.not_le_iff_exists.mp hk
    have ha' : a ∈ m ^ n := hIn haI
    rw [hpow, Ideal.mem_span_singleton'] at ha'
    obtain ⟨y, rfl⟩ := ha'
    have hy : IsUnit y := by
      by_contra hy
      apply ha
      have hym : y ∈ m := (IsLocalRing.mem_maximalIdeal y).mpr hy
      rw [hx, Ideal.mem_span_singleton'] at hym
      obtain ⟨z, rfl⟩ := hym
      rw [hpow, Ideal.mem_span_singleton']
      exact ⟨z, by ring⟩
    refine ⟨n, Set.mem_Iic.mpr (by omega), ?_⟩
    show m ^ n = I
    apply le_antisymm _ hIn
    rw [hpow, Ideal.span_le, Set.singleton_subset_iff]
    have := I.mul_mem_left ((hy.unit⁻¹ : Sˣ) : S) haI
    rwa [← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul] at this

end GlobalTheory
