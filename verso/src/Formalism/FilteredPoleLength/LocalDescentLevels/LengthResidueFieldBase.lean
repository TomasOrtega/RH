import Formalism.FilteredPoleLength.ReducedBasisBounds.FilteredPoleLength
import Formalism.FilteredPoleLength.LocalDescentLevels.ReductionQuotient

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

/- English proof (translation)
Introduce `O' Rr A _ _ _ _ _ _ _ _ _ _ x mm n F r h0 hn hF hinj hlen`. Establish `hpow : ∀ k, k < n → ∀ m : ℕ, ∀ a ∈ F k, x ^ m • a ∈ F (k + 1) → a ∈ F (k + 1)`. Introduce `k hk m`. Proceed by induction on `m with`. Consider the case `zero => intro a _ h`.

Simplify using `using h`. Consider the case `succ m ih`. Introduce `a ha h`. Use `ih a ha (hinj k hk _ ((F k).smul_mem _ ha) ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, ← pow_succ']` and apply the resulting hypothesis.

Establish `hstrict : ∀ k, k ≤ n → ∀ a : A, x ^ mm • a ∈ F k → a ∈ F k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _ a _`. Rewrite using `[h0]`.

Discharge the goal by the elementary cases of `trivial`. Consider the case `succ k ih`. Introduce `hk a h`. Conclude with `hpow k hk mm a (ih (by omega) a (hF k hk h)) h`. Use `set N : Submodule Rr A := (⊤ : Submodule Rr A).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A)) with hN`.

Establish `hcap : ∀ k, k ≤ n → N ⊓ F k = (F k).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))`. Introduce `k hk`. Use extensionality with `b`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, -, rfl⟩, hb⟩`.

Conclude with `⟨a, hstrict k hk a hb, rfl⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨⟨a, trivial, rfl⟩, (F k).smul_mem _ ha⟩`. Establish `hfl` using `filteredLength Rr A n (fun k => F (min k n)) (by simpa using h0) (by simpa using hn) (by`. Introduce `k`.

Break down `lt_or_ge k n with hk | hk` into its components or cases. Simplify `hF k hk` using `[min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk)]`. Simplify using `[min_eq_right hk, min_eq_right (hk.trans (Nat.le_succ k))]) N`. Establish `hsum : Module.length Rr (A ⧸ N) = (((∑ k ∈ Finset.range n, r k) * mm : ℕ) : ℕ∞)`. Rewrite using `[hfl, Finset.sum_mul, Nat.cast_sum]`.

Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k < n` using `Finset.mem_range.mp hk`. Rewrite using `[min_eq_left hk'.le, min_eq_left (Nat.succ_le_of_lt hk'), hcap k hk'.le]`. Conclude with `hlen k hk'`. Rewrite using `[IsLocalRing.length_restrictScalars O' Rr (A ⧸ N), hsum]`.
-/
theorem filteredPoleLength : FilteredPoleLength := by
  intro O' Rr A _ _ _ _ _ _ _ _ _ _ x mm n F r h0 hn hF hinj hlen

  have hpow : ∀ k, k < n → ∀ m : ℕ, ∀ a ∈ F k, x ^ m • a ∈ F (k + 1) → a ∈ F (k + 1) := by
    intro k hk m
    induction m with
    | zero => intro a _ h; simpa using h
    | succ m ih =>
      intro a ha h
      refine ih a ha (hinj k hk _ ((F k).smul_mem _ ha) ?_)
      rwa [smul_smul, ← pow_succ']

  have hstrict : ∀ k, k ≤ n → ∀ a : A, x ^ mm • a ∈ F k → a ∈ F k := by
    intro k
    induction k with
    | zero => intro _ a _; rw [h0]; trivial
    | succ k ih =>
      intro hk a h
      exact hpow k hk mm a (ih (by omega) a (hF k hk h)) h
  set N : Submodule Rr A := (⊤ : Submodule Rr A).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))
    with hN
  have hcap : ∀ k, k ≤ n → N ⊓ F k = (F k).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A)) := by
    intro k hk
    ext b
    constructor
    · rintro ⟨⟨a, -, rfl⟩, hb⟩
      exact ⟨a, hstrict k hk a hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, trivial, rfl⟩, (F k).smul_mem _ ha⟩

  have hfl := filteredLength Rr A n (fun k => F (min k n)) (by simpa using h0) (by simpa using hn)
    (by
      intro k
      rcases lt_or_ge k n with hk | hk
      · simpa [min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk)] using hF k hk
      · simp [min_eq_right hk, min_eq_right (hk.trans (Nat.le_succ k))]) N
  have hsum : Module.length Rr (A ⧸ N) = (((∑ k ∈ Finset.range n, r k) * mm : ℕ) : ℕ∞) := by
    rw [hfl, Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    rw [min_eq_left hk'.le, min_eq_left (Nat.succ_le_of_lt hk'), hcap k hk'.le]
    exact hlen k hk'
  rw [IsLocalRing.length_restrictScalars O' Rr (A ⧸ N), hsum]

end Formalism.LatticeBaseChangeAlt
