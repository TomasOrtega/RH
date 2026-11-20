import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Establish `hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x`. Introduce `m k hmk`. Proceed by induction on `k, hmk using Nat.le_induction with`. Consider the case `base => intro x _`. Both sides reduce to the same expression.

Consider the case `succ k hmk ih`. Introduce `x hx`. Rewrite using `[hcomp k x (hB hmk hx), ih x hx]`. Set `D' : S → M` to `fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0`. Establish `hD' : ∀ m, ∀ x ∈ B m, D' x = D m x`.

Introduce `m x hx`. Establish `h : ∃ m, x ∈ B m` using `⟨m, hx⟩`. Simplify using `only [D', dif_pos h]`. Conclude with `(hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm`. Establish `hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m` using `fun x hx => by`.

Use `hx` as an intermediate fact. Rewrite `this` using `[← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion]`. Conclude with `this`. Use `⟨D', ⟨?_, ?_, ?_⟩, hD'⟩` and prove the remaining obligations. Introduce `x hx y hy`.

Take `⟨m, hm⟩` from `hmem x hx`. Take `⟨n, hn⟩` from `hmem y hy`. Establish `hx' : x ∈ B (max m n)` using `hB (le_max_left m n) hm`. Establish `hy' : y ∈ B (max m n)` using `hB (le_max_right m n) hn`. Rewrite using `[hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']`.

Introduce `x hx y hy`. Take `⟨m, hm⟩` from `hmem x hx`. Take `⟨n, hn⟩` from `hmem y hy`. Establish `hx' : x ∈ B (max m n)` using `hB (le_max_left m n) hm`. Establish `hy' : y ∈ B (max m n)` using `hB (le_max_right m n) hn`.

Rewrite using `[hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']`. Introduce `a`. Rewrite using `[hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]`.
-/
theorem isDerOn_iSup_glue (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B : ℕ → Subalgebra A S) (hB : Monotone B) (D : ℕ → S → M)
    (hDer : ∀ m, IsDerOn (B m) (D m)) (hcomp : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) :
    ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  classical
  have hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro x _; rfl
    | succ k hmk ih =>
      intro x hx
      rw [hcomp k x (hB hmk hx), ih x hx]
  let D' : S → M := fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0
  have hD' : ∀ m, ∀ x ∈ B m, D' x = D m x := by
    intro m x hx
    have h : ∃ m, x ∈ B m := ⟨m, hx⟩
    simp only [D', dif_pos h]
    exact (hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm
  have hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m := fun x hx =>
    by
    have := hx
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion] at this
    exact this
  refine ⟨D', ⟨?_, ?_, ?_⟩, hD'⟩
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']
  · intro a
    rw [hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]

end GlobalTheory.AlmostEt
