import Mathlib

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `r p hp hpr W h`. Establish `hs : ∀ (j k : Fin r) (v : Fin r → ℂ), (Matrix.single j k (1 : ℂ)).mulVec v = v k • (Pi.single j (1 : ℂ) : Fin r → ℂ)`. Introduce `j k v`. Use extensionality with `i`. Rewrite using `[Matrix.single_mulVec]`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hi]`. Establish `key : ∀ (j k : Fin r) (v : Fin r → ℂ), v k ≠ 0 → (Matrix.single j k (1 : ℂ)).mulVec v ∈ W → (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W`.

Introduce `j k v hv hm`. Rewrite `hm` using `[hs]`. Conclude with `(W.smul_mem_iff hv).1 hm`. Establish `up : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v k ≠ 0 → (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W` using `fun j k v hj hk hv hvk => key j k v hvk (h j k hj hk v hv).1`. Establish `down : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v j ≠ 0 → (Pi.single k (1 : ℂ) : Fin r → ℂ) ∈ W` using `fun j k v hj hk hv hvj => key k j v hvj (h j k hj hk v hv).2`.

Distinguish the cases in `hW : W = ⊥`. Conclude with `Or.inl hW`. Use `right`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hv0`.

Establish `hk' : v k ≠ 0` using `hk`. Set `a : Fin r` to `⟨0, by omega⟩`. Set `b : Fin r` to `⟨p, hpr⟩`. Establish `ha : (a : ℕ) < p` using `hp`. Establish `hb : p ≤ (b : ℕ)` using `le_rfl`.

Establish `hbW : (Pi.single b (1 : ℂ) : Fin r → ℂ) ∈ W`. Break down `lt_or_ge (k : ℕ) p with hkp | hkp` into its components or cases. Conclude with `down k b v hkp hb hv hk'`. Conclude with `down a b _ ha hb (up a k v ha hkp hv hk') (by simp)`. Establish `haW : (Pi.single a (1 : ℂ) : Fin r → ℂ) ∈ W` using `up a b _ ha hb hbW (by simp)`.

Establish `hall : ∀ i : Fin r, (Pi.single i (1 : ℂ) : Fin r → ℂ) ∈ W`. Introduce `i`. Break down `lt_or_ge (i : ℕ) p with hi | hi` into its components or cases. Conclude with `up i b _ hi hb hbW (by simp)`. Conclude with `down a i _ ha hi haW (by simp)`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin r → ℂ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Rewrite using `[hx]`. Conclude with `W.sum_mem fun i _ => W.smul_mem _ (hall i)`.
-/
theorem offDiagonal_matrixUnits_irreducible :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ),
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
        (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) := by
  intro r p hp hpr W h
  have hs : ∀ (j k : Fin r) (v : Fin r → ℂ),
      (Matrix.single j k (1 : ℂ)).mulVec v = v k • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j k v
    ext i
    rw [Matrix.single_mulVec]
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have key : ∀ (j k : Fin r) (v : Fin r → ℂ), v k ≠ 0 →
      (Matrix.single j k (1 : ℂ)).mulVec v ∈ W → (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro j k v hv hm
    rw [hs] at hm
    exact (W.smul_mem_iff hv).1 hm
  have up : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v k ≠ 0 →
      (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvk => key j k v hvk (h j k hj hk v hv).1
  have down : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v j ≠ 0 →
      (Pi.single k (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvj => key k j v hvj (h j k hj hk v hv).2
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : v k ≠ 0 := hk
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨p, hpr⟩
  have ha : (a : ℕ) < p := hp
  have hb : p ≤ (b : ℕ) := le_rfl
  have hbW : (Pi.single b (1 : ℂ) : Fin r → ℂ) ∈ W := by
    rcases lt_or_ge (k : ℕ) p with hkp | hkp
    · exact down k b v hkp hb hv hk'
    · exact down a b _ ha hb (up a k v ha hkp hv hk') (by simp)
  have haW : (Pi.single a (1 : ℂ) : Fin r → ℂ) ∈ W := up a b _ ha hb hbW (by simp)
  have hall : ∀ i : Fin r, (Pi.single i (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro i
    rcases lt_or_ge (i : ℕ) p with hi | hi
    · exact up i b _ hi hb hbW (by simp)
    · exact down a i _ ha hi haW (by simp)
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

end GlobalTheory
