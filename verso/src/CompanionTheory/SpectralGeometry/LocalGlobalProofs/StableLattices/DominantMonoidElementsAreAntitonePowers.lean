import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

/- English proof (translation)
Introduce `j k hjk`. Establish `hjk' : (j : ℕ) ≤ (k : ℕ)` using `hjk`. Unfold `tExp`. Distinguish the cases in `h : (i : ℕ) = n + 1`. Simplify using `[h]`.

Simplify using `only [h, if_false]`. Distinguish the cases in `hk : (k : ℕ) < i`. Establish `hj : (j : ℕ) < i` using `lt_of_le_of_lt hjk' hk`. Simplify using `[hj, hk]`. Apply the tactic sequence `by_cases hj : (j : ℕ) < i <;> simp [hj, hk]`.
-/
theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `⟨tExp n i, tExp_antitone n i, rfl⟩`. Consider the case `one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, ha.add hb, (dPow_add p a b).symm⟩`.
-/
theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
