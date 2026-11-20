import Mathlib

namespace GlobalTheory.Published

def primesInProgression (a q : ℕ) : Set ℕ := {p | p.Prime ∧ p ≡ a [MOD q]}

noncomputable def leastPrimeMod (a q : ℕ) : ℕ := sInf (primesInProgression a q)

def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L

/- English proof (translation)
Use `haveI : NeZero q := ⟨by omega⟩`. Establish `hu : IsUnit (a : ZMod q)` using `(ZMod.isUnit_iff_coprime a q).2 h`. Take `⟨p, -, hp, hpa⟩` from `Nat.forall_exists_prime_gt_and_eq_mod hu 0`. Conclude with `⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa⟩`.
-/
private theorem exists_prime_modEq_of_coprime (a q : ℕ) (hq : 1 ≤ q) (h : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] := by
  haveI : NeZero q := ⟨by omega⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 h
  obtain ⟨p, -, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  exact ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨C, L, hC, hL, hb⟩`. Use `⟨C, L, hC, hL, fun a q ha hq h => ?_⟩` and prove the remaining obligations. Establish `hne : (_root_.GlobalTheory.Published.primesInProgression a q).Nonempty` using `exists_prime_modEq_of_coprime a q hq h`. Establish `hmem` using `Nat.sInf_mem hne`.

Conclude with `⟨_, hmem.1, hmem.2, hb a q ha hq h⟩`. Introduce and unpack `⟨C, L, hC, hL, hb⟩`. Use `⟨C, L, hC, hL, fun a q ha hq h => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, hpa, hpC⟩` from `hb a q ha hq h`. Establish `hle : _root_.GlobalTheory.Published.leastPrimeMod a q ≤ p` using `Nat.sInf_le ⟨hp, hpa⟩`.

Conclude with `le_trans (by exact_mod_cast hle) hpC`.
-/
theorem _root_.GlobalTheory.Published.linnik_iff_exists_prime : _root_.GlobalTheory.Published.Linnik ↔
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ L := by
  constructor
  · rintro ⟨C, L, hC, hL, hb⟩
    refine ⟨C, L, hC, hL, fun a q ha hq h => ?_⟩
    have hne : (_root_.GlobalTheory.Published.primesInProgression a q).Nonempty :=
      exists_prime_modEq_of_coprime a q hq h
    have hmem := Nat.sInf_mem hne
    exact ⟨_, hmem.1, hmem.2, hb a q ha hq h⟩
  · rintro ⟨C, L, hC, hL, hb⟩
    refine ⟨C, L, hC, hL, fun a q ha hq h => ?_⟩
    obtain ⟨p, hp, hpa, hpC⟩ := hb a q ha hq h
    have hle : _root_.GlobalTheory.Published.leastPrimeMod a q ≤ p := Nat.sInf_le ⟨hp, hpa⟩
    exact le_trans (by exact_mod_cast hle) hpC

end GlobalTheory.Published
