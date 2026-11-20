import Mathlib

namespace GlobalTheory.Published

def primesInProgression (a q : ℕ) : Set ℕ := {p | p.Prime ∧ p ≡ a [MOD q]}

noncomputable def leastPrimeMod (a q : ℕ) : ℕ := sInf (primesInProgression a q)

def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem exists_prime_modEq_of_coprime (a q : ℕ) (hq : 1 ≤ q) (h : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] := by
  haveI : NeZero q := ⟨by omega⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 h
  obtain ⟨p, -, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  exact ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

A detailed English derivation is pending.
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
