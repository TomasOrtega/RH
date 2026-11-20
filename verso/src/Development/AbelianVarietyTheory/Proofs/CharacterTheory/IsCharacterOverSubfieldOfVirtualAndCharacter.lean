import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterExtendScalarsRep
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymmStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharactersStatement
open GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Take `⟨n, ρ, _, hρ⟩` from `hφ`. Conclude with `⟨n, ρ, hρ⟩`.
-/
private theorem isChar_of_isIrrChar (K L : Type) [Field K] [Field L]
    [Algebra K L] {G : Type} [Group G] (φ : G → L) (hφ : _root_.GlobalTheory.BI.IsIrrChar K L φ) :
    _root_.GlobalTheory.BI.IsChar K L φ := by
  obtain ⟨n, ρ, _, hρ⟩ := hφ
  exact ⟨n, ρ, hρ⟩

/- English proof (translation)
Take `⟨a, b, ha, hb, hab⟩` from `(_root_.GlobalTheory.BI.mem_virt_iff_sub K L G χ).1 hv`. Take `⟨hadd, hnat, hpos, -⟩` from `_root_.GlobalTheory.BI.pair_add_nat_pos_symm K L G`. Take `⟨-, hnatL, -, -⟩` from `_root_.GlobalTheory.BI.pair_add_nat_pos_symm L L G`. Establish `key : ∀ c : G → L, _root_.GlobalTheory.BI.IsChar K L c → ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a = χ + c → _root_.GlobalTheory.BI.IsChar K L χ`. Use `_root_.GlobalTheory.BI.isChar_induction K L G _ ?_ ?_` and prove the remaining obligations.

Introduce `a ha h`. Rewrite `h` using `[add_zero]`. Conclude with `h ▸ ha`. Introduce `φ c hφ hc ih a ha h`. Establish `hφc` using `isChar_of_isIrrChar K L φ hφ`.

Take `⟨n₁, h₁⟩` from `hnatL χ φ hχ (_root_.GlobalTheory.BI.isChar_baseChange K L G φ hφc)`. Take `⟨n₂, hn₂, h₂⟩` from `hpos φ hφ`. Take `⟨n₃, h₃⟩` from `hnat c φ hc hφc`. Establish `hne : _root_.GlobalTheory.BI.pair a φ ≠ 0`. Rewrite using `[h, hadd, hadd, h₁, h₂, h₃]`.

Conclude with `(by omega : n₁ + (n₂ + n₃) ≠ 0)` after adjusting the coercions. Take `⟨a', ha', ha'eq⟩` from `_root_.GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero K L G φ a hφ ha hne`. Use `ih a' ha' ?_` and prove the remaining obligations. Establish `: φ + a' = φ + (χ + c)`. Rewrite using `[← ha'eq, h]`.

Normalize the expressions using the abelian group laws. Conclude with `add_left_cancel this`. Conclude with `key b hb a ha (by rw [hab]; abel)`.
-/
theorem _root_.GlobalTheory.BI.isChar_of_isChar_of_mem_virt (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (χ : G → L) (hχ : _root_.GlobalTheory.BI.IsChar L L χ) (hv : χ ∈ _root_.GlobalTheory.BI.Virt K L G) :
    _root_.GlobalTheory.BI.IsChar K L χ := by
  obtain ⟨a, b, ha, hb, hab⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub K L G χ).1 hv
  obtain ⟨hadd, hnat, hpos, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm K L G
  obtain ⟨-, hnatL, -, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm L L G
  have key : ∀ c : G → L, _root_.GlobalTheory.BI.IsChar K L c →
      ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a = χ + c → _root_.GlobalTheory.BI.IsChar K L χ := by
    refine _root_.GlobalTheory.BI.isChar_induction K L G _ ?_ ?_
    · intro a ha h
      rw [add_zero] at h
      exact h ▸ ha
    · intro φ c hφ hc ih a ha h
      have hφc := isChar_of_isIrrChar K L φ hφ
      obtain ⟨n₁, h₁⟩ := hnatL χ φ hχ (_root_.GlobalTheory.BI.isChar_baseChange K L G φ hφc)
      obtain ⟨n₂, hn₂, h₂⟩ := hpos φ hφ
      obtain ⟨n₃, h₃⟩ := hnat c φ hc hφc
      have hne : _root_.GlobalTheory.BI.pair a φ ≠ 0 := by
        rw [h, hadd, hadd, h₁, h₂, h₃]
        exact_mod_cast (by omega : n₁ + (n₂ + n₃) ≠ 0)
      obtain ⟨a', ha', ha'eq⟩ := _root_.GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero K L G φ a hφ ha hne
      refine ih a' ha' ?_
      have : φ + a' = φ + (χ + c) := by
        rw [← ha'eq, h]
        abel
      exact add_left_cancel this
  exact key b hb a ha (by rw [hab]; abel)

end GlobalTheory.BI
