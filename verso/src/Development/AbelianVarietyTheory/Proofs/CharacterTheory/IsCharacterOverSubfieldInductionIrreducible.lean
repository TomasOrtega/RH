import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAddStatement
open GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Introduce `K L _ _ _ _ _ G _ _ Q h0 hstep`. Establish `hchar : ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → ∃ n : ℕ, a 1 = n`. Introduce `a ha`. Unfold `_root_.GlobalTheory.BI.IsChar at ha`. Take `⟨n, ρ, hρ⟩` from `ha`.

Conclude with `⟨n, by rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩`. Establish `hirr : ∀ φ : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ → ∃ m : ℕ, 0 < m ∧ φ 1 = m`. Introduce `φ hφ`. Unfold `_root_.GlobalTheory.BI.IsIrrChar at hφ`. Take `⟨m, ρ, hρirr, hρ⟩` from `hφ`.

Use `⟨m, Nat.pos_of_ne_zero fun hm => ?_, by` and prove the remaining obligations. Rewrite using `[hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩`. Substitute `hm` using the available equality. Establish `hs : IsSimpleOrder (Subrepresentation ρ)` using `hρirr`. Take `⟨x, y, hxy⟩` from `hs.toNontrivial.exists_pair_ne`.

Apply `hxy` to reduce the goal to its premises. Use extensionality with `v`. Rewrite using `[Subsingleton.elim v 0]`. Conclude with `⟨fun _ => y.toSubmodule.zero_mem, fun _ => x.toSubmodule.zero_mem⟩`. Establish `key : ∀ n : ℕ, ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a 1 = n → Q a`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `a ha ha1`. Distinguish the cases in `hz : a = 0`.

Rewrite using `[hz]`. Conclude with `h0`. Take `⟨φ, c, hφ, hc, rfl⟩` from `_root_.GlobalTheory.BI.exists_irrChar_add K L G a ha hz`. Take `⟨m, hm, hφ1⟩` from `hirr φ hφ`. Take `⟨k, hk1⟩` from `hchar c hc`.

Establish `hn : n = m + k`. Establish `hsum : ((m + k : ℕ) : L) = n`. Rewrite using `[Nat.cast_add, ← hφ1, ← hk1]`. Conclude with `ha1`. Conclude with `hsum.symm` after adjusting the coercions.

Conclude with `hstep φ c hφ hc (ih k (by omega) c hc hk1)`. Introduce `a ha`. Take `⟨n, hn⟩` from `hchar a ha`. Conclude with `key n a ha hn`.
-/
theorem _root_.GlobalTheory.BI.isChar_induction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G]
      [Finite G] (Q : (G → L) → Prop), Q 0 →
      (∀ φ c : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ → _root_.GlobalTheory.BI.IsChar K L c →
        Q c → Q (φ + c)) → ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → Q a := by
  intro K L _ _ _ _ _ G _ _ Q h0 hstep
  have hchar : ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → ∃ n : ℕ, a 1 = n := by
    intro a ha
    unfold _root_.GlobalTheory.BI.IsChar at ha
    obtain ⟨n, ρ, hρ⟩ := ha
    exact ⟨n, by rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
  have hirr : ∀ φ : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ →
      ∃ m : ℕ, 0 < m ∧ φ 1 = m := by
    intro φ hφ
    unfold _root_.GlobalTheory.BI.IsIrrChar at hφ
    obtain ⟨m, ρ, hρirr, hρ⟩ := hφ
    refine ⟨m, Nat.pos_of_ne_zero fun hm => ?_, by
      rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
    subst hm
    have hs : IsSimpleOrder (Subrepresentation ρ) := hρirr
    obtain ⟨x, y, hxy⟩ := hs.toNontrivial.exists_pair_ne
    apply hxy
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => y.toSubmodule.zero_mem, fun _ => x.toSubmodule.zero_mem⟩
  have key : ∀ n : ℕ, ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a 1 = n → Q a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha ha1
      by_cases hz : a = 0
      · rw [hz]; exact h0
      obtain ⟨φ, c, hφ, hc, rfl⟩ := _root_.GlobalTheory.BI.exists_irrChar_add K L G a ha hz
      obtain ⟨m, hm, hφ1⟩ := hirr φ hφ
      obtain ⟨k, hk1⟩ := hchar c hc
      have hn : n = m + k := by
        have hsum : ((m + k : ℕ) : L) = n := by
          rw [Nat.cast_add, ← hφ1, ← hk1]
          exact ha1
        exact_mod_cast hsum.symm
      exact hstep φ c hφ hc (ih k (by omega) c hc hk1)
  intro a ha
  obtain ⟨n, hn⟩ := hchar a ha
  exact key n a ha hn

end GlobalTheory.BI
