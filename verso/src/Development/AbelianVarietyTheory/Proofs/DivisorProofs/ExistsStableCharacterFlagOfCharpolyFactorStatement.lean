import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactor
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharFlag.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsStableCharacterFlagOfCharpolyFactor.lean&line=310#L310)
-/
theorem _root_.GlobalTheory.T.exists_stable_character_flag_of_charpoly_factor : ∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc := by
  first | exact @GlobalTheory.CharFlag.main | exact GlobalTheory.CharFlag.main | (intros; apply GlobalTheory.CharFlag.main <;> assumption)
