import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulLevelSubstPow

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

/- English proof (translation)
Take `⟨M, rfl⟩` from `hd`. Establish `hN : 0 < N` using `Nat.pos_of_mul_pos_right h`. Establish `hM : 0 < M` using `Nat.pos_of_mul_pos_left h`. Take `⟨a, ha, hpa⟩` from `hf`. Use `⟨spread M a, hasQ_mul_spread N M f a hN hM ha, fun n => ?_⟩` and prove the remaining obligations.

Unfold `spread`. Use `split_ifs`. Conclude with `hpa _`. Conclude with `h0`.
-/
theorem QAll.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {p : ℂ → Prop} {f : ℍ → ℂ}
    (h0 : p 0) (hf : QAll p N f) : QAll p N' f := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, hpa⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, fun n => ?_⟩
  unfold spread
  split_ifs
  · exact hpa _
  · exact h0

/- English proof (translation)
Take `⟨M, rfl⟩` from `hd`. Establish `hN : 0 < N` using `Nat.pos_of_mul_pos_right h`. Establish `hM : 0 < M` using `Nat.pos_of_mul_pos_left h`. Take `⟨a, ha, ha'⟩` from `hf`. Use `⟨spread M a, hasQ_mul_spread N M f a hN hM ha, ?_⟩` and prove the remaining obligations.

Establish `key : (fun n => g (spread M a n)) = spread M (fun n => g (a n))`. Use function extensionality and compare the values at `n`. Unfold `spread`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[key]`.

Conclude with `hasQ_mul_spread N M f' _ hN hM ha'`.
-/
theorem QConj.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {g : ℂ ≃+* ℂ} {f f' : ℍ → ℂ}
    (hf : QConj g N f f') : QConj g N' f f' := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, ha'⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, ?_⟩
  have key : (fun n => g (spread M a n)) = spread M (fun n => g (a n)) := by
    funext n
    unfold spread
    split_ifs <;> simp
  rw [key]
  exact hasQ_mul_spread N M f' _ hN hM ha'

end GlobalTheory.QFam
