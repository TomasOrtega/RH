import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigC

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey

/- English proof (translation)
Introduce `C _ _ V hAlg hc O _ n d hd0 K v`. Establish `hd : d ≠ 0` using `NeZero.ne d`. Establish `hq2 : 2 ≤ V.l ^ d` using `le_trans V.l_prime.two_le (Nat.le_self_pow hd _)`. Take `⟨m, w, hsum, hw⟩` from `hJ C hAlg n (V.l ^ d) hq2 {τ | τ ∈ Acl K ∧ τ ^ V.l ^ d = τ} (fun _ ht => ht.2) (fun _ hs _ ht => comm_mem K hs.1 ht.1) (Matrix.mulVec K.P v)`. Use `set w' : Fin m → Fin n → C := fun j => Matrix.mulVec K.P (w j) with hw'`.

Establish `hPq : K.P ^ V.l ^ d = K.P`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero (pow_ne_zero d V.l_prime.ne_zero)`. Rewrite using `[hk]`. Use `clear hk`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ih, P_idem]`. Establish `hw'e : ∀ j, ∀ τ ∈ Acl K, τ ^ V.l ^ d = τ → ∃ c : C, Matrix.mulVec τ (w' j) = c • w' j`. Introduce `j τ hτ hτq`. Take `⟨c, hc'⟩` from `hw j τ ⟨hτ, hτq⟩`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hw', Matrix.mulVec_mulVec, comm_mem K hτ (P_mem K), ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]`. Establish `hPw' : ∀ j, Matrix.mulVec K.P (w' j) = w' j` using `fun j => by`. Rewrite using `[hw', Matrix.mulVec_mulVec, P_idem]`. Establish `hρ : ∀ j x, ∃ σ : C, Matrix.mulVec (K.ρ x) (w' j) = σ • w' j`.

Introduce `j x`. Take `⟨σ, hσ⟩` from `scal K hT hc hd (S_mem K x) (w' j) (hw'e j)`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hPw' j, Matrix.mulVec_mulVec, ← P_comm, hPw' j]`. Conclude with `hσ`.

Establish `hχ : ∀ j, ∃ χ : O →+* C, ∀ x, Matrix.mulVec (K.ρ x) (w' j) = χ x • w' j`. Introduce `j`. Distinguish the cases in `h0 : w' j = 0`. Conclude with `⟨K.em 0, fun x => by rw [h0, Matrix.mulVec_zero, smul_zero]⟩`. Use `choose σ hσ using hρ j`.

Establish `uniq : ∀ a b : C, a • w' j = b • w' j → a = b` using `fun a b h => smul_left_injective C h0 h`. Use `⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσ⟩` and prove the remaining obligations. Conclude with `uniq _ _ (by rw [← hσ 1, map_one, Matrix.one_mulVec, one_smul])`. Introduce `x y`. Use `uniq _ _ ?_` and prove the remaining obligations.

Rewrite using `[← hσ (x * y), map_mul, ← Matrix.mulVec_mulVec, hσ y, Matrix.mulVec_smul, hσ x, smul_smul, mul_comm]`. Conclude with `uniq _ _ (by rw [← hσ 0, map_zero, Matrix.zero_mulVec, zero_smul])`. Introduce `x y`. Use `uniq _ _ ?_` and prove the remaining obligations. Rewrite using `[← hσ (x + y), map_add, Matrix.add_mulVec, hσ x, hσ y, add_smul]`.

Use `choose χ hχ using hχ`. Use `⟨m, w', χ, ?_, fun j => ⟨hPw' j, hχ j⟩⟩` and prove the remaining obligations. Rewrite using `[hw', ← Matrix.mulVec_sum, ← hsum, Matrix.mulVec_mulVec, P_idem]`.
-/
theorem keyEig_of (hT : TeichSt) (hJ : JointEigSt) : KeyEigSt := by
  intro C _ _ V hAlg hc O _ n d hd0 K v
  have hd : d ≠ 0 := NeZero.ne d
  have hq2 : 2 ≤ V.l ^ d := le_trans V.l_prime.two_le (Nat.le_self_pow hd _)
  obtain ⟨m, w, hsum, hw⟩ := hJ C hAlg n (V.l ^ d) hq2 {τ | τ ∈ Acl K ∧ τ ^ V.l ^ d = τ}
    (fun _ ht => ht.2) (fun _ hs _ ht => comm_mem K hs.1 ht.1) (Matrix.mulVec K.P v)
  set w' : Fin m → Fin n → C := fun j => Matrix.mulVec K.P (w j) with hw'
  have hPq : K.P ^ V.l ^ d = K.P := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero d V.l_prime.ne_zero)
    rw [hk]
    clear hk
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, P_idem]

  have hw'e : ∀ j, ∀ τ ∈ Acl K, τ ^ V.l ^ d = τ → ∃ c : C, Matrix.mulVec τ (w' j) = c • w' j := by
    intro j τ hτ hτq
    obtain ⟨c, hc'⟩ := hw j τ ⟨hτ, hτq⟩
    refine ⟨c, ?_⟩
    rw [hw', Matrix.mulVec_mulVec, comm_mem K hτ (P_mem K), ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]
  have hPw' : ∀ j, Matrix.mulVec K.P (w' j) = w' j := fun j => by
    rw [hw', Matrix.mulVec_mulVec, P_idem]
  have hρ : ∀ j x, ∃ σ : C, Matrix.mulVec (K.ρ x) (w' j) = σ • w' j := by
    intro j x
    obtain ⟨σ, hσ⟩ := scal K hT hc hd (S_mem K x) (w' j) (hw'e j)
    refine ⟨σ, ?_⟩
    rw [← hPw' j, Matrix.mulVec_mulVec, ← P_comm, hPw' j]
    exact hσ
  have hχ : ∀ j, ∃ χ : O →+* C, ∀ x, Matrix.mulVec (K.ρ x) (w' j) = χ x • w' j := by
    intro j
    by_cases h0 : w' j = 0
    · exact ⟨K.em 0, fun x => by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    choose σ hσ using hρ j
    have uniq : ∀ a b : C, a • w' j = b • w' j → a = b := fun a b h => smul_left_injective C h0 h
    refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσ⟩
    · exact uniq _ _ (by rw [← hσ 1, map_one, Matrix.one_mulVec, one_smul])
    · intro x y
      refine uniq _ _ ?_
      rw [← hσ (x * y), map_mul, ← Matrix.mulVec_mulVec, hσ y, Matrix.mulVec_smul, hσ x, smul_smul, mul_comm]
    · exact uniq _ _ (by rw [← hσ 0, map_zero, Matrix.zero_mulVec, zero_smul])
    · intro x y
      refine uniq _ _ ?_
      rw [← hσ (x + y), map_add, Matrix.add_mulVec, hσ x, hσ y, add_smul]
  choose χ hχ using hχ
  refine ⟨m, w', χ, ?_, fun j => ⟨hPw' j, hχ j⟩⟩
  rw [hw', ← Matrix.mulVec_sum, ← hsum, Matrix.mulVec_mulVec, P_idem]

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
