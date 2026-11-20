import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩`. Consider the case `cons j l ih`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[List.foldr_cons, h j (by simp), ih.1 (fun i hi => h i (by simp [hi]))]`.

Both sides reduce to the same expression. Rewrite using `[List.foldr_cons]`. Distinguish the cases in `hl : ∀ i ∈ l, α i = 0`. Rewrite using `[ih.1 hl]`. Establish `hj : α j ≠ 0`.

Introduce `hj`. Apply `h` to reduce the goal to its premises. Introduce `i hi`. Break down `List.mem_cons.1 hi with rfl | hi` into its components or cases. Conclude with `hj`.

Conclude with `hl i hi`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hj`. Rewrite using `[hk, Function.iterate_succ_apply, hc j]`. Conclude with `Function.iterate_fixed (h0 j) k`. Rewrite using `[ih.2 hl]`.

Conclude with `Function.iterate_fixed (h0 j) _`.
-/
theorem foldr_iterate_of_kills {A ι : Type} [Zero A] (ds : ι → A → A) (α : ι → ℕ) (c : A)
    (hc : ∀ i, ds i c = 0) (h0 : ∀ i, ds i 0 = 0) (l : List ι) :
    ((∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = c) ∧
    (¬ (∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = 0) := by
  induction l with
  | nil => exact ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩
  | cons j l ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [List.foldr_cons, h j (by simp), ih.1 (fun i hi => h i (by simp [hi]))]
      rfl
    · rw [List.foldr_cons]
      by_cases hl : ∀ i ∈ l, α i = 0
      · rw [ih.1 hl]
        have hj : α j ≠ 0 := by
          intro hj
          apply h
          intro i hi
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hj
          · exact hl i hi
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [hk, Function.iterate_succ_apply, hc j]
        exact Function.iterate_fixed (h0 j) k
      · rw [ih.2 hl]
        exact Function.iterate_fixed (h0 j) _

/- English proof (translation)
Introduce `A B _ _ _ n ev ds c hc`. Use extensionality with `α`. Rewrite using `[MvPowerSeries.coeff_C]`. Express the relevant statement in the definitionally equal form `(∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) α c) = _`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[iterOp_zero]`. Simplify using the standard rewrite rules. Establish `: iterOp (fun i => ⇑(ds i)) α c = 0`. Use `(foldr_iterate_of_kills (fun i => ⇑(ds i)) α c hc (fun i => map_zero _) _).2 ?_` and prove the remaining obligations.

Introduce `h'`. Apply `h` to reduce the goal to its premises. Use extensionality with `i`. Conclude with `h' i (List.mem_finRange i)`. Rewrite using `[this, map_zero, smul_zero]`.
-/
theorem taylor_const :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  intro A B _ _ _ n ev ds c hc
  ext α
  rw [MvPowerSeries.coeff_C]
  change (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) α c) = _
  split_ifs with h
  · subst h
    rw [iterOp_zero]
    simp
  · have : iterOp (fun i => ⇑(ds i)) α c = 0 := by
      refine (foldr_iterate_of_kills (fun i => ⇑(ds i)) α c hc (fun i => map_zero _) _).2 ?_
      intro h'
      apply h
      ext i
      exact h' i (List.mem_finRange i)
    rw [this, map_zero, smul_zero]

end GlobalTheory.FormalOrigin
