import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Qg2.near_of_adjoin :
    ∀ {P L : Type} [inst : CommRing P] [inst_1 : CommRing L]
    [inst_2 : Algebra P L] (G : Set L),
    (∀ g ∈ G, IsNilpotent g) →
      ∀ x ∈ Algebra.adjoin P G, ∃ (p : P), IsNilpotent (x - (Algebra.algebraMap P L : P → L) p) := by
  intro P L _ _ _ G hG x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, by simpa using hG y hy⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    have h := (Commute.all _ _).isNilpotent_add hp hq
    convert h using 1
    rw [map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p * q, ?_⟩
    rw [← mem_nilradical] at hp hq ⊢
    have h := (nilradical L).add_mem ((nilradical L).mul_mem_right z hp)
      ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)
    convert h using 1
    rw [map_mul]
    ring
