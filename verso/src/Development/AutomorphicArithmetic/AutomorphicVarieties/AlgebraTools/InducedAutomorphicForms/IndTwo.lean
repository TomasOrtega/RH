import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IsIrreducibleIff

open UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R G n _ _ _ _ H s hH hs r`. Choose the witnesses or unpack the hypotheses as in `⟨r0, hin, hout⟩ : ∃ r0 : G → Matrix n n R, (∀ h : H, r0 h = (r h : Matrix n n R)) ∧ ∀ g, g ∉ H → r0 g = 0 := by`. Use `⟨fun g => if h : g ∈ H then (r ⟨g, h⟩ : Matrix n n R) else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Simplify using `only [dif_pos h.2]`.

Introduce `g hg`. Simplify using `only [dif_neg hg]`. Establish `hs' : s⁻¹ ∉ H` using `fun h => hs (by simpa using h)`. Establish `hm : ∀ a b : G, a * b ∈ H ↔ (a ∈ H ↔ b ∈ H)` using `fun a b => Subgroup.mul_mem_iff_of_index_two hH`. Establish `hmul : ∀ a b : G, a ∈ H → b ∈ H → r0 (a * b) = r0 a * r0 b`.

Introduce `a b ha hb`. Establish `h1` using `hin ⟨a, ha⟩`. Establish `h2` using `hin ⟨b, hb⟩`. Establish `h3` using `hin (⟨a, ha⟩ * ⟨b, hb⟩)`. Rewrite `h3` using `[map_mul, Units.val_mul, ← h1, ← h2]`.

Conclude with `h3`. Establish `hone : r0 1 = 1`. Use `hin 1` as an intermediate fact. Rewrite `this` using `[map_one]`. Simplify using `using this`.

Establish `key : ∀ a b : G, r0 (a * b) = r0 a * r0 b + r0 (a * s) * r0 (s⁻¹ * b)`. Introduce `a b`. Apply the tactic sequence `by_cases ha : a ∈ H <;> by_cases hb : b ∈ H`. Rewrite using `[hmul a b ha hb, hout (a * s) (by rw [hm]; tauto), zero_mul, add_zero]`. Rewrite using `[hout (a * b) (by rw [hm]; tauto), hout b hb, hout (a * s) (by rw [hm]; tauto)]`.

Simplify using the standard rewrite rules. Rewrite using `[hout (a * b) (by rw [hm]; tauto), hout a ha, hout (s⁻¹ * b) (by rw [hm]; tauto)]`. Simplify using the standard rewrite rules. Rewrite using `[hout a ha, zero_mul, zero_add, ← hmul _ _ (by rw [hm]; tauto) (by rw [hm]; tauto)]`. Use `congr 1`.

Use `group`. Set `M : G →* Matrix (n ⊕ n) (n ⊕ n) R` to `{ toFun := fun g => Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s)) map_one' := by`. Rewrite using `[one_mul, mul_one, inv_mul_cancel, hone, hout s hs, hout _ hs', Matrix.fromBlocks_one]`. Use the proof step `map_mul' := by`. Introduce `a b`.

Rewrite using `[Matrix.fromBlocks_multiply]`. Establish `e1` using `key a b`. Establish `e2` using `key a (b * s)`. Establish `e3` using `key (s⁻¹ * a) b`. Establish `e4` using `key (s⁻¹ * a) (b * s)`.

Simplify using `only [mul_assoc] at e1 e2 e3 e4 ⊢`. Rewrite using `[e1, e2, e3, e4] }`. Establish `hM : ∀ g, (M.toHomUnits g : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s))` using `fun g => rfl`. Use `⟨M.toHomUnits, ?_, ?_⟩` and prove the remaining obligations. Introduce `h h' hh`.

Establish `h2` using `h.2`. Rewrite using `[hM, ← hh, hin, hin, hout (h * s) (by rw [hm]; tauto), hout (s⁻¹ * h) (by rw [hm]; tauto)]`. Introduce `t ht`. Rewrite using `[hM, ← ht, hin, inv_mul_cancel, one_mul, hone, hout s hs]`.
-/
theorem UpperTheory.V.AlgebraTools.indTwo :
    ∀ {R G n : Type} [CommRing R] [Group G] [Fintype n] [DecidableEq n] (H : Subgroup G) (s : G), H.index = 2 → s ∉ H → ∀ r : H →* GL n R, ∃ I : G →* GL (n ⊕ n) R, (∀ h h' : H, (h' : G) = s⁻¹ * h * s → (I h : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks (r h : Matrix n n R) 0 0 (r h' : Matrix n n R)) ∧ ∀ t : H, (t : G) = s * s → (I s : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks 0 (r t : Matrix n n R) 1 0 := by
  intro R G n _ _ _ _ H s hH hs r
  classical
  obtain ⟨r0, hin, hout⟩ : ∃ r0 : G → Matrix n n R,
      (∀ h : H, r0 h = (r h : Matrix n n R)) ∧ ∀ g, g ∉ H → r0 g = 0 := by
    refine ⟨fun g => if h : g ∈ H then (r ⟨g, h⟩ : Matrix n n R) else 0, ?_, ?_⟩
    · intro h
      simp only [dif_pos h.2]
    · intro g hg
      simp only [dif_neg hg]
  have hs' : s⁻¹ ∉ H := fun h => hs (by simpa using h)
  have hm : ∀ a b : G, a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hH
  have hmul : ∀ a b : G, a ∈ H → b ∈ H → r0 (a * b) = r0 a * r0 b := by
    intro a b ha hb
    have h1 := hin ⟨a, ha⟩
    have h2 := hin ⟨b, hb⟩
    have h3 := hin (⟨a, ha⟩ * ⟨b, hb⟩)
    rw [map_mul, Units.val_mul, ← h1, ← h2] at h3
    exact h3
  have hone : r0 1 = 1 := by
    have := hin 1
    rw [map_one] at this
    simpa using this
  have key : ∀ a b : G, r0 (a * b) = r0 a * r0 b + r0 (a * s) * r0 (s⁻¹ * b) := by
    intro a b
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
    · rw [hmul a b ha hb, hout (a * s) (by rw [hm]; tauto), zero_mul, add_zero]
    · rw [hout (a * b) (by rw [hm]; tauto), hout b hb, hout (a * s) (by rw [hm]; tauto)]
      simp
    · rw [hout (a * b) (by rw [hm]; tauto), hout a ha, hout (s⁻¹ * b) (by rw [hm]; tauto)]
      simp
    · rw [hout a ha, zero_mul, zero_add,
        ← hmul _ _ (by rw [hm]; tauto) (by rw [hm]; tauto)]
      congr 1
      group
  let M : G →* Matrix (n ⊕ n) (n ⊕ n) R :=
    { toFun := fun g => Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s))
      map_one' := by
        rw [one_mul, mul_one, inv_mul_cancel, hone, hout s hs, hout _ hs', Matrix.fromBlocks_one]
      map_mul' := by
        intro a b
        rw [Matrix.fromBlocks_multiply]
        have e1 := key a b
        have e2 := key a (b * s)
        have e3 := key (s⁻¹ * a) b
        have e4 := key (s⁻¹ * a) (b * s)
        simp only [mul_assoc] at e1 e2 e3 e4 ⊢
        rw [e1, e2, e3, e4] }
  have hM : ∀ g, (M.toHomUnits g : Matrix (n ⊕ n) (n ⊕ n) R) =
      Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s)) := fun g => rfl
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · intro h h' hh
    have h2 := h.2
    rw [hM, ← hh, hin, hin, hout (h * s) (by rw [hm]; tauto),
      hout (s⁻¹ * h) (by rw [hm]; tauto)]
  · intro t ht
    rw [hM, ← ht, hin, inv_mul_cancel, one_mul, hone, hout s hs]
