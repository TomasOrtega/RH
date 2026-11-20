import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, fun l _ => Matrix.one_mulVec _, fun l hl => absurd hl (by simp)⟩`. Consider the case `insert t S htS ih`. Take `⟨P, hP1, hP2⟩` from `ih (fun h => hS (Finset.mem_insert_of_mem h))`. Establish `hne : t₀ ≠ t` using `fun h => hS (h ▸ Finset.mem_insert_self t S)`.

Take `⟨a, c, hc⟩` from `hsep t₀ t hne`. Establish `key : ∀ l, (P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O)))).mulVec (u l) = ((↑c⁻¹ : O) * (σ l.1 a - σ t a)) • P.mulVec (u l)`. Introduce `l`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig, ← sub_smul, smul_smul, Matrix.mulVec_smul]`. Use `⟨P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O))), fun l hl => ?_, fun l hl => ?_⟩` and prove the remaining obligations.

Rewrite using `[key, hP1 l hl, hl, ← hc, Units.inv_mul, one_smul]`. Rewrite using `[key]`. Break down `Finset.mem_insert.mp hl with h | h` into its components or cases. Rewrite using `[h, sub_self, mul_zero, zero_smul]`. Rewrite using `[hP2 l h, smul_zero]`.
-/
theorem exists_matrix_fix_type_kill {O A : Type} [CommRing O] {d : ℕ}
    (ρ : A → Matrix (Fin d) (Fin d) O) {T : Type} [DecidableEq T] {r : T → ℕ} (σ : T → A → O)
    (u : (Σ t : T, Fin (r t)) → Fin d → O)
    (hsep : ∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a))
    (heig : ∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) (t₀ : T) (S : Finset T) (hS : t₀ ∉ S) :
    ∃ P : Matrix (Fin d) (Fin d) O, (∀ l, l.1 = t₀ → P.mulVec (u l) = u l) ∧
      (∀ l, l.1 ∈ S → P.mulVec (u l) = 0) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun l _ => Matrix.one_mulVec _, fun l hl => absurd hl (by simp)⟩
  | insert t S htS ih =>
    obtain ⟨P, hP1, hP2⟩ := ih (fun h => hS (Finset.mem_insert_of_mem h))
    have hne : t₀ ≠ t := fun h => hS (h ▸ Finset.mem_insert_self t S)
    obtain ⟨a, c, hc⟩ := hsep t₀ t hne
    have key : ∀ l, (P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O)))).mulVec (u l)
        = ((↑c⁻¹ : O) * (σ l.1 a - σ t a)) • P.mulVec (u l) := by
      intro l
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, heig, ← sub_smul, smul_smul, Matrix.mulVec_smul]
    refine ⟨P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O))),
      fun l hl => ?_, fun l hl => ?_⟩
    · rw [key, hP1 l hl, hl, ← hc, Units.inv_mul, one_smul]
    · rw [key]
      rcases Finset.mem_insert.mp hl with h | h
      · rw [h, sub_self, mul_zero, zero_smul]
      · rw [hP2 l h, smul_zero]

/- English proof (translation)
Introduce `O A _ d ρ T _ _ r σ u hsep heig hdual`. Use `choose lam hlam using hdual`. Use `choose P hP1 hP2 using fun t₀ : T => exists_matrix_fix_type_kill ρ σ u hsep heig t₀ (Finset.univ.erase t₀) (by simp)`. Use `⟨fun l => Matrix.vecMul (lam l.1 l.2) (P l.1), ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, i⟩ ⟨t', i'⟩`.

Express the relevant statement in the definitionally equal form `Matrix.vecMul (lam t i) (P t) ⬝ᵥ u ⟨t', i'⟩ = _`. Rewrite using `[← Matrix.dotProduct_mulVec]`. Distinguish the cases in `h : t' = t`. Substitute `h` using the available equality. Rewrite using `[hP1 t' ⟨t', i'⟩ rfl]`.

Use `hlam t' i i'` as an intermediate fact. Simplify `this` using `[dotProduct]`. Rewrite using `[hP2 t ⟨t', i'⟩ (by simpa using h), dotProduct_zero, if_neg]`. Introduce `h'`. Conclude with `h (congrArg Sigma.fst h').symm`.
-/
theorem exists_dual_forms_of_separated_types :
    ∀ (O A : Type) [CommRing O] (d : ℕ) (ρ : A → Matrix (Fin d) (Fin d) O) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (σ : T → A → O) (u : (Σ t : T, Fin (r t)) → Fin d → O), (∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a)) → (∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) → (∀ t, ∃ lam : Fin (r t) → Fin d → O, ∀ i i', ∑ s, lam i s * u ⟨t, i'⟩ s = if i = i' then 1 else 0) → ∃ lam : (Σ t : T, Fin (r t)) → Fin d → O, ∀ l l', ∑ s, lam l s * u l' s = if l = l' then 1 else 0 := by
  intro O A _ d ρ T _ _ r σ u hsep heig hdual
  choose lam hlam using hdual
  choose P hP1 hP2 using fun t₀ : T =>
    exists_matrix_fix_type_kill ρ σ u hsep heig t₀ (Finset.univ.erase t₀) (by simp)
  refine ⟨fun l => Matrix.vecMul (lam l.1 l.2) (P l.1), ?_⟩
  rintro ⟨t, i⟩ ⟨t', i'⟩
  change Matrix.vecMul (lam t i) (P t) ⬝ᵥ u ⟨t', i'⟩ = _
  rw [← Matrix.dotProduct_mulVec]
  by_cases h : t' = t
  · subst h
    rw [hP1 t' ⟨t', i'⟩ rfl]
    have := hlam t' i i'
    simpa [dotProduct] using this
  · rw [hP2 t ⟨t', i'⟩ (by simpa using h), dotProduct_zero, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

end GlobalTheory
