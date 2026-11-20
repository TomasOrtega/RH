import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.WedgeMul

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => exact ⟨1, Or.inl rfl, by simp⟩`. Consider the case `cons x _ ih`. Take `⟨ε, hε, e⟩` from `ih`. Conclude with `⟨ε, hε, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩`.

Consider the case `swap x y l`. Use `⟨-1, Or.inr rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul, one_smul]`. Consider the case `trans _ _ ih₁ ih₂`. Take `⟨ε₁, h₁, e₁⟩` from `ih₁`.

Take `⟨ε₂, h₂, e₂⟩` from `ih₂`. Use `⟨ε₁ * ε₂, ?_, by rw [e₁, e₂, smul_smul]⟩` and prove the remaining obligations. Apply the tactic sequence `rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp`.
-/
theorem prod_perm_sign {A : Type} [Ring A] {α : Type} (f : α → A)
    (hf : ∀ a b, f a * f b = -(f b * f a)) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (l₁.map f).prod = ε • (l₂.map f).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨ε, hε, e⟩ := ih
    exact ⟨ε, hε, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul, one_smul]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ε₁, h₁, e₁⟩ := ih₁
    obtain ⟨ε₂, h₂, e₂⟩ := ih₂
    refine ⟨ε₁ * ε₂, ?_, by rw [e₁, e₂, smul_smul]⟩
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

end GlobalTheory.LogDR.WedgeMul

open GlobalTheory.LogDR.WedgeMul in

/- English proof (translation)
Introduce `K _ n x i I`. Use `set f : Fin n → abelian₂ K := fun j => ExteriorAlgebra.ι K (dlog (x j)) with hfdef`. Establish `hf : ∀ a b, f a * f b = -(f b * f a)` using `fun a b => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)`. Prove the components needed by the constructor for the conclusion. Introduce `hi`.

Establish `hp : (I.sort (· ≤ ·)).Perm (i :: (I.erase i).sort (· ≤ ·))`. Use `(List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_` and prove the remaining obligations. Use `List.nodup_cons.2 ⟨?_, Finset.sort_nodup _ _⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Distinguish the cases in `ha : a = i`.

Substitute `ha` using the available equality. Simplify using `[hi]`. Simplify using `[ha]`. Take `⟨ε, -, e⟩` from `prod_perm_sign f hf hp`. Use `show f i * ((I.sort (· ≤ ·)).map f).prod = 0`.

Rewrite using `[e, mul_smul_comm, List.map_cons, List.prod_cons, ← mul_assoc]`. Simplify using `[hfdef, ExteriorAlgebra.ι_sq_zero]`. Introduce `hi`. Establish `hp : ((insert i I).sort (· ≤ ·)).Perm (i :: I.sort (· ≤ ·))`. Use `(List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_` and prove the remaining obligations.

Conclude with `List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩`. Simplify using the standard rewrite rules. Take `⟨ε, hε, e⟩` from `prod_perm_sign f hf hp`. Use `⟨ε, hε, ?_⟩` and prove the remaining obligations. Use `show f i * ((I.sort (· ≤ ·)).map f).prod = ε • (((insert i I).sort (· ≤ ·)).map f).prod`.

Rewrite using `[e, List.map_cons, List.prod_cons, smul_smul]`. Apply the tactic sequence `rcases hε with rfl | rfl <;> simp`.
-/
theorem GlobalTheory.LogDR.dlog_mul_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  intro K _ n x i I
  set f : Fin n → abelian₂ K := fun j => ExteriorAlgebra.ι K (dlog (x j)) with hfdef
  have hf : ∀ a b, f a * f b = -(f b * f a) := fun a b =>
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  constructor
  · intro hi
    have hp : (I.sort (· ≤ ·)).Perm (i :: (I.erase i).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · refine List.nodup_cons.2 ⟨?_, Finset.sort_nodup _ _⟩
        simp
      · by_cases ha : a = i
        · subst ha; simp [hi]
        · simp [ha]
    obtain ⟨ε, -, e⟩ := prod_perm_sign f hf hp
    show f i * ((I.sort (· ≤ ·)).map f).prod = 0
    rw [e, mul_smul_comm, List.map_cons, List.prod_cons, ← mul_assoc]
    simp [hfdef, ExteriorAlgebra.ι_sq_zero]
  · intro hi
    have hp : ((insert i I).sort (· ≤ ·)).Perm (i :: I.sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · exact List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩
      · simp
    obtain ⟨ε, hε, e⟩ := prod_perm_sign f hf hp
    refine ⟨ε, hε, ?_⟩
    show f i * ((I.sort (· ≤ ·)).map f).prod = ε • (((insert i I).sort (· ≤ ·)).map f).prod
    rw [e, List.map_cons, List.prod_cons, smul_smul]
    rcases hε with rfl | rfl <;> simp
