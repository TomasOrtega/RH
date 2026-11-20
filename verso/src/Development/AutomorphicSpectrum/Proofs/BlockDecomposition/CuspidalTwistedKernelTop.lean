import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

section Groups

variable {k : Type} [Field k]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem blk_stdBlocks_two {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (i : Fin N) :
    blk (stdBlocks ![n, N - n] h) i = if (i : ℕ) < n then 0 else 1 := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks ![n, N - n] h).surjective i
  rw [blk_apply]
  have := stdBlocks_val ![n, N - n] h c i'
  fin_cases c
  · have hi := i'.2
    simp at this hi ⊢
    omega
  · have hi := i'.2
    simp at this hi ⊢
    omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities.
-/
theorem mem_unipRad_two_iff {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks ![n, N - n] h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_stdBlocks_two, blk_stdBlocks_two]
  have : ((if (i : ℕ) < n then (0 : Fin 2) else 1) < if (j : ℕ) < n then 0 else 1) ↔
      ((i : ℕ) < n ∧ n ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;> simp [hi, hj] <;> omega
  rw [this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem unipRad_two_le_derUnip {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) :
    unipRad k (stdBlocks ![n, N - n] h) ≤ derUnip k N n := by
  intro g hg
  have hE := (mem_unipRad_two_iff h).1 hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · intro i hi
    ext r
    have hc : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hc, hE r i (by omega)]
    by_cases hri : r = i
    · subst hri; simp
    · rw [one_apply_ne hri, Pi.single_apply, if_neg hri]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem unipRad_two_ne_bot {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (h1 : 1 ≤ n) (h2 : n < N) :
    unipRad k (stdBlocks ![n, N - n] h) ≠ ⊥ := by
  set i : Fin N := ⟨0, by omega⟩
  set j : Fin N := ⟨n, h2⟩
  have hne : i ≠ j := by
    intro e
    have := congrArg Fin.val e
    simp [i, j] at this
    omega
  let t : GL (Fin N) k := ⟨transvection i j 1, transvection i j (-1),
    by rw [transvection_mul_transvection_same i j hne]; simp,
    by rw [transvection_mul_transvection_same i j hne]; simp⟩
  have ht : t ∈ unipRad k (stdBlocks ![n, N - n] h) := by
    refine (mem_unipRad_two_iff h).2 fun r s hrs => ?_
    show transvection i j (1 : k) r s = _
    have : ¬ (r = i ∧ s = j) := by
      rintro ⟨rfl, rfl⟩
      exact hrs ⟨by simp [i]; omega, le_refl _⟩
    simp only [transvection, Matrix.add_apply]
    rw [Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact this ⟨rfl, rfl⟩
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ht
  simp [t, transvection, one_apply_ne hne] at this

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem derChar_eq_one_of_mem_unipRad_two {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    (u : derUnip k N n) (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks ![n, N - n] h)) :
    derChar k ψ N n u = 1 := by
  have hE := (mem_unipRad_two_iff h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem twKer_unipRad_two_le {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 ≤ twKer π (derUnip k N n) (derChar k ψ N n) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_two_le_derUnip h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad_two ψ h _ u.2]
  simp

end Chars

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem twKer_derUnip_eq_top_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  intro k _ _ _ _ ψ N n V _ _ π hπ h1 h2
  have h : ∑ c, ![n, N - n] c = N := by
    simp [Fin.sum_univ_two]
    omega
  have hs := hπ.2 2 ![n, N - n] (stdBlocks ![n, N - n] h) (unipRad_two_ne_bot h h1 h2)
  have htop : twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hs
  exact eq_top_iff.2 (htop ▸ twKer_unipRad_two_le ψ h π)

end GlobalTheory.CompanionTheory.BZMir
