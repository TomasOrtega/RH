import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselRadical

/- English proof (translation)
Take `⟨hU, hcol, hmid⟩` from `hu`. Establish `hspan : ∀ y : Fin (2 * r + k + 1) → ℂ, (∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) → y = colE k r *ᵥ fun b => y (PI.UpqRep.eI k r b)`. Introduce `y hy`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, colE, ite_mul, one_mul, zero_mul]`.

Distinguish the cases in `hi : (i : ℕ) < r`. Rewrite using `[Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]`. Establish `h : i = PI.UpqRep.eI k r ⟨i, hi⟩` using `Fin.ext rfl`. Rewrite using `[if_pos h, ← h]`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (Fin.ext (congrArg Fin.val h).symm)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[hy i (not_lt.mp hi)]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hi` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `b.isLt`. Establish `key : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) (j : Fin (2 * r + k + 1)), (b : ℕ) + j = 2 * r + k → (((colE k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) *ᵥ x) b = x j`.

Introduce `x b j hbj`. Rewrite using `[← Matrix.mulVec_mulVec]`. Establish `hc : ∀ w : Fin (2 * r + k + 1) → ℂ, ((colE k r)ᴴ *ᵥ w) b = w (PI.UpqRep.eI k r b)`. Introduce `w`. Simplify using `[Matrix.mulVec, dotProduct, colE, Matrix.conjTranspose_apply]`.

Rewrite using `[hc]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Establish `hb` using `b.isLt`. Rewrite using `[Finset.sum_eq_single j]`. Establish `h1 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) j = 1`.

Simplify using `[Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hbj, hb]`. Rewrite using `[h1, one_mul]`. Introduce `m _ hm`. Establish `hne : (b : ℕ) + m ≠ 2 * r + k` using `fun h => hm (Fin.ext (by omega))`. Establish `h0 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) m = 0`.

Simplify using `[Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hne, not_le.mpr hb]`. Rewrite using `[h0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `⟨hU, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Establish `hy : ∀ m, ((u - 1) *ᵥ fun m => colE k r m i) m = u m (PI.UpqRep.eI k r i) - if m = PI.UpqRep.eI k r i then 1 else 0`. Introduce `m`. Simplify using `[Matrix.mulVec, dotProduct, colE, Matrix.sub_apply, Matrix.one_apply, sub_mul]`. Use `⟨fun b => ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r b), ?_, hspan _ ?_⟩` and prove the remaining obligations.

Introduce `j hij show ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r j) = 0`. Rewrite using `[hy]`. Conclude with `sub_eq_zero.mpr (hcol i _ hij)`. Introduce `m hm`. Rewrite using `[hy]`.

Conclude with `sub_eq_zero.mpr (hcol i m (le_trans (Nat.le_of_lt i.isLt) hm))`. Introduce `x hx`. Establish `hxz : ∀ j : Fin (2 * r + k + 1), r + k < (j : ℕ) → x j = 0`. Introduce `j hj`. Establish `hjN` using `j.isLt`.

Establish `hb : 2 * r + k - (j : ℕ) < r` using `by omega`. Establish `h` using `key x ⟨2 * r + k - j, hb⟩ j (by show 2 * r + k - (j : ℕ) + j = 2 * r + k; omega)`. Rewrite using `[← h, hx]`. Both sides reduce to the same expression. Use `⟨fun b => ((u - 1) *ᵥ x) (PI.UpqRep.eI k r b), hspan _ ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hj : (j : ℕ) ≤ r + k`.

Establish `h0 : (u - 1) i j = 0`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]`. Distinguish the cases in `hjr : (j : ℕ) < r`. Conclude with `hcol ⟨j, hjr⟩ i (by show (j : ℕ) ≤ i; omega)`. Conclude with `hmid i j (not_lt.mp hjr) hj hi`.

Rewrite using `[h0, zero_mul]`. Rewrite using `[hxz j (not_le.mp hj), mul_zero]`.
-/
theorem mem_unipRad_of_mem_Nset {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hu : u ∈ Formalism.QuantumDeterminants.Nset k r) : u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  obtain ⟨hU, hcol, hmid⟩ := hu
  have hspan : ∀ y : Fin (2 * r + k + 1) → ℂ, (∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) →
      y = colE k r *ᵥ fun b => y (PI.UpqRep.eI k r b) := by
    intro y hy
    funext i
    simp only [Matrix.mulVec, dotProduct, colE, ite_mul, one_mul, zero_mul]
    by_cases hi : (i : ℕ) < r
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have h : i = PI.UpqRep.eI k r ⟨i, hi⟩ := Fin.ext rfl
        rw [if_pos h, ← h]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (congrArg Fin.val h).symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hy i (not_lt.mp hi)]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact b.isLt
  have key : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) (j : Fin (2 * r + k + 1)), (b : ℕ) + j = 2 * r + k →
      (((colE k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) *ᵥ x) b = x j := by
    intro x b j hbj
    rw [← Matrix.mulVec_mulVec]
    have hc : ∀ w : Fin (2 * r + k + 1) → ℂ, ((colE k r)ᴴ *ᵥ w) b = w (PI.UpqRep.eI k r b) := by
      intro w
      simp [Matrix.mulVec, dotProduct, colE, Matrix.conjTranspose_apply]
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    have hb := b.isLt
    rw [Finset.sum_eq_single j]
    · have h1 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) j = 1 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hbj, hb]
      rw [h1, one_mul]
    · intro m _ hm
      have hne : (b : ℕ) + m ≠ 2 * r + k := fun h => hm (Fin.ext (by omega))
      have h0 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) m = 0 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hne, not_le.mpr hb]
      rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨hU, ?_, ?_⟩
  · intro i
    have hy : ∀ m, ((u - 1) *ᵥ fun m => colE k r m i) m
        = u m (PI.UpqRep.eI k r i) - if m = PI.UpqRep.eI k r i then 1 else 0 := by
      intro m
      simp [Matrix.mulVec, dotProduct, colE, Matrix.sub_apply, Matrix.one_apply, sub_mul]
    refine ⟨fun b => ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r b), ?_, hspan _ ?_⟩
    · intro j hij
      show ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r j) = 0
      rw [hy]
      exact sub_eq_zero.mpr (hcol i _ hij)
    · intro m hm
      rw [hy]
      exact sub_eq_zero.mpr (hcol i m (le_trans (Nat.le_of_lt i.isLt) hm))
  · intro x hx
    have hxz : ∀ j : Fin (2 * r + k + 1), r + k < (j : ℕ) → x j = 0 := by
      intro j hj
      have hjN := j.isLt
      have hb : 2 * r + k - (j : ℕ) < r := by omega
      have h := key x ⟨2 * r + k - j, hb⟩ j (by show 2 * r + k - (j : ℕ) + j = 2 * r + k; omega)
      rw [← h, hx]
      rfl
    refine ⟨fun b => ((u - 1) *ᵥ x) (PI.UpqRep.eI k r b), hspan _ ?_⟩
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : (j : ℕ) ≤ r + k
    · have h0 : (u - 1) i j = 0 := by
        rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
        by_cases hjr : (j : ℕ) < r
        · exact hcol ⟨j, hjr⟩ i (by show (j : ℕ) ≤ i; omega)
        · exact hmid i j (not_lt.mp hjr) hj hi
      rw [h0, zero_mul]
    · rw [hxz j (not_le.mp hj), mul_zero]

end UpperTheory.Lit.Bur.BesselRadical

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | exact UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | (intros; apply UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup : ∀ {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.Nset k r), u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  first | exact @UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | exact UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | (intros; apply UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset <;> assumption)
