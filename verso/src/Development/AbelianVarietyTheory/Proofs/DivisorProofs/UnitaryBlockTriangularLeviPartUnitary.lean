import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `h : β i = β j`. Rewrite using `[← hAB, Matrix.mul_apply]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy (β l) (β i) with h1 | h1 | h1` into its components or cases. Rewrite using `[hA h1]`. Simplify using the standard rewrite rules. Rewrite using `[if_pos h1.symm, if_pos (h1.trans h)]`.

Rewrite using `[hB (h ▸ h1 : β j < β l)]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne (fun e => h (by rw [e]))]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : β i = β l`.

Rewrite using `[if_neg (hl ▸ h : ¬ β l = β j), mul_zero]`. Rewrite using `[if_neg hl, zero_mul]`.
-/
theorem blockDiagPart_mul {L : Type} [Field L] {n : ℕ} (β : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L)
    (hA : A.BlockTriangular β) (hB : B.BlockTriangular β) (hAB : A * B = 1) :
    (Matrix.of fun a b => if β a = β b then A a b else 0) *
      (Matrix.of fun a b => if β a = β b then B a b else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h : β i = β j
  · rw [← hAB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
    · rw [hA h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hB (h ▸ h1 : β j < β l)]; simp
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e]))]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [if_neg (hl ▸ h : ¬ β l = β j), mul_zero]
    · rw [if_neg hl, zero_mul]

/- English proof (translation)
Introduce `L _ _ σ n β hβ g hg`. Establish `hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev` using `fun a b => ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩`. Establish `h0 : (mat g⁻¹).BlockTriangular β`. Use `letI : Invertible (mat g) := (g : GL (Fin n) L).invertible`. Establish `e : mat g⁻¹ = (mat g)⁻¹` using `by simp [mat]`.

Rewrite using `[e]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hg`. Establish `h1` using `blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)`. Use `set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM`. Establish `h2 : antiJ L n * (cT σ M * antiJ L n) = Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0`.

Use extensionality with `a b`. Rewrite using `[antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]`. Distinguish the cases in `h : β a = β b`. Rewrite using `[if_pos h, if_pos ((hβ' _ _).1 h.symm)]`. Rewrite using `[if_neg h, if_neg (fun e => h ((hβ' _ _).2 e).symm), map_zero]`.

Establish `h3 : cT σ M * antiJ L n * M = antiJ L n`. Rewrite `h1` using `[← h2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n), GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]`. Use `_ = antiJ L n := by rw [h1, Matrix.mul_one]`.

Take `⟨m, hm⟩` from `exists_mat M h3`. Establish `hmL : m ∈ leviU σ β` using `fun i j h => by rw [hm, hM, Matrix.of_apply, if_neg h]`. Use `⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, if_pos h], fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : β i = β l`. Rewrite using `[hm, hM, Matrix.of_apply] split_ifs with h4`. Both sides reduce to the same expression. Rewrite using `[hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]`. Rewrite using `[(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]`.
-/
theorem leviPart : LeviPart := by
  intro L _ _ σ n β hβ g hg
  have hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev := fun a b =>
    ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩
  have h0 : (mat g⁻¹).BlockTriangular β := by
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h1 := blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM
  have h2 : antiJ L n * (cT σ M * antiJ L n) =
      Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0 := by
    ext a b
    rw [antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]
    by_cases h : β a = β b
    · rw [if_pos h, if_pos ((hβ' _ _).1 h.symm)]
    · rw [if_neg h, if_neg (fun e => h ((hβ' _ _).2 e).symm), map_zero]
  have h3 : cT σ M * antiJ L n * M = antiJ L n := by
    rw [← h2] at h1
    calc cT σ M * antiJ L n * M
        = antiJ L n * (antiJ L n * (cT σ M * antiJ L n) * M) := by
          rw [← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n),
            GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = antiJ L n := by rw [h1, Matrix.mul_one]
  obtain ⟨m, hm⟩ := exists_mat M h3
  have hmL : m ∈ leviU σ β := fun i j h => by rw [hm, hM, Matrix.of_apply, if_neg h]
  refine ⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, if_pos h], fun i j h => ?_⟩
  rw [← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : β i = β l
  · rw [hm, hM, Matrix.of_apply]
    split_ifs with h4
    · rfl
    · rw [hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]
  · rw [(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]

end GlobalTheory.SatakeWeyl
