import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ZjCentral

/- English proof (translation)
Use extensionality with `i l`. Take `⟨⟨a, i'⟩, rfl⟩` from `(stdBlocks d hd).surjective i`. Take `⟨⟨b, l'⟩, rfl⟩` from `(stdBlocks d hd).surjective l`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Rewrite using `[leviEmb_apply_same]`. Distinguish the cases in `hil : i' = l'`. Substitute `hil` using the available equality. Distinguish the cases in `haj : a ≤ j`. Simplify using `[Zl.JC.zj, Zl.JC.blockIdx, haj, Matrix.GeneralLinearGroup.scalar]`.

Simplify using `[Zl.JC.zj, Zl.JC.blockIdx, haj]`. Establish `hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨a, l'⟩` using `fun e => hil (by`. Simplify using `using (stdBlocks d hd).injective e)`. Rewrite using `[Matrix.diagonal_apply_ne _ hne]`. Distinguish the cases in `haj : a ≤ j`.

Simplify using `[Zl.JC.zj, haj, Matrix.GeneralLinearGroup.scalar, hil]`. Simplify using `[Zl.JC.zj, haj, hil]`. Establish `hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨b, l'⟩` using `fun e => hab (by`. Simplify using `using congrArg Sigma.fst ((stdBlocks d hd).injective e))`. Rewrite using `[leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]`.
-/
theorem leviEmb_zj_eq_diagonal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ)
    (j : Fin h) :
    ((leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext i l
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, l'⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i' = l'
    · subst hil
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj, Matrix.GeneralLinearGroup.scalar]
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj]
    · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨a, l'⟩ := fun e => hil (by
        simpa using (stdBlocks d hd).injective e)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, haj, Matrix.GeneralLinearGroup.scalar, hil]
      · simp [Zl.JC.zj, haj, hil]
  · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨b, l'⟩ := fun e => hab (by
      simpa using congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]

/- English proof (translation)
Introduce `k _ _ _ _ h N d hd t j y hy`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, leviEmb_zj_eq_diagonal]`. Use extensionality with `i l`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Distinguish the cases in `hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l`. Rewrite using `[hil]`. Conclude with `mul_comm _ _`. Establish `h0 : (y : Matrix (Fin N) (Fin N) k) i l = 0` using `GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i l hil`. Rewrite using `[h0, mul_zero, zero_mul]`.
-/
theorem leviEmb_zj_comm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ)
    (j : Fin h), ∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd),
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * y =
      y * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) := by
  intro k _ _ _ _ h N d hd t j y hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, leviEmb_zj_eq_diagonal]
  ext i l
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l
  · rw [hil]
    exact mul_comm _ _
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i l = 0 :=
      GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i l hil
    rw [h0, mul_zero, zero_mul]

end GlobalTheory.CompanionTheory.ZjCentral
