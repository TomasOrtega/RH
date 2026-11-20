import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

namespace GlobalTheory.RegSS

def monomialChar (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (a : Fin s → ℤ) :
    (Fin s → Fˣ) →* Ω where
  toFun t := algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, map_mul]

/- English proof (translation)
Introduce `F Ω _ _ _ s f S c hf`. Assume the negation of the conclusion as `hno`. Establish `hdiff : ∀ a, monomialChar F Ω s a ≠ f`. Introduce `a hEq`. Use `hno ⟨a, fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hEq]`. Both sides reduce to the same expression. Set `l : ((Fin s → Fˣ) →* Ω) →₀ Ω` to `Finsupp.single f 1 - ∑ a ∈ S, Finsupp.single (monomialChar F Ω s a) (c a)`. Establish `hvanish : Finsupp.linearCombination Ω (fun φ : (Fin s → Fˣ) →* Ω => (φ : (Fin s → Fˣ) → Ω)) l = 0`. Use function extensionality and compare the values at `t`.

Simplify using `only [l, map_sub, map_sum, Finsupp.linearCombination_single, one_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hf t]`. Rewrite using `[sub_eq_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show _ = c a * algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)`. Rewrite using `[Algebra.smul_def, mul_comm]`.

Establish `hl0 : l = 0` using `(linearIndependent_iff.mp (linearIndependent_monoidHom _ Ω)) l hvanish`. Establish `hlf : l f = 1`. Simplify using `only [l, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne' (hdiff a), sub_zero]`. Rewrite `hlf` using `[hl0, Finsupp.zero_apply]`.

Conclude with `zero_ne_one hlf`.
-/
theorem characterMonomial : CharacterMonomial := by
  classical
  intro F Ω _ _ _ s f S c hf
  by_contra hno

  have hdiff : ∀ a, monomialChar F Ω s a ≠ f := by
    intro a hEq
    refine hno ⟨a, fun t => ?_⟩
    rw [← hEq]
    rfl

  let l : ((Fin s → Fˣ) →* Ω) →₀ Ω :=
    Finsupp.single f 1 - ∑ a ∈ S, Finsupp.single (monomialChar F Ω s a) (c a)
  have hvanish : Finsupp.linearCombination Ω
      (fun φ : (Fin s → Fˣ) →* Ω => (φ : (Fin s → Fˣ) → Ω)) l = 0 := by
    funext t
    simp only [l, map_sub, map_sum, Finsupp.linearCombination_single, one_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hf t]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = c a * algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
    rw [Algebra.smul_def, mul_comm]
  have hl0 : l = 0 := (linearIndependent_iff.mp (linearIndependent_monoidHom _ Ω)) l hvanish
  have hlf : l f = 1 := by
    simp only [l, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne' (hdiff a), sub_zero]
  rw [hl0, Finsupp.zero_apply] at hlf
  exact zero_ne_one hlf

end GlobalTheory.RegSS
