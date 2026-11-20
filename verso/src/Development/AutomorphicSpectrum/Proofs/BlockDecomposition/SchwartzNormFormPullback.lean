import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.NormSB

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep

section Quadratic

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

/- English proof (translation)
Use `haveI := GroundTheory.LocalField.isModuleTopology F E`. Take `⟨c, hc⟩` from `Algebra.trace_surjective F E 1`. Establish `e : (fun x : E => Algebra.norm F x) = fun x => Algebra.trace F E (c * (x * conj F E x))`. Use function extensionality and compare the values at `x`. Rewrite using `[← algebraMap_norm_eq_mul_conj, mul_comm c, ← Algebra.smul_def, map_smul, hc, smul_eq_mul, mul_one]`.

Rewrite using `[e]`. Conclude with `(IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)).comp (continuous_const.mul (continuous_id.mul continuous_conj))`.
-/
theorem continuous_norm_quadratic : Continuous (fun x : E => Algebra.norm F x) := by
  haveI := GroundTheory.LocalField.isModuleTopology F E
  obtain ⟨c, hc⟩ := Algebra.trace_surjective F E 1
  have e : (fun x : E => Algebra.norm F x) =
      fun x => Algebra.trace F E (c * (x * conj F E x)) := by
    funext x
    rw [← algebraMap_norm_eq_mul_conj, mul_comm c, ← Algebra.smul_def, map_smul, hc, smul_eq_mul,
      mul_one]
  rw [e]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)).comp
    (continuous_const.mul (continuous_id.mul continuous_conj))

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (residueDegree F E) with h | h` into its components or cases. Establish `h1` using `residueCard_eq_pow (K := F) (E := E)`. Rewrite `h1` using `[h, pow_zero]`. Establish `h2` using `one_lt_residueCard (K := E)`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`.
-/
theorem residueDegree_pos_quadratic : 0 < residueDegree F E := by
  rcases Nat.eq_zero_or_pos (residueDegree F E) with h | h
  · have h1 := residueCard_eq_pow (K := F) (E := E)
    rw [h, pow_zero] at h1
    have h2 := one_lt_residueCard (K := E)
    omega
  · exact h

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `zero_mem _`. Establish `hN : Algebra.norm F x ≠ 0` using `Algebra.norm_ne_zero_iff.2 hx`. Rewrite `h` using `[mem_valBall_iff_le_ord hN, ord_norm (K := F) (L := E)]`. Rewrite using `[mem_valBall_iff_le_ord hx]`.

Establish `hd : (1 : ℤ) ≤ (residueDegree F E : ℤ)`. Conclude with `residueDegree_pos_quadratic F E` after adjusting the coercions. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hM1 : -|M| ≤ M` using `neg_abs_le M`.

Establish `hM0 : -|M| ≤ 0` using `by simp`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mem_valBall_of_norm_mem {M : ℤ} {x : E} (h : Algebra.norm F x ∈ valBall F M) :
    x ∈ valBall E (-|M|) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  have hN : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
  rw [mem_valBall_iff_le_ord hN, ord_norm (K := F) (L := E)] at h
  rw [mem_valBall_iff_le_ord hx]
  have hd : (1 : ℤ) ≤ (residueDegree F E : ℤ) := by
    exact_mod_cast residueDegree_pos_quadratic F E
  by_contra hlt
  push_neg at hlt
  have hM1 : -|M| ≤ M := neg_abs_le M
  have hM0 : -|M| ≤ 0 := by simp
  nlinarith

end Quadratic

end GlobalTheory.CompanionTheory.NormSB

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ f hf`. Take `⟨-, M, -, hM⟩` from `exists_invariant_of_mem_schwartzBruhat hf`. Use `mem_schwartzBruhat.2 ⟨hf.1.comp_continuous (GlobalTheory.CompanionTheory.NormSB.continuous_norm_quadratic F E), HasCompactSupport.intro (isCompact_valBall (-|M|)) fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hx (GlobalTheory.CompanionTheory.NormSB.mem_valBall_of_norm_mem F E (hM _ hne))`.
-/
theorem GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (f : F → ℂ), f ∈ schwartzBruhat F → (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨-, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  refine mem_schwartzBruhat.2 ⟨hf.1.comp_continuous (GlobalTheory.CompanionTheory.NormSB.continuous_norm_quadratic F E),
    HasCompactSupport.intro (isCompact_valBall (-|M|)) fun x hx => ?_⟩
  by_contra hne
  exact hx (GlobalTheory.CompanionTheory.NormSB.mem_valBall_of_norm_mem F E (hM _ hne))
