import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJPow

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hq1' : (1 : ℝ) < (residueCard F : ℝ)` using `by exact_mod_cast one_lt_residueCard (K := F)`. Use `set q : ℝ := (residueCard F : ℝ) with hq`. Establish `hq1 : 1 < q` using `hq1'`. Establish `hq0 : 0 < q` using `by linarith`. Use `set ρ : ℝ := q ^ (-α) with hρ`.

Establish `hρ0 : 0 < ρ` using `Real.rpow_pos_of_pos hq0 _`. Establish `hρ1 : ρ < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt R hq1`. Use `set S : Set F := {y | (GroundTheory.LocalField.modulus y : ℝ) ≤ R} with hS`. Establish `hmm : Measurable fun y : F => (GroundTheory.LocalField.modulus y : ℝ)` using `measurable_modulus.coe_nnreal_real`.

Establish `hSm : MeasurableSet S` using `measurableSet_le hmm measurable_const`. Set `g : F → ENNReal` to `S.indicator fun x => ENNReal.ofReal ((GroundTheory.LocalField.modulus x : ℝ) ^ α)`. Establish `hg : Measurable g` using `(ENNReal.measurable_ofReal.comp (hmm.pow_const α)).indicator hSm`. Set `a : ℤ → ℝ` to `fun k => if -(n : ℤ) ≤ k then ρ ^ k else 0`. Establish `ha0 : ∀ k, 0 ≤ a k` using `fun k => by`.

Simplify using `only [a]`. Use `split_ifs`. Conclude with `zpow_nonneg hρ0.le _`. Conclude with `le_rfl`. Establish `hsum : HasSum a (ρ ^ (-(n : ℤ)) * (1 - ρ)⁻¹)`.

Use `hasSum_int_of_shift (-(n : ℤ)) (fun k hk => by simp [a, not_le.mpr hk]) ?_` and prove the remaining obligations. Establish `e : (fun m : ℕ => a (-(n : ℤ) + m)) = fun m : ℕ => ρ ^ (-(n : ℤ)) * ρ ^ m`. Use function extensionality and compare the values at `m`. Simplify using `only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]`. Rewrite using `[zpow_add₀ hρ0.ne', zpow_natCast]`.

Rewrite using `[e]`. Conclude with `(hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _`. Establish `hbound : ∀ u : Fˣ, g (u : F) ≤ ENNReal.ofReal (a (ord (u : F)))`. Introduce `u`. Distinguish the cases in `hu : (u : F) ∈ S`.

Establish `hmod : (GroundTheory.LocalField.modulus (u : F) : ℝ) = q ^ (-ord (u : F))`. Rewrite using `[modulus_of_ne_zero u.ne_zero]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hk : -(n : ℤ) ≤ ord (u : F)`.

Establish `h1 : q ^ (-ord (u : F)) < q ^ (n : ℤ)`. Rewrite using `[zpow_natCast, ← hmod]`. Conclude with `lt_of_le_of_lt hu hn`. Use `(zpow_lt_zpow_iff_right₀ hq1).1 h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [g, a, Set.indicator_of_mem hu, if_pos hk]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Use `le_of_eq ?_` and prove the remaining obligations. Rewrite using `[hmod, hρ, ← Real.rpow_intCast q, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast (q ^ (-α)), ← Real.rpow_mul hq0.le]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[g, Set.indicator_of_notMem hu]`. Establish `hfin : ∫⁻ u : Fˣ, g (u : F) ∂multHaar F < ⊤`. Use `(lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]`. Conclude with `ENNReal.ofReal_lt_top`. Rewrite `hfin` using `[lintegral_multHaar hg]`. Establish `hfin2 : ∫⁻ x in ({0}ᶜ : Set F), ((GroundTheory.LocalField.modulus x : ENNReal))⁻¹ * g x ∂haarIntegers F < ⊤`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_lt, top_le_iff]`. Rewrite `hfin` using `[h, ENNReal.mul_top multHaarConst_ne_zero]`. Conclude with `lt_irrefl _ hfin`. Use `⟨(hmm.pow_const _).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `lt_of_le_of_lt ?_ hfin2` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∫⁻ x in S, ‖(GroundTheory.LocalField.modulus x : ℝ) ^ (α - 1)‖ₑ ∂haarIntegers F ≤ _`. Rewrite using `[← lintegral_indicator hSm, ← lintegral_indicator (measurableSet_singleton (0 : F)).compl]`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Establish `h0 : ∀ᵐ x ∂haarIntegers F, x ≠ 0`. Rewrite using `[ae_iff]`.

Simplify using `using haarIntegers_singleton_zero`. Use `filter_upwards [h0] with x hx`. Establish `ht : 0 < (GroundTheory.LocalField.modulus x : ℝ)` using `by exact_mod_cast modulus_pos hx`. Distinguish the cases in `hxS : x ∈ S`. Rewrite using `[Set.indicator_of_mem hxS, Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set F) from hx)]`.

Simplify using `only [g, Set.indicator_of_mem hxS]`. Rewrite using `[Real.enorm_eq_ofReal (Real.rpow_nonneg ht.le _), Real.rpow_sub_one ht.ne', div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht, ENNReal.ofReal_coe_nnreal]`. Rewrite using `[Set.indicator_of_notMem hxS]`. Simplify using the standard rewrite rules.
-/
theorem integrableOn_haarIntegers_modulus_rpow {α : ℝ} (hα : 0 < α) (R : ℝ) :
    IntegrableOn (fun y : F => (GroundTheory.LocalField.modulus y : ℝ) ^ (α - 1))
      {y | (GroundTheory.LocalField.modulus y : ℝ) ≤ R} (haarIntegers F) := by
  have hq1' : (1 : ℝ) < (residueCard F : ℝ) := by exact_mod_cast one_lt_residueCard (K := F)
  set q : ℝ := (residueCard F : ℝ) with hq
  have hq1 : 1 < q := hq1'
  have hq0 : 0 < q := by linarith
  set ρ : ℝ := q ^ (-α) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R hq1
  set S : Set F := {y | (GroundTheory.LocalField.modulus y : ℝ) ≤ R} with hS
  have hmm : Measurable fun y : F => (GroundTheory.LocalField.modulus y : ℝ) :=
    measurable_modulus.coe_nnreal_real
  have hSm : MeasurableSet S := measurableSet_le hmm measurable_const
  let g : F → ENNReal :=
    S.indicator fun x => ENNReal.ofReal ((GroundTheory.LocalField.modulus x : ℝ) ^ α)
  have hg : Measurable g := (ENNReal.measurable_ofReal.comp (hmm.pow_const α)).indicator hSm
  let a : ℤ → ℝ := fun k => if -(n : ℤ) ≤ k then ρ ^ k else 0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [a]
    split_ifs
    · exact zpow_nonneg hρ0.le _
    · exact le_rfl
  have hsum : HasSum a (ρ ^ (-(n : ℤ)) * (1 - ρ)⁻¹) := by
    refine hasSum_int_of_shift (-(n : ℤ)) (fun k hk => by simp [a, not_le.mpr hk]) ?_
    have e : (fun m : ℕ => a (-(n : ℤ) + m)) = fun m : ℕ => ρ ^ (-(n : ℤ)) * ρ ^ m := by
      funext m
      simp only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]
      rw [zpow_add₀ hρ0.ne', zpow_natCast]
    rw [e]
    exact (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ u : Fˣ, g (u : F) ≤ ENNReal.ofReal (a (ord (u : F))) := by
    intro u
    by_cases hu : (u : F) ∈ S
    · have hmod : (GroundTheory.LocalField.modulus (u : F) : ℝ) = q ^ (-ord (u : F)) := by
        rw [modulus_of_ne_zero u.ne_zero]
        push_cast
        rfl
      have hk : -(n : ℤ) ≤ ord (u : F) := by
        have h1 : q ^ (-ord (u : F)) < q ^ (n : ℤ) := by
          rw [zpow_natCast, ← hmod]
          exact lt_of_le_of_lt hu hn
        have := (zpow_lt_zpow_iff_right₀ hq1).1 h1
        omega
      simp only [g, a, Set.indicator_of_mem hu, if_pos hk]
      apply ENNReal.ofReal_le_ofReal
      refine le_of_eq ?_
      rw [hmod, hρ, ← Real.rpow_intCast q, ← Real.rpow_mul hq0.le,
        ← Real.rpow_intCast (q ^ (-α)), ← Real.rpow_mul hq0.le]
      congr 1
      push_cast
      ring
    · simp [g, Set.indicator_of_notMem hu]
  have hfin : ∫⁻ u : Fˣ, g (u : F) ∂multHaar F < ⊤ := by
    refine (lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]
    exact ENNReal.ofReal_lt_top
  rw [lintegral_multHaar hg] at hfin
  have hfin2 : ∫⁻ x in ({0}ᶜ : Set F), ((GroundTheory.LocalField.modulus x : ENNReal))⁻¹ * g x
      ∂haarIntegers F < ⊤ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top multHaarConst_ne_zero] at hfin
    exact lt_irrefl _ hfin
  refine ⟨(hmm.pow_const _).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt ?_ hfin2
  change ∫⁻ x in S, ‖(GroundTheory.LocalField.modulus x : ℝ) ^ (α - 1)‖ₑ ∂haarIntegers F ≤ _
  rw [← lintegral_indicator hSm, ← lintegral_indicator (measurableSet_singleton (0 : F)).compl]
  refine lintegral_mono_ae ?_
  have h0 : ∀ᵐ x ∂haarIntegers F, x ≠ 0 := by
    rw [ae_iff]
    simpa using haarIntegers_singleton_zero
  filter_upwards [h0] with x hx
  have ht : 0 < (GroundTheory.LocalField.modulus x : ℝ) := by exact_mod_cast modulus_pos hx
  by_cases hxS : x ∈ S
  · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set F) from hx)]
    simp only [g, Set.indicator_of_mem hxS]
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg ht.le _), Real.rpow_sub_one ht.ne', div_eq_inv_mul,
      ENNReal.ofReal_mul (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht,
      ENNReal.ofReal_coe_nnreal]
  · rw [Set.indicator_of_notMem hxS]
    simp

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ α R hα`. Establish `hsd : selfDualMeasure ψ = haarIntegers F`. Simplify using `[selfDualMeasure, hψ.2.2]`. Rewrite using `[hsd]`. Conclude with `integrableOn_haarIntegers_modulus_rpow hα R`.
-/
theorem integrableOn_modulus_rpow :
    (ForS fun F _ _ _ _ _ _ ψ => ∀ α R : ℝ, 0 < α →
      IntegrableOn (fun y : F => (modulus y : ℝ) ^ (α - 1)) {y | (modulus y : ℝ) ≤ R}
        (selfDualMeasure ψ)) := by
  intro F _ _ _ _ _ _ ψ hψ α R hα
  have hsd : selfDualMeasure ψ = haarIntegers F := by
    simp [selfDualMeasure, hψ.2.2]
  rw [hsd]
  exact integrableOn_haarIntegers_modulus_rpow hα R

end GlobalTheory.CompanionTheory.GJPow
