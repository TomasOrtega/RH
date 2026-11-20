import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.IntMatBound

variable (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L)

def boundSub (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (n : ℕ) (m : ℤ) :
    Submodule K.O (Matrix (Fin n) (Fin n) K.E) where
  carrier := {X | ∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m}
  add_mem' := by
    intro X Y hX hY i j
    simp only [Matrix.add_apply, map_add]
    exact Valuation.map_add_le _ (hX i j) (hY i j)
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c X hX i j
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, Valuation.map_mul]
    have h1 : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (he _).1 ⟨c, rfl⟩
    calc Valued.v (e (algebraMap K.O K.E c)) * Valued.v (e (X i j)) ≤ 1 * WithZero.exp m :=
          mul_le_mul' h1 (hX i j)
      _ = WithZero.exp m := one_mul _

/- English proof (translation)
Distinguish the cases in `h : Valued.v (e x) = 0`. Conclude with `⟨0, by rw [h]; exact zero_le'⟩`. Conclude with `⟨(Valued.v (e x)).log, (WithZero.exp_log h).ge⟩`.
-/
theorem exists_bound (x : K.E) : ∃ m : ℤ, Valued.v (e x) ≤ WithZero.exp m := by
  by_cases h : Valued.v (e x) = 0
  · exact ⟨0, by rw [h]; exact zero_le'⟩
  · exact ⟨(Valued.v (e x)).log, (WithZero.exp_log h).ge⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible K.O`. Use `⟨ϖ, hϖ.ne_zero, ?_⟩` and prove the remaining obligations. Use `set w := Valued.v (e (algebraMap K.O K.E ϖ)) with hw`. Establish `hE : algebraMap K.O K.E ϖ ≠ 0`. Introduce `h0`.

Conclude with `hϖ.ne_zero (IsFractionRing.injective K.O K.E (by simpa using h0))`. Establish `w0 : w ≠ 0`. Rewrite using `[hw, Valuation.ne_zero_iff]`. Conclude with `(map_ne_zero e).2 hE`. Establish `w1 : w ≤ 1` using `(he _).1 ⟨ϖ, rfl⟩`.

Establish `wne : w ≠ 1`. Introduce `h1`. Establish `: Valued.v (e (algebraMap K.O K.E ϖ)⁻¹) ≤ 1`. Rewrite using `[map_inv₀, map_inv₀, ← hw, h1, inv_one]`. Take `⟨u, hu⟩` from `(he _).2 this`.

Apply `hϖ.not_isUnit` to reduce the goal to its premises. Use `IsUnit.of_mul_eq_one (b := u) (IsFractionRing.injective K.O K.E ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hu, map_one, mul_inv_cancel₀ hE]`. Establish `wlt : w < 1` using `lt_of_le_of_ne w1 wne`. Establish `hlog : w.log < 0`.

Rewrite using `[← WithZero.exp_lt_exp, WithZero.exp_log w0, WithZero.exp_zero]`. Conclude with `wlt`. Rewrite using `[← WithZero.exp_log w0, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_unif (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) :
    ∃ ϖ : K.O, ϖ ≠ 0 ∧ Valued.v (e (algebraMap K.O K.E ϖ)) ≤ WithZero.exp (-1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  refine ⟨ϖ, hϖ.ne_zero, ?_⟩
  set w := Valued.v (e (algebraMap K.O K.E ϖ)) with hw
  have hE : algebraMap K.O K.E ϖ ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (IsFractionRing.injective K.O K.E (by simpa using h0))
  have w0 : w ≠ 0 := by
    rw [hw, Valuation.ne_zero_iff]
    exact (map_ne_zero e).2 hE
  have w1 : w ≤ 1 := (he _).1 ⟨ϖ, rfl⟩
  have wne : w ≠ 1 := by
    intro h1
    have : Valued.v (e (algebraMap K.O K.E ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, map_inv₀, ← hw, h1, inv_one]
    obtain ⟨u, hu⟩ := (he _).2 this
    apply hϖ.not_isUnit
    refine IsUnit.of_mul_eq_one (b := u) (IsFractionRing.injective K.O K.E ?_)
    rw [map_mul, hu, map_one, mul_inv_cancel₀ hE]
  have wlt : w < 1 := lt_of_le_of_ne w1 wne
  have hlog : w.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log w0, WithZero.exp_zero]
    exact wlt
  rw [← WithZero.exp_log w0, WithZero.exp_le_exp]
  omega

end GlobalTheory.IntMatBound

open GlobalTheory.IntMatBound in
/- English proof (translation)
Introduce `K L _ _ e he n M`. Prove the components needed by the constructor for the conclusion. Introduce `hM`. Take `⟨s, hs⟩` from `hM.fg_adjoin_singleton`. Establish `hb : ∀ p : s × Fin n × Fin n, ∃ m : ℤ, Valued.v (e ((p.1 : Matrix (Fin n) (Fin n) K.E) p.2.1 p.2.2)) ≤ WithZero.exp m` using `fun p => exists_bound K e _`.

Use `choose f hf using hb`. Take `⟨m, hm⟩` from `(Set.finite_range f).bddAbove`. Use `⟨m, fun k i j => ?_⟩` and prove the remaining obligations. Establish `hle : Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) ≤ boundSub K e he n m`. Rewrite using `[Submodule.span_le]`.

Introduce `X hX i j`. Conclude with `(hf ⟨⟨X, hX⟩, i, j⟩).trans (WithZero.exp_le_exp.2 (hm ⟨_, rfl⟩))`. Establish `hk : M ^ k ∈ Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E))`. Rewrite using `[hs]`. Conclude with `Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O M) k`.

Conclude with `hle hk i j`. Introduce and unpack `⟨m, hm⟩`. Take `⟨ϖ, hϖ0, hϖ⟩` from `exists_unif K e he`. Establish `hE : algebraMap K.O K.E ϖ ≠ 0`. Introduce `h0`.

Conclude with `hϖ0 (IsFractionRing.injective K.O K.E (by simpa using h0))`. Use `set N := m.toNat with hN`. Use `set y : K.E := (algebraMap K.O K.E ϖ)⁻¹ ^ N with hy`. Use `set S : Submodule K.O (Matrix (Fin n) (Fin n) K.E) := Submodule.span K.O (Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 y) with hS`. Establish `hmem : ∀ X : Matrix (Fin n) (Fin n) K.E, (∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m) → X ∈ S`.

Introduce `X hX`. Rewrite using `[Matrix.matrix_eq_sum_single X]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `hv : Valued.v (e ((algebraMap K.O K.E ϖ) ^ N * X i j)) ≤ 1`. Rewrite using `[map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[WithZero.exp_le_exp, nsmul_eq_mul, hN]`. Use linear arithmetic over natural numbers and integers. Use `_ = 1 := WithZero.exp_zero`. Take `⟨c, hc⟩` from `(he _).2 hv`.

Establish `: Matrix.single i j (X i j) = c • Matrix.single i j y`. Rewrite using `[Matrix.smul_single, Algebra.smul_def, hc, hy, inv_pow, mul_assoc, mul_comm (X i j), ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hE), one_mul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)`. Establish `hSfg : S.FG` using `Submodule.fg_span (Set.finite_range _)`.

Establish `hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {M}) ≤ S`. Rewrite using `[Algebra.adjoin_eq_span, Submodule.span_le]`. Introduce and unpack `_ hx`. Take `⟨k, rfl⟩` from `Submonoid.mem_closure_singleton.1 hx`. Conclude with `hmem _ (hm k)`.

Use `haveI := isNoetherian_of_fg_of_noetherian S hSfg`. Use `haveI := isNoetherian_of_le hle`. Establish `hfg : (Subalgebra.toSubmodule (Algebra.adjoin K.O {M})).FG` using `Module.Finite.iff_fg.mp inferInstance`. Conclude with `IsIntegral.of_mem_of_fg _ hfg M (Algebra.self_mem_adjoin_singleton K.O M)`.
-/
theorem GlobalTheory.IntMatBound.isIntegral_iff_bounded : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  intro K L _ _ e he n M
  constructor
  · intro hM
    obtain ⟨s, hs⟩ := hM.fg_adjoin_singleton
    have hb : ∀ p : s × Fin n × Fin n, ∃ m : ℤ, Valued.v (e ((p.1 : Matrix (Fin n) (Fin n) K.E) p.2.1 p.2.2)) ≤ WithZero.exp m :=
      fun p => exists_bound K e _
    choose f hf using hb
    obtain ⟨m, hm⟩ := (Set.finite_range f).bddAbove
    refine ⟨m, fun k i j => ?_⟩
    have hle : Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) ≤ boundSub K e he n m := by
      rw [Submodule.span_le]
      intro X hX i j
      exact (hf ⟨⟨X, hX⟩, i, j⟩).trans (WithZero.exp_le_exp.2 (hm ⟨_, rfl⟩))
    have hk : M ^ k ∈ Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) := by
      rw [hs]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O M) k
    exact hle hk i j
  · rintro ⟨m, hm⟩
    obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif K e he
    have hE : algebraMap K.O K.E ϖ ≠ 0 := by
      intro h0
      exact hϖ0 (IsFractionRing.injective K.O K.E (by simpa using h0))
    set N := m.toNat with hN
    set y : K.E := (algebraMap K.O K.E ϖ)⁻¹ ^ N with hy
    set S : Submodule K.O (Matrix (Fin n) (Fin n) K.E) :=
      Submodule.span K.O (Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 y) with hS
    have hmem : ∀ X : Matrix (Fin n) (Fin n) K.E, (∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m) → X ∈ S := by
      intro X hX
      rw [Matrix.matrix_eq_sum_single X]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      have hv : Valued.v (e ((algebraMap K.O K.E ϖ) ^ N * X i j)) ≤ 1 := by
        rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (e (algebraMap K.O K.E ϖ)) ^ N * Valued.v (e (X i j))
            ≤ WithZero.exp (-1) ^ N * WithZero.exp m := mul_le_mul' (pow_le_pow_left' hϖ N) (hX i j)
          _ = WithZero.exp (N • (-1 : ℤ) + m) := by rw [WithZero.exp_add, WithZero.exp_nsmul]
          _ ≤ WithZero.exp 0 := by
              rw [WithZero.exp_le_exp, nsmul_eq_mul, hN]
              omega
          _ = 1 := WithZero.exp_zero
      obtain ⟨c, hc⟩ := (he _).2 hv
      have : Matrix.single i j (X i j) = c • Matrix.single i j y := by
        rw [Matrix.smul_single, Algebra.smul_def, hc, hy, inv_pow, mul_assoc, mul_comm (X i j), ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hE), one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hSfg : S.FG := Submodule.fg_span (Set.finite_range _)
    have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {M}) ≤ S := by
      rw [Algebra.adjoin_eq_span, Submodule.span_le]
      rintro _ hx
      obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
      exact hmem _ (hm k)
    haveI := isNoetherian_of_fg_of_noetherian S hSfg
    haveI := isNoetherian_of_le hle
    have hfg : (Subalgebra.toSubmodule (Algebra.adjoin K.O {M})).FG := Module.Finite.iff_fg.mp inferInstance
    exact IsIntegral.of_mem_of_fg _ hfg M (Algebra.self_mem_adjoin_singleton K.O M)
