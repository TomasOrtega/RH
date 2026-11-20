import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section DualMono

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem rA_le_of_subset {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem div_mem_rA_of_mem {J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ J) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x J :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_omA_iff_mul {I : Finset (Fin (d + 1))} {y : F} :
    y ∈ omA k x I ↔ ∀ i ∈ I, (∏ j, x i / x j) * y ∈ rA k x I := by
  simp [omA, Submodule.mem_iInf]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mul_mem_omA_of_mem_rA {J : Finset (Fin (d + 1))} {r y : F} (hr : r ∈ rA k x J) (hy : y ∈ omA k x J) :
    r * y ∈ omA k x J := by
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  rw [mul_left_comm]
  exact (rA k x J).mul_mem hr (hy i hi)

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Clear the denominators using the available nonvanishing facts.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem omA_le_of_subset (hx : ∀ i, x i ≠ 0) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (h : I ⊆ J) :
    omA k x I ≤ omA k x J := by
  obtain ⟨i₀, hi₀⟩ := hI
  intro y hy
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  have e : (∏ j, x i / x j) = (x i / x i₀) ^ (d + 1) * ∏ j, x i₀ / x j := by
    have hc : (x i / x i₀) ^ (d + 1) = ∏ _j : Fin (d + 1), (x i / x i₀) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [hx i₀, hx j]
  rw [e, mul_assoc]
  exact (rA k x J).mul_mem ((rA k x J).pow_mem (div_mem_rA_of_mem (h hi₀) i) _) (rA_le_of_subset h (hy i₀ hi₀))

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

end DualMono

end GlobalTheory.PD
