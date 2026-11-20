import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdInertClosed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix Polynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem keyInert (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - 1 - (x - 1) * (x ^ (2 * n + 1) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - (-1) ^ n * x ^ (-(n : ℤ))) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, he.add_one.neg_one_pow]
    field_simp
    ring
  · rw [ho.neg_one_pow, ho.add_one.neg_one_pow]
    field_simp
    ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Both sides reduce to the same expression. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem fixed_mem_range {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (h2 : Module.finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) (t : K) (ht : σ t = t) :
    ∃ c : k, t = algebraMap k K c := by
  classical
  haveI : FiniteDimensional k K := inferInstance
  haveI : IsGalois k K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[k] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ τ : K ≃ₐ[k] K, τ = AlgEquiv.refl ∨ τ = σ := by
    intro τ
    by_contra h
    push_neg at h
    have h3 : ({AlgEquiv.refl, σ, τ} : Finset (K ≃ₐ[k] K)).card ≤ 2 := hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne, Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)] at h3
    omega
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed t).mpr (fun τ => by
    rcases hall τ with rfl | rfl
    · rfl
    · exact ht)
  exact ⟨c, hc.symm⟩

end PI.OmVe
