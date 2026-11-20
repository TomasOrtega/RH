import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

/- English proof (translation)
Introduce `k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf`. Use `hpp` as an intermediate fact. Take `⟨f, hfp, hfq⟩` from `hf`. Take `⟨j, hj⟩` from `hrel`. Establish `hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞)`.

Rewrite using `[← hx.dim]`. Use `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_` and prove the remaining obligations. Apply `mem_nonZeroDivisors_of_ne_zero` to reduce the goal to its premises. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Rewrite using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hfp`. Establish `hnf : ¬ IsField (Poly k N ⧸ pp)`. Introduce `hF`. Take `⟨v, hv⟩` from `hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j)) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective v`.

Rewrite `hv` using `[← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq]`. Establish `h0` using `hhom _ hv 0`. Rewrite `h0` using `[homogeneousComponent_zero]`. Establish `h1 : (1 : Poly k N) ∈ pp`. Establish `hc : coeff 0 (X j * g - 1 : Poly k N) = -1`.

Express the relevant statement in the definitionally equal form `constantCoeff (X j * g - 1 : Poly k N) = -1`. Simplify using the standard rewrite rules. Rewrite `h0` using `[hc, map_neg, map_one]`. Simplify using `using pp.neg_mem h0`. Conclude with `hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.

Establish `hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0`. Introduce `h0`. Establish `: Ring.KrullDimLE 0 (Poly k N ⧸ pp)` using `(ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0`. Conclude with `hnf Ring.KrullDimLE.isField_of_isDomain`. Establish `hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp)` using `ringKrullDim_nonneg_of_nontrivial`.

Rewrite `hup` using `[← WithBot.coe_one, ← WithBot.coe_natCast]`. Generalize the expression as in `hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => exact absurd hnn (by simp)`. Consider the case `coe D`.

Proceed by induction on `D using ENat.recTopCoe with`. Consider the case `top`. Rewrite `hup` using `[← WithBot.coe_add, WithBot.coe_le_coe, top_add]`. Conclude with `absurd hup (by simp)`. Consider the case `coe n`.

Take `⟨e, rfl⟩ : ∃ e, n = e + 1` from `⟨n - 1, by`. Establish `: n ≠ 0` using `by rintro rfl; exact hne0 rfl`. Use the proof step `omega⟩`. Use `⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩` and prove the remaining obligations. Rewrite `hup` using `[← WithBot.coe_add, WithBot.coe_le_coe]`.

Establish `: ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hup`. Use `Nat.cast_le.mp this` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem SubvarDrop.proof : SubvarDrop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf
  have := hpp
  obtain ⟨f, hfp, hfq⟩ := hf
  obtain ⟨j, hj⟩ := hrel

  have hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hx.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hfp

  have hnf : ¬ IsField (Poly k N ⧸ pp) := by
    intro hF
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j))
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq] at hv
    have h0 := hhom _ hv 0
    rw [homogeneousComponent_zero] at h0
    have h1 : (1 : Poly k N) ∈ pp := by
      have hc : coeff 0 (X j * g - 1 : Poly k N) = -1 := by
        change constantCoeff (X j * g - 1 : Poly k N) = -1; simp
      rw [hc, map_neg, map_one] at h0
      simpa using pp.neg_mem h0
    exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ pp) := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_nonneg_of_nontrivial

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe n =>
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hne0 rfl
        omega⟩
      refine ⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have : ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have := Nat.cast_le.mp this
      omega

end GroundTheory.Heights₂.Heights.Kleiman
