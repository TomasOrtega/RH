import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow

open Matrix Filter Topology

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem val_lt_exp_of_dvdPow_succ {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {N : ℕ} (hx : DvdPow ϖ (N + 1) x) : Valued.v x < WithZero.exp (-(N : ℤ)) := by
  obtain ⟨b, hb, hxb⟩ := hx
  rw [hxb, map_mul, map_pow, hϖ]
  calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
        mul_le_mul' le_rfl hb
    _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
    _ < WithZero.exp (-(N : ℤ)) := WithZero.exp_lt_exp.2 (by push_cast; omega)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isClosed_dvdPow_sub {ϖ : L} (h0 : ϖ ≠ 0) (m : ℕ) (c : L) : IsClosed {x : L | DvdPow ϖ m (x - c)} := by
  have hp : ϖ ^ m ≠ 0 := pow_ne_zero _ h0
  have he : {x : L | DvdPow ϖ m (x - c)} =
      (fun x => (ϖ ^ m)⁻¹ * (x - c)) ⁻¹' ((Valued.v (R := L)).integer : Set L) := by
    ext x
    constructor
    · rintro ⟨b, hb, hxb⟩
      show Valued.v ((ϖ ^ m)⁻¹ * (x - c)) ≤ 1
      rw [hxb, inv_mul_cancel_left₀ hp]; exact hb
    · intro hx
      exact ⟨(ϖ ^ m)⁻¹ * (x - c), hx, by rw [mul_inv_cancel_left₀ hp]⟩
  rw [he]
  exact (Valued.isClosed_integer L).preimage (by fun_prop)

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_limit_dvdPow (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (a : ℕ → L) (ha : ∀ k, DvdPow ϖ (k + 1) (a (k + 1) - a k)) :
    ∃ b : L, ∀ k, DvdPow ϖ (k + 1) (b - a k) := by
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hint : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ]
    show WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
    exact WithZero.exp_le_exp.2 (by omega)
  have hstep : ∀ k m, k ≤ m → DvdPow ϖ (k + 1) (a m - a k) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => rw [sub_self]; exact dvdPow_zero ϖ _
    | succ m hkm ih =>
      have := dvdPow_add (dvdPow_mono hint (Nat.succ_le_succ hkm) (ha m)) ih
      rwa [sub_add_sub_cancel] at this
  have hc : CauchySeq a := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by
      simp
    obtain ⟨e, he⟩ : ∃ e, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp e :=
      ⟨_, (WithZero.exp_log hγ).symm⟩
    refine ⟨(-e).toNat, fun m hm n hn => ?_⟩
    show Valued.v.restrict (a n - a m) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, he]
    have h1 := dvdPow_sub (hstep _ n hn) (hstep _ m hm)
    rw [sub_sub_sub_cancel_right] at h1
    refine (val_lt_exp_of_dvdPow_succ hϖ h1).trans_le (WithZero.exp_le_exp.2 ?_)
    have := Int.self_le_toNat (-e)
    omega
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨b, fun k => ?_⟩
  exact (isClosed_dvdPow_sub h0 (k + 1) (a k)).mem_of_tendsto hb
    (eventually_atTop.2 ⟨k, fun m hm => hstep k m hm⟩)

end GlobalTheory.Hk3.IntWittBase
