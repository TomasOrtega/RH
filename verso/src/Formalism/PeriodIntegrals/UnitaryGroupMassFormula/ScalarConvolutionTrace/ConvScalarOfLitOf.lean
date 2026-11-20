import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem convScalar_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff) (h5 : RankLeOne)
    (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) (hm : GelfandGraevMultOne) :
    ConvScalar := by
  intro F _ _ k ψ₀ hψ V _ _ _ π hπ
  have hu : IsUni k (1 : GL (Fin k) F) :=
    ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_gt hij)]⟩
  have hpsi1 : psiNat ψ₀ (1 : GL (Fin k) F) = 1 := by
    simp only [psiNat, if_pos hu, psiU]
    have hs : superdiag k ((1 : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = 0 := by
      unfold superdiag
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hij : i ≠ j := by
          intro e
          rw [e] at h
          omega
        simp [Matrix.one_apply_ne hij]
      · rfl
    rw [hs, AddChar.map_zero_eq_one]
  have hgam : gam ψ₀ (1 : GL (Fin k) F) =
      (cardU F k : ℂ)⁻¹ * (Fintype.card (GL (Fin k) F) : ℂ) := by
    unfold gam
    simp [hpsi1]
  have hG0 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU0 : (cardU F k : ℂ) ≠ 0 := by
    haveI : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, hu⟩⟩
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdim := h9 F k V π hπ
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
  obtain ⟨c, hc⟩ := h6 F k V π hπ (repGam ψ₀ π) fun g => h2 F k ψ₀ V π g
  have htr := h7 F k ψ₀ V π
  rw [hc, h8 V (projQ ψ₀ π) (h3 F k ψ₀ V π), map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hc, hgam]
  split_ifs with hgen
  · have hne := (h4 F k ψ₀ V π).mp hgen
    have hr1 : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) = 1 := by
      have hle := h5 hm F k ψ₀ hψ V π hπ
      have hpos : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≠ 0 := fun h0 =>
        hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
      omega
    rw [hr1, Nat.cast_one, mul_one] at htr
    have hcv : c = (Fintype.card (GL (Fin k) F) : ℂ) / (Module.finrank ℂ V : ℂ) := by
      rw [eq_div_iff hd0]
      exact htr
    rw [smul_smul, hcv]
    congr 1
    field_simp
  · have hz : projQ ψ₀ π = 0 := by
      by_contra h
      exact hgen ((h4 F k ψ₀ V π).mpr h)
    rw [hz, LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero] at htr
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp htr with h | h
      · exact h
      · exact absurd h hd0
    rw [hc0, zero_smul, smul_zero]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem convScalarOfLit_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff)
    (h5 : RankLeOne) (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) :
    ConvScalarOfLit := by
  exact fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm

end PI.GGConvScalarW
