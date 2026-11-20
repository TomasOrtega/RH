import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

/- English proof (translation)
Introduce `F _ _ k ψ₀ hψ V _ _ _ π hπ`. Establish `hu : IsUni k (1 : GL (Fin k) F)` using `⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_gt hij)]⟩`. Establish `hpsi1 : psiNat ψ₀ (1 : GL (Fin k) F) = 1`. Simplify using `only [psiNat, if_pos hu, psiU]`. Establish `hs : superdiag k ((1 : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = 0`.

Unfold `superdiag`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `hij : i ≠ j`. Introduce `e`.

Rewrite `h` using `[e]`. Use linear arithmetic over natural numbers and integers. Simplify using `[Matrix.one_apply_ne hij]`. Both sides reduce to the same expression. Rewrite using `[hs, AddChar.map_zero_eq_one]`.

Establish `hgam : gam ψ₀ (1 : GL (Fin k) F) = (cardU F k : ℂ)⁻¹ * (Fintype.card (GL (Fin k) F) : ℂ)`. Unfold `gam`. Simplify using `[hpsi1]`. Establish `hG0 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hU0 : (cardU F k : ℂ) ≠ 0` using `by haveI : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, hu⟩⟩`.

Conclude with `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hdim` using `h9 F k V π hπ`. Establish `hd0 : (Module.finrank ℂ V : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hdim.ne'`. Take `⟨c, hc⟩` from `h6 F k V π hπ (repGam ψ₀ π) fun g => h2 F k ψ₀ V π g`. Establish `htr` using `h7 F k ψ₀ V π`.

Rewrite `htr` using `[hc, h8 V (projQ ψ₀ π) (h3 F k ψ₀ V π), map_smul, LinearMap.trace_id, smul_eq_mul]`. Rewrite using `[hc, hgam]`. Use `split_ifs with hgen`. Establish `hne` using `(h4 F k ψ₀ V π).mp hgen`. Establish `hr1 : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) = 1`.

Establish `hle` using `h5 hm F k ψ₀ hψ V π hπ`. Establish `hpos : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≠ 0` using `fun h0 => hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))`. Use linear arithmetic over natural numbers and integers. Rewrite `htr` using `[hr1, Nat.cast_one, mul_one]`. Establish `hcv : c = (Fintype.card (GL (Fin k) F) : ℂ) / (Module.finrank ℂ V : ℂ)`.

Rewrite using `[eq_div_iff hd0]`. Conclude with `htr`. Rewrite using `[smul_smul, hcv]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `hz : projQ ψ₀ π = 0`. Assume the negation of the conclusion as `h`. Conclude with `hgen ((h4 F k ψ₀ V π).mpr h)`. Rewrite `htr` using `[hz, LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero]`. Establish `hc0 : c = 0`.

Break down `mul_eq_zero.mp htr with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hd0`. Rewrite using `[hc0, zero_smul, smul_zero]`.
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
Conclude with `fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm`.
-/
theorem convScalarOfLit_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff)
    (h5 : RankLeOne) (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) :
    ConvScalarOfLit := by
  exact fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm

end PI.GGConvScalarW
