import Formalism.GaussJetBounds.FrameJetEval
import Formalism.GaussJetBounds.GaussJetProofs.Generic
import Formalism.GaussJetBounds.GaussJetProofs.GField
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
Introduce `l _ d N0 N1 _ hl3 hd hde K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size hnu1 hnu2 hsize a ha hsa hthr n`. Establish `hlp : l.Prime` using `Fact.out`. Take `⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩` from `residuallyGenericExists l (ZMod d × Fin N0 × Fin N0)`. Use `hult` as an intermediate fact. Use `hchar` as an intermediate fact.

Establish `hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖` using `by rw [← map_natCast φ, hφ]`. Establish `hl1 : ‖(l : ℂ_[l])‖ < 1`. Establish `h` using `norm_intCast_padicComplex l (l : ℤ)`. Rewrite `h` using `[Int.cast_natCast, Int.cast_natCast]`. Rewrite using `[h]`.

Conclude with `Padic.norm_p_lt_one`. Establish `hN0 : 0 < N0`. Establish `h0 : 0 ≤ Real.logb l a` using `Real.logb_nonneg (by exact_mod_cast hlp.one_lt) (by exact_mod_cast ha)`. Establish `h1 : (0 : ℝ) < N0` using `by linarith`. Conclude with `h1` after adjusting the coercions.

Establish `hnu1a : ∀ s, nu1 s ≤ a` using `fun s => le_trans (by`. Rewrite using `[hnu1, hsize]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨J, lab, m, hinj, hlab, hJ, hm⟩` from `hL l d N0 hlp.two_le TT nu1 size a ha hnu1a hsa hthr`. Take `⟨hT1, hT2, hT3, hT4⟩` from `hT ℂ_[l] K φ hφ l d N0 N1 K0 ζ be`.

Take `⟨hg0', hg'⟩` from `hT3 g hg0 hg`. Apply the tactic sequence `have hA := theorem_A_generic.{0} K l d N0 N1 hlp hl3 hd hde (hnl ▸ hl1) hN0 (K0.map φ) (hT1 hK0) (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) _ hg0' hg' _ (hT4 U hU) (φ ε) (by rcases hε with rfl | rfl <;> simp) TT colN p hp hp1 I Y hgen nu1 nu2 size hnu1 hnu2 hsize a ha hs …`. Rewrite `hA` using `[← hF ℂ_[l] K φ d N0 N1 g U ε be hg0 (asmS_cc_be hbe.2.2.1) colN p hp I (genFrame TT l m Y), hnl]`. Use `le_trans ?_ hA` and prove the remaining obligations. Establish `hk : genFrame TT l m Y = fun y => Y y ^ (if y.1 ∈ TT ∧ y.2.1.val = 0 then l ^ m else 1)`.

Use function extensionality and compare the values at `y`. Unfold `genFrame`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hk]`. Use `hG ℂ_[l] K φ _ Y hgauss _ (fun y => ?_) _ n` and prove the remaining obligations.

Use `split_ifs`. Conclude with `pow_ne_zero _ hlp.ne_zero`. Conclude with `one_ne_zero`.
-/
theorem thmAGauss_of (hT : TransferB) (hF : FrameJetEval) (hL : LabelsExist) (hG : GaussPow) :
    ThmAGauss := by
  intro l _ d N0 N1 _ hl3 hd hde K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize a ha hsa hthr n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (ZMod d × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hN0 : 0 < N0 := by
    have h0 : 0 ≤ Real.logb l a :=
      Real.logb_nonneg (by exact_mod_cast hlp.one_lt) (by exact_mod_cast ha)
    have h1 : (0 : ℝ) < N0 := by linarith
    exact_mod_cast h1
  have hnu1a : ∀ s, nu1 s ≤ a := fun s => le_trans (by
    rw [hnu1, hsize]
    calc colN s = ∑ _c : Fin (colN s), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hp1 s c) (hsa s)
  obtain ⟨J, lab, m, hinj, hlab, hJ, hm⟩ := hL l d N0 hlp.two_le TT nu1 size a ha hnu1a hsa hthr
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hT ℂ_[l] K φ hφ l d N0 N1 K0 ζ be
  obtain ⟨hg0', hg'⟩ := hT3 g hg0 hg
  have hA := theorem_A_generic.{0} K l d N0 N1 hlp hl3 hd hde (hnl ▸ hl1) hN0 (K0.map φ) (hT1 hK0)
    (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) _ hg0' hg' _ (hT4 U hU) (φ ε)
    (by rcases hε with rfl | rfl <;> simp) TT colN p hp hp1 I Y hgen nu1 nu2 size hnu1 hnu2 hsize
    a ha hsa J lab hinj hlab hJ m hm
  rw [← hF ℂ_[l] K φ d N0 N1 g U ε be hg0 (asmS_cc_be hbe.2.2.1) colN p hp I (genFrame TT l m Y),
    hnl] at hA
  refine le_trans ?_ hA
  have hk : genFrame TT l m Y =
      fun y => Y y ^ (if y.1 ∈ TT ∧ y.2.1.val = 0 then l ^ m else 1) := by
    funext y
    unfold genFrame
    split_ifs <;> simp
  rw [hk]
  refine hG ℂ_[l] K φ _ Y hgauss _ (fun y => ?_) _ n
  split_ifs
  · exact pow_ne_zero _ hlp.ne_zero
  · exact one_ne_zero

end Formalism.DworkPowerSeriesWeights
