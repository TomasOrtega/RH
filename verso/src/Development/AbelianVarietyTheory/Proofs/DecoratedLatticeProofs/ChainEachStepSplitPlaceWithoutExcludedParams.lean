import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallEntriesAndStringsAvoidExcludedNormPowersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientNeOneCompletelySplitPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainNS

/- English proof (translation)
Introduce `D c hc S' hS' B hB hBi k hk`. Take `⟨p, hp, -, hpS, v, hv⟩` from `GlobalTheory.SplitChoice.exists_split_prime D (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) 1 (Finset.finite_toSet _) one_ne_zero`. Establish `hvS : v ∉ S'` using `fun h => hpS v (Finset.mem_coe.2 h) hv`. Use `⟨v, hvS, GlobalTheory.SplitPlace.isSplit_of_splitsCompletely D p hp v hv, ?_⟩` and prove the remaining obligations. Introduce `w hw β hβ k' hk'`.

Establish `hrt5 : D.R.r + 5 ≤ D.R.t` using `D.R.rank_add_five_le`. Establish `hrt : D.R.r + 2 ≤ D.R.t` using `by omega`. Establish `hwS : w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))`. Simplify using `[GlobalTheory.LFun.above, hw, hvS]`. Establish `hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal`.

Establish `h` using `hv`. Rewrite `h` using `[← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `h`. Establish `hwc : w.under (𝓞 D.host.F) ∉ c.S` using `fun h => hvS (hw ▸ hS' h)`. Use `set x := GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w with hx`.

Establish `hmem : x⁻¹ * β ∈ GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F` using `D.host.F) (c.chT (k + 1)))⁻¹ w := by`. Simplify using `only [GlobalTheory.LFun.twist, Pi.inv_apply]`. Conclude with `Multiset.mem_map_of_mem _ hβ`. Rewrite `hmem` using `[chainPar_twist_chT]`. Establish `key : ((x⁻¹ * β : ℂˣ) : ℂ) ≠ GlobalTheory.LFun.npow w ((k' : ℂ) / 2)`.

Establish `hN` using `GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers D.host.E w D.R.r D.R.t hrt k' hk'`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Multiset.mem_add, Multiset.mem_sum] at hmem`. Break down `hmem with h | ⟨i, hi, h⟩` into its components or cases. Simplify using `only [GlobalTheory.LFun.twist, Pi.inv_apply] at h`. Take `⟨b, hb, hb'⟩` from `Multiset.mem_map.1 h`.

Rewrite using `[← hb']`. Establish `hb1` using `(hB w hwS).2 b hb`. Establish `hb2` using `(hBi w hwS).2 b⁻¹ (Multiset.mem_map_of_mem _ hb)`. Establish `hu : ‖((GlobalTheory.LFun.val (F` using `D.host.F) (c.μ (k + 1)) w : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _`. Use `hN.1 _ (Units.ne_zero _) ?_ ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]`. Conclude with `hb1`. Rewrite using `[Units.val_mul, mul_inv, norm_mul, Units.val_inv_eq_inv_val, inv_inv, hu, one_mul]`. Rewrite `hb2` using `[Units.val_inv_eq_inv_val]`. Conclude with `hb2`.

Establish `hi'` using `Finset.mem_Icc.1 hi`. Conclude with `hN.2 _ (GlobalTheory.LFun.norm_val _ _) (GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime D c hc i (k + 1) hi'.1 (by omega) (by omega) p hp w hpw hwc) _ h`. Introduce `he`. Apply `key` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]`.

Conclude with `he`.
-/
theorem chainNS_holds : ∀ D : D7, ChainNS D := by
  intro D c hc S' hS' B hB hBi k hk
  obtain ⟨p, hp, -, hpS, v, hv⟩ :=
    GlobalTheory.SplitChoice.exists_split_prime D (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) 1 (Finset.finite_toSet _) one_ne_zero
  have hvS : v ∉ S' := fun h => hpS v (Finset.mem_coe.2 h) hv
  refine ⟨v, hvS, GlobalTheory.SplitPlace.isSplit_of_splitsCompletely D p hp v hv, ?_⟩
  intro w hw β hβ k' hk'
  have hrt5 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt : D.R.r + 2 ≤ D.R.t := by omega
  have hwS : w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    simp [GlobalTheory.LFun.above, hw, hvS]
  have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have h := hv
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h
  have hwc : w.under (𝓞 D.host.F) ∉ c.S := fun h => hvS (hw ▸ hS' h)
  set x := GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w with hx
  have hmem : x⁻¹ * β ∈ GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ w := by
    simp only [GlobalTheory.LFun.twist, Pi.inv_apply]
    exact Multiset.mem_map_of_mem _ hβ
  rw [chainPar_twist_chT] at hmem
  have key : ((x⁻¹ * β : ℂˣ) : ℂ) ≠ GlobalTheory.LFun.npow w ((k' : ℂ) / 2) := by
    have hN := GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers D.host.E w D.R.r D.R.t hrt k' hk'
    simp only [Pi.add_apply, Finset.sum_apply, Multiset.mem_add, Multiset.mem_sum] at hmem
    rcases hmem with h | ⟨i, hi, h⟩
    · simp only [GlobalTheory.LFun.twist, Pi.inv_apply] at h
      obtain ⟨b, hb, hb'⟩ := Multiset.mem_map.1 h
      rw [← hb']
      have hb1 := (hB w hwS).2 b hb
      have hb2 := (hBi w hwS).2 b⁻¹ (Multiset.mem_map_of_mem _ hb)
      have hu : ‖((GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
      refine hN.1 _ (Units.ne_zero _) ?_ ?_
      · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]
        exact hb1
      · rw [Units.val_mul, mul_inv, norm_mul, Units.val_inv_eq_inv_val, inv_inv, hu, one_mul]
        rw [Units.val_inv_eq_inv_val] at hb2
        exact hb2
    · have hi' := Finset.mem_Icc.1 hi
      exact hN.2 _ (GlobalTheory.LFun.norm_val _ _)
        (GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime D c hc i (k + 1) hi'.1 (by omega) (by omega) p hp w hpw hwc) _ h
  intro he
  apply key
  rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]
  exact he

end GlobalTheory.ChainNS
