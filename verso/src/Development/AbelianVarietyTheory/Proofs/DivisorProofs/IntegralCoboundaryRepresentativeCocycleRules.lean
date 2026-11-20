import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

/- English proof (translation)
Introduce `a b h`. Use extensionality with `α`. Apply `hι` to reduce the goal to its premises. Rewrite using `[← coeff_map, ← coeff_map, h]`.
-/
theorem map_inj_of_inj {σ O E : Type} [CommRing O] [CommRing E] (ι : O →+* E)
    (hι : Function.Injective ι) : Function.Injective (map ι : MvPowerSeries σ O → MvPowerSeries σ E) := by
  intro a b h
  ext α
  apply hι
  rw [← coeff_map, ← coeff_map, h]

/- English proof (translation)
Introduce `O E _ _ _ d μ hμ hι f κ hκ`. Use `set ι := algebraMap O E with hιdef`. Establish `inj2` using `map_inj_of_inj (σ := Fin d ⊕ Fin d) ι hι`. Establish `inj3` using `map_inj_of_inj (σ := Fin d ⊕ (Fin d ⊕ Fin d)) ι hι`. Establish `inj1` using `map_inj_of_inj (σ := Fin d) ι hι`.

Take `⟨hlawE, hnm⟩` from `GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E ι`. Take `⟨hcob1, hcob2, hswap, -, hpull⟩` from `GlobalTheory.T.map_coboundary_swap_pullback_commute O d μ hμ.const E ι`. Establish `hupμ : up E μ = fun i => map ι (μ i)` using `rfl`. Establish `hconstE : ∀ i, constantCoeff (up E μ i) = 0` using `hlawE.const`. Establish `hcocE` using `(GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt E d (up E μ) hconstE f).2.2.2.2.2 hlawE`.

Establish `hsmul : ∀ {σ : Type} (k : ℕ) (g : MvPowerSeries σ O), map ι ((k : O) • g) = (k : E) • map ι g`. Introduce `σ k g`. Use extensionality with `α`. Simplify using `[coeff_map, map_natCast]`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Apply `inj3` to reduce the goal to its premises. Rewrite using `[hcob2, ← hupμ, hκ, hcocE.1, map_zero]`. Apply `inj2` to reduce the goal to its premises. Rewrite using `[hswap, hκ, hcocE.2]`. Introduce `hf`.

Apply `hι` to reduce the goal to its premises. Establish `h1 : ι (constantCoeff κ) = constantCoeff (map ι κ)`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]`. Rewrite using `[h1, hκ, map_zero]`. Unfold `cob1 inL inR`.

Rewrite using `[map_sub, map_sub, GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero hconstE, GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _), GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _), hf]`. Simplify using the standard rewrite rules. Introduce `n s hs`. Establish `hnc : ∀ i, constantCoeff (nmul μ n i) = 0` using `fun i => (hnm n i).1`. Establish `hupn : up E (nmul μ n) = fun i => map ι (nmul μ n i)` using `rfl`.

Take `⟨hpl, hsb⟩` from `hpull (nmul μ n) hnc`. Take `⟨hd1, -⟩` from `GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f 0 n`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `inj2` to reduce the goal to its premises. Rewrite using `[hcob1, ← hupμ, hs, hd1, map_sub, hsmul, hpl, hκ, ← hupn]`.

Introduce `m t u ht hu`. Take `⟨-, hd2⟩` from `GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f m n`. Apply `inj1` to reduce the goal to its premises. Rewrite using `[hu, hd2, map_add, hsmul, hsb, ← hupn, hs, ht]`.
-/
theorem integral_cob_defect_rules : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → Function.Injective (algebraMap O E) → ∀ (f : MvPowerSeries (Fin d) E) (κ : MvPowerSeries (Fin d ⊕ Fin d) O), map (algebraMap O E) κ = cob1 (up E μ) f → IsCoc μ κ ∧ (constantCoeff f = 0 → constantCoeff κ = 0) ∧ ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect μ n f → cob1 μ s = (n : O) • κ - pull2 (nmul μ n) κ ∧ ∀ (m : ℕ) (t u : MvPowerSeries (Fin d) O), map (algebraMap O E) t = defect μ m f → map (algebraMap O E) u = defect μ (m * n) f → u = (m : O) • s + subst (nmul μ n) t := by
  intro O E _ _ _ d μ hμ hι f κ hκ
  set ι := algebraMap O E with hιdef
  have inj2 := map_inj_of_inj (σ := Fin d ⊕ Fin d) ι hι
  have inj3 := map_inj_of_inj (σ := Fin d ⊕ (Fin d ⊕ Fin d)) ι hι
  have inj1 := map_inj_of_inj (σ := Fin d) ι hι
  obtain ⟨hlawE, hnm⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E ι
  obtain ⟨hcob1, hcob2, hswap, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d μ hμ.const E ι
  have hupμ : up E μ = fun i => map ι (μ i) := rfl
  have hconstE : ∀ i, constantCoeff (up E μ i) = 0 := hlawE.const
  have hcocE := (GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt E d (up E μ) hconstE f).2.2.2.2.2 hlawE
  have hsmul : ∀ {σ : Type} (k : ℕ) (g : MvPowerSeries σ O), map ι ((k : O) • g) = (k : E) • map ι g := by
    intro σ k g
    ext α
    simp [coeff_map, map_natCast]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply inj3
    rw [hcob2, ← hupμ, hκ, hcocE.1, map_zero]
  · apply inj2
    rw [hswap, hκ, hcocE.2]
  · intro hf
    apply hι
    have h1 : ι (constantCoeff κ) = constantCoeff (map ι κ) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rw [h1, hκ, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero hconstE,
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _),
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _), hf]
    simp
  · intro n s hs
    have hnc : ∀ i, constantCoeff (nmul μ n i) = 0 := fun i => (hnm n i).1
    have hupn : up E (nmul μ n) = fun i => map ι (nmul μ n i) := rfl
    obtain ⟨hpl, hsb⟩ := hpull (nmul μ n) hnc
    obtain ⟨hd1, -⟩ := GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f 0 n
    refine ⟨?_, ?_⟩
    · apply inj2
      rw [hcob1, ← hupμ, hs, hd1, map_sub, hsmul, hpl, hκ, ← hupn]
    · intro m t u ht hu
      obtain ⟨-, hd2⟩ := GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f m n
      apply inj1
      rw [hu, hd2, map_add, hsmul, hsb, ← hupn, hs, ht]

end GlobalTheory.QLog
