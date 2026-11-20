import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ZetaValUnique

/- English proof (translation)
Establish `ho : IsOpen ({1}ᶜ : Set ℂ)` using `isOpen_compl_singleton`. Establish `hc : IsPreconnected ({1}ᶜ : Set ℂ)` using `(isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected`. Use `(h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc (z₀ := 2) (by norm_num) ?_` and prove the remaining obligations. Establish `hh : IsOpen {s : ℂ | 1 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs`.

Conclude with `(h.2 s hs).unique (h'.2 s hs)`.
-/
theorem classZeta_eqOn {E : Type} [Field E] [NumberField E] {C : ClassGroup (GlobalTheory.CMVal.OF E)} {Z Z' : ℂ → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc
    (z₀ := 2) (by norm_num) ?_
  have hh : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

/- English proof (translation)
Introduce `E _ _ k hk z z' hz hz'`. Use function extensionality and compare the values at `C`. Take `⟨Z, hZ, hZv⟩` from `hz C`. Take `⟨Z', hZ', hZv'⟩` from `hz' C`. Establish `hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ)`.

Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_self, Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers. Use `classZeta_eqOn hZ hZ' hne` as an intermediate fact. Rewrite `this` using `[hZv, hZv']`. Conclude with `this` after adjusting the coercions.
-/
theorem classZetaVals_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k →
    ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z →
      GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  intro E _ _ k hk z z' hz hz'
  funext C
  obtain ⟨Z, hZ, hZv⟩ := hz C
  obtain ⟨Z', hZ', hZv'⟩ := hz' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_self, Nat.cast_eq_zero]
    omega
  have := classZeta_eqOn hZ hZ' hne
  rw [hZv, hZv'] at this
  exact_mod_cast this

end GlobalTheory.ZetaValUnique
