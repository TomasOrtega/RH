import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSuppStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultipleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

/- English proof (translation)
Introduce `X _ _ p hp N x z ε hN hzx hε`. Take `⟨l, s, hl, hx, hz⟩` from `GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing X N x z hN hzx`. Establish `hs : genericPoint X ∈ nonzeroLocus s` using `(genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx`. Take `⟨m, hm⟩` from `exists_nat_ge ((l : ℚ) / ε)`. Establish `hm0 : 0 < m`.

Establish `: (0 : ℚ) < (l : ℚ) / ε` using `div_pos (by exact_mod_cast hl) hε`. Conclude with `this.trans_le hm` after adjusting the coercions. Take `⟨hE, hQ⟩` from `GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple X p hp N hN.isLB l m s hs hm0`. Use `⟨(l : ℚ) / m, _, by positivity, ?_, hQ, ?_, ?_⟩` and prove the remaining obligations. Establish `hm' : (0 : ℚ) < m` using `by exact_mod_cast hm0`.

Rewrite using `[div_le_iff₀ hm']`. Rewrite `hm` using `[div_le_iff₀ hε]`. Combine the linear relations using `[mul_comm (m : ℚ) ε]`. Conclude with `(GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m x hE hm0).2 (notMem_supp_divOfSec.2 hx)`. Rewrite using `[GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m z hE hm0, notMem_supp_divOfSec]`.

Conclude with `hz`.
-/
theorem GlobalTheory.PairStep.exists_small_ample_through_off : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  intro X _ _ p hp N x z ε hN hzx hε
  obtain ⟨l, s, hl, hx, hz⟩ := GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing X N x z hN hzx
  have hs : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  obtain ⟨m, hm⟩ := exists_nat_ge ((l : ℚ) / ε)
  have hm0 : 0 < m := by
    have : (0 : ℚ) < (l : ℚ) / ε := div_pos (by exact_mod_cast hl) hε
    exact_mod_cast this.trans_le hm
  obtain ⟨hE, hQ⟩ := GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple X p hp N hN.isLB l m s hs hm0
  refine ⟨(l : ℚ) / m, _, by positivity, ?_, hQ, ?_, ?_⟩
  · have hm' : (0 : ℚ) < m := by exact_mod_cast hm0
    rw [div_le_iff₀ hm']
    rw [div_le_iff₀ hε] at hm
    linarith [mul_comm (m : ℚ) ε]
  · exact (GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m x hE hm0).2 (notMem_supp_divOfSec.2 hx)
  · rw [GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m z hE hm0, notMem_supp_divOfSec]
    exact hz
