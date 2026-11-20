import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseReads
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalJumpSetsEqIntegerMultisetsTwistedDualStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

open Classical in

/- English proof (translation)
Introduce `D L C₀ i r ρ π w hw Cx hR h7 hF hJ hP`. Take `⟨ep, hep⟩` from `hJ`. Set `C : Enl D i w hw` to `⟨Cx.LL, Cx.inc⟩`. Establish `hτ₀ : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)` using `⟨((D.nbr i w hw).Kw.1.val).codRestrict Cx.LL.1.toSubalgebra (fun x => Cx.le ((D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x))⟩`. Take `⟨τ₀⟩` from `hτ₀`.

Take `⟨g₀, ρ₀, hr₀, -⟩` from `hep i r hP.good w hw Cx τ₀`. Take `⟨κ, hκ⟩` from `exists_base_reads D.host (D.nbr i w hw).Kw Cx.LL (Br.cEw D.nbr i w hw) (D.naut.iotaQC i) τ₀ g₀ hr₀.1`. Use `⟨if ep then 1 else -1, κ, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), (Continuous fun g => M g) → Continuous (TruncatedSeriesCountingIdentities.locC Cx M)`. Introduce `k M hM`.

Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Establish `h1` using `locC_cont D i M hM w hw Cx (Pi.single b 1)`. Establish `h2` using `(continuous_apply a).comp h1`. Simplify `h2` using `[Function.comp_def, Matrix.mulVec_single]`. Establish `hW : Continuous fun g => WpO D.nd i ρ π g`.

Establish `h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)`. Establish `e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) = fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)`. Use function extensionality and compare the values at `g`. Rewrite using `[map_inv]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(D.nd.chi_cont i 1).comp continuous_inv`. Conclude with `h1.smul hP.contρ`. Use `GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition L C₀ i w hw C r ρ π _ κ hR h7 (hF i w hw Cx).2.2.1 (fun z => (IntermediateField.inclusion Cx.le).commutes z) (fun x => hc _ (rTwO_cont D i r hP.cont x)) (hc _ hW) (fun x => hP.crys w hw Cx x) hP.dec ?_` and prove the remaining obligations. Introduce `τ`.

Take `⟨g, ρ', hrd, hx, hπ⟩` from `hep i r hP.good w hw Cx τ`. Establish `hup : (decide (LJ.TypeU D ep g) = true ↔ LJ.TypeU D ep g)` using `decide_eq_true_iff`. Establish `hs` using `GlobalTheory.T.rationalJumpSets_eq_integerMultisets_twistedDual D i ρ' g ep _ hrd.2 hup`. Use `⟨g, hκ τ g hrd.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `x a ha`.

Conclude with `((hs a).1).1 (((hx x a).2.2.1).1 ha)`. Introduce `a`. Use `((hπ ρ π hP.mem hP.dec a).2.2.2).trans ?_` and prove the remaining obligations. Distinguish the cases in `h : a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep = true then 1 else -1) g)`. Rewrite using `[if_pos ((hs a).2.2 h), if_pos h]`.

Rewrite using `[if_neg (fun h' => h ((hs a).2.1 h')), if_neg h]`.
-/
theorem hodgeTateJumps_coefficientExtension : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  intro D L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  obtain ⟨ep, hep⟩ := hJ
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  have hτ₀ : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) :=
    ⟨((D.nbr i w hw).Kw.1.val).codRestrict Cx.LL.1.toSubalgebra
      (fun x => Cx.le ((D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x))⟩
  obtain ⟨τ₀⟩ := hτ₀
  obtain ⟨g₀, ρ₀, hr₀, -⟩ := hep i r hP.good w hw Cx τ₀
  obtain ⟨κ, hκ⟩ := exists_base_reads D.host (D.nbr i w hw).Kw Cx.LL (Br.cEw D.nbr i w hw)
    (D.naut.iotaQC i) τ₀ g₀ hr₀.1
  refine ⟨if ep then 1 else -1, κ, ?_⟩

  have hc : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), (Continuous fun g => M g) →
      Continuous (TruncatedSeriesCountingIdentities.locC Cx M) := by
    intro k M hM
    refine continuous_matrix fun a b => ?_
    have h1 := locC_cont D i M hM w hw Cx (Pi.single b 1)
    have h2 := (continuous_apply a).comp h1
    simpa [Function.comp_def, Matrix.mulVec_single] using h2
  have hW : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hP.contρ
  refine GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition L C₀ i w hw C r ρ π _ κ hR h7 (hF i w hw Cx).2.2.1
    (fun z => (IntermediateField.inclusion Cx.le).commutes z)
    (fun x => hc _ (rTwO_cont D i r hP.cont x)) (hc _ hW) (fun x => hP.crys w hw Cx x) hP.dec ?_
  intro τ
  obtain ⟨g, ρ', hrd, hx, hπ⟩ := hep i r hP.good w hw Cx τ
  have hup : (decide (LJ.TypeU D ep g) = true ↔ LJ.TypeU D ep g) := decide_eq_true_iff
  have hs := GlobalTheory.T.rationalJumpSets_eq_integerMultisets_twistedDual D i ρ' g ep _ hrd.2 hup
  refine ⟨g, hκ τ g hrd.1, ?_, ?_⟩
  · intro x a ha
    exact ((hs a).1).1 (((hx x a).2.2.1).1 ha)
  · intro a
    refine ((hπ ρ π hP.mem hP.dec a).2.2.2).trans ?_
    by_cases h : a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep = true then 1 else -1) g)
    · rw [if_pos ((hs a).2.2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hs a).2.1 h')), if_neg h]

end GlobalTheory.HTW.Rec
