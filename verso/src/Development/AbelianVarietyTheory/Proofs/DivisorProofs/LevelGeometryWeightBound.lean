import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Formalism.LocalToGlobal.ProjectiveLattices.TieReadSS
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.BergComp

open MeasureTheory

/- English proof (translation)
Introduce `hT D j H Dw l Xo c U dict hL σ hσ G hG w hw hsp Z y hy`. Establish `hU : IsUnf (U σ)` using `hL.unf σ hσ`. Take `⟨Kf, th, hr, -, -, hDU, -⟩` from `hL.dictU σ hσ`. Establish `hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom` using `Formalism.L2.Pj.dict_dom_of hDU`. Use `set A := AllWt.framesOn (U σ) Z with hA`.

Use `set S : Set (U σ).Comp := {k | ∃ f, (⟨k, f⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ A} with hS`. Establish `key : ∀ g, dict σ g ∈ A ↔ (dict σ g).1 ∈ S` using `fun g => ⟨fun h => ⟨_, h⟩, fun ⟨f, hf⟩ => GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ f _ (hdom g) hf⟩`. Use `set la := AllWt.modelWt (U σ) G with hla`. Establish `hchi` using `GlobalTheory.AllWt.Model.chi_modelWt (U σ) (hL.chiTriv σ hσ) G hG`. Use `set Cl := AllWt.classesOver (D.sp.W j) (dict σ) A with hCl`.

Establish `hyS : y.1 ∈ S` using `⟨y.2.1, hy⟩`. Unfold `AllWt.bergOn AllWt.bergE`. Use `iSup₂_le fun P hP => ?_` and prove the remaining obligations. Use `set P' : Formalism.L2.Pj.FDSec (U σ).X := fun k => if k ∈ S then P k else 0 with hP'`. Establish `hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la`.

Use `Formalism.L2.Pj.holCusp_mem_holSub _ _ fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ S`. Simplify using `only [hP', if_pos hk]`. Conclude with `Formalism.L2.Pj.holSub_comp_SS _ _ _ hP k`. Simplify using `only [hP', if_neg hk]`.

Conclude with `(ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1`. Establish `hpt : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r, AllWt.ptN la P' z = if z.1 ∈ S then AllWt.ptN la P z else 0` using `fun z => by`. Distinguish the cases in `hz : z.1 ∈ S`. Simplify using `only [AllWt.ptN, hP', if_pos hz]`. Simplify using `only [AllWt.ptN, hP', if_neg hz]`.

Conclude with `Formalism.L2.Pj.pnorm_zero _ _ _`. Establish `h1 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤ Formalism.L2.Pj.supE (U σ).X la P' ^ 2`. Establish `e : AllWt.ptN la P ⟨y.1, y.2.1⟩ = AllWt.ptN la P' ⟨y.1, y.2.1⟩`. Rewrite using `[hpt, if_pos hyS]`. Rewrite using `[e]`.

Use `gcongr`. Conclude with `le_iSup (fun p : Formalism.L2.Pj.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P' p.1) p.2)) y`. Establish `h2` using `GlobalTheory.T.weighted_frame_sum_second hT D j H Dw l Xo c U dict hL σ hσ la w hw hsp hchi P' hP'm`. Establish `h3 : AllWt.petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P' ≤ AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P`. Establish `hsupp : Function.support (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) ⊆ Cl`.

Introduce `q hq`. Assume the negation of the conclusion as `hn`. Apply `hq` to reduce the goal to its premises. Establish `: ¬ (dict σ q.out).1 ∈ S` using `fun h => hn ((key _).2 h)`. Use `show AllWt.ptN la P' (dict σ q.out) = 0`.

Rewrite using `[hpt, if_neg this]`. Unfold `AllWt.petE`. Rewrite using `[← eLpNorm_restrict_eq_of_support_subset hsupp]`. Combine the equalities or inequalities in the displayed calculation. Use `eLpNorm_mono fun q => ?_` and prove the remaining obligations.

Rewrite using `[Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), hpt]`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `AllWt.ptN_nonneg _ _ _`. Use `_ ≤ eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2 (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) := by show _ ≤ eLpNorm _ 2 ((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl)`.

Rewrite using `[eLpNorm_smul_measure_of_ne_top (by norm_num)]`. Use `le_mul_of_one_le_left (by simp) ?_` and prove the remaining obligations. Conclude with `ENNReal.one_le_rpow (ENNReal.one_le_inv.2 prob_le_one) (by norm_num)`. Establish `h4 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) * AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2` using `h1.trans (h2.trans (by gcongr))`. Conclude with `ENNReal.div_le_of_le_mul h4`.
-/
theorem bergOn_le_supConst : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 → ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) → ∀ (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z → AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) := by
  intro hT D j H Dw l Xo c U dict hL σ hσ G hG w hw hsp Z y hy
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  set A := AllWt.framesOn (U σ) Z with hA
  set S : Set (U σ).Comp := {k | ∃ f, (⟨k, f⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ A} with hS
  have key : ∀ g, dict σ g ∈ A ↔ (dict σ g).1 ∈ S := fun g =>
    ⟨fun h => ⟨_, h⟩, fun ⟨f, hf⟩ =>
      GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ f _ (hdom g) hf⟩
  set la := AllWt.modelWt (U σ) G with hla
  have hchi := GlobalTheory.AllWt.Model.chi_modelWt (U σ) (hL.chiTriv σ hσ) G hG
  set Cl := AllWt.classesOver (D.sp.W j) (dict σ) A with hCl
  have hyS : y.1 ∈ S := ⟨y.2.1, hy⟩
  unfold AllWt.bergOn AllWt.bergE
  refine iSup₂_le fun P hP => ?_
  set P' : Formalism.L2.Pj.FDSec (U σ).X := fun k => if k ∈ S then P k else 0 with hP'
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := by
    refine Formalism.L2.Pj.holCusp_mem_holSub _ _ fun k => ?_
    by_cases hk : k ∈ S
    · simp only [hP', if_pos hk]
      exact Formalism.L2.Pj.holSub_comp_SS _ _ _ hP k
    · simp only [hP', if_neg hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hpt : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r,
      AllWt.ptN la P' z = if z.1 ∈ S then AllWt.ptN la P z else 0 := fun z => by
    by_cases hz : z.1 ∈ S
    · simp only [AllWt.ptN, hP', if_pos hz]
    · simp only [AllWt.ptN, hP', if_neg hz]
      exact Formalism.L2.Pj.pnorm_zero _ _ _

  have h1 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤ Formalism.L2.Pj.supE (U σ).X la P' ^ 2 := by
    have e : AllWt.ptN la P ⟨y.1, y.2.1⟩ = AllWt.ptN la P' ⟨y.1, y.2.1⟩ := by
      rw [hpt, if_pos hyS]
    rw [e]
    gcongr
    exact le_iSup (fun p : Formalism.L2.Pj.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P' p.1) p.2)) y

  have h2 := GlobalTheory.T.weighted_frame_sum_second hT D j H Dw l Xo c U dict hL σ hσ la w hw hsp hchi P' hP'm

  have h3 : AllWt.petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P' ≤
      AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P := by
    have hsupp : Function.support (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) ⊆ Cl := by
      intro q hq
      by_contra hn
      apply hq
      have : ¬ (dict σ q.out).1 ∈ S := fun h => hn ((key _).2 h)
      show AllWt.ptN la P' (dict σ q.out) = 0
      rw [hpt, if_neg this]
    unfold AllWt.petE
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    calc eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2 ((muQ1 (D.sp.W j)).restrict Cl)
        ≤ eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2 ((muQ1 (D.sp.W j)).restrict Cl) := by
          refine eLpNorm_mono fun q => ?_
          rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), hpt]
          split_ifs
          · exact le_rfl
          · exact AllWt.ptN_nonneg _ _ _
      _ ≤ eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2
            (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) := by
          show _ ≤ eLpNorm _ 2 ((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl)
          rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
          refine le_mul_of_one_le_left (by simp) ?_
          exact ENNReal.one_le_rpow (ENNReal.one_le_inv.2 prob_le_one) (by norm_num)
  have h4 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) *
        AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2 :=
    h1.trans (h2.trans (by gcongr))
  exact ENNReal.div_le_of_le_mul h4

end GlobalTheory.BergComp
