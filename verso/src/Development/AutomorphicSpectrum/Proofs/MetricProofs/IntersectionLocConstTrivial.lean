import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Introduce `hInt K _ ι _ Ω _ F _ _ _ y D L B Λ II hII hP hL hB0 hB hex hloc`. Set `S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ)` to `fun sg => {z | LiesOver y sg z}`. Establish `hSc : ∀ sg, IsClosed (S sg)` using `fun sg => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg`. Establish `hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg → (fun p => t p.1 * z p) ∈ S sg` using `fun _ t _ _ hz => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.liesOver_smul hz t`. Establish `hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg` using `hex`.

Establish `hR` using `(hII K ι).2.2 (mCoordIdeal y) D L B 1 0 hP hL hB (fun k => by simp [hB0]) tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1))`. Establish `hnum : II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) = ptsIntegral (mCoordIdeal y) (pot L) fun z => Real.log (B.h z)`. Rewrite using `[hR]`. Unfold `recR`. Rewrite using `[tele_divSupp_one, finsum_mem_empty, zero_sub]`.

Unfold `arInt`. Establish `hl : logNorm B 1 = fun z => - Real.log (B.h z)`. Use function extensionality and compare the values at `z`. Simplify using `[logNorm, Real.log_inv]`. Rewrite using `[hl, tele_ptsIntegral_neg, neg_neg]`.

Both sides reduce to the same expression. Establish `hw : ptsIntegral (mCoordIdeal y) (pot L) (fun z => Real.log (B.h z)) = ptsIntegral (mCoordIdeal y) (pot L) (fun z => ∑ s, Real.log (Λ s) * (S s).indicator (fun _ => (1 : ℝ)) z)`. Use `GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨sg, hsg, -⟩` from `hex z hz`.

Establish `hval : B.h z = Λ sg` using `(hloc z hz sg hsg).self_of_nhds`. Rewrite using `[Finset.sum_eq_single sg]`. Rewrite using `[Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one, hval]`. Introduce `s _ hs`. Establish `hns : z ∉ S s` using `fun h => hs ((hex z hz).unique h hsg)`.

Rewrite using `[Set.indicator_of_notMem hns, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ sg) h`. Rewrite using `[hnum, hw]`. Conclude with `GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt K ι _ D L (F →+* ℂ) S (fun s => Real.log (Λ s)) hP hL hSc hSs hex'`.
-/
theorem intersection_locConst_trivial : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (B : HermLine ι) (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → B.a = 0 → IsSmoothHerm B → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) → II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) = ∑ sg : F →+* ℂ, Real.log (Λ sg) * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hInt K _ ι _ Ω _ F _ _ _ y D L B Λ II hII hP hL hB0 hB hex hloc
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hR := (hII K ι).2.2 (mCoordIdeal y) D L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1))
  have hnum : II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) =
      ptsIntegral (mCoordIdeal y) (pot L) fun z => Real.log (B.h z) := by
    rw [hR]
    unfold recR
    rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
    unfold arInt
    have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
      funext z
      simp [logNorm, Real.log_inv]
    rw [hl, tele_ptsIntegral_neg, neg_neg]
    rfl
  have hw : ptsIntegral (mCoordIdeal y) (pot L) (fun z => Real.log (B.h z)) =
      ptsIntegral (mCoordIdeal y) (pot L)
        (fun z => ∑ s, Real.log (Λ s) * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = Λ sg := (hloc z hz sg hsg).self_of_nhds
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one, hval]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [hnum, hw]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt K ι _ D L (F →+* ℂ) S
    (fun s => Real.log (Λ s)) hP hL hSc hSs hex'

end GlobalTheory.CompanionTheory.Ar.Giv
