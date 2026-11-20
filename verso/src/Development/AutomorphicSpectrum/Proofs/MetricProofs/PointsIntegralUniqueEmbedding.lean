import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetryStatement
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def conjugateProjection {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w := star (Ψ (star w))
  map_add' a b := by simp only [star_add, map_add]
  map_smul' c w := by
    simp only [star_smul, map_smul, RingHom.id_apply, star_star]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `star (Ψ (star (star w))) = _`. Rewrite using `[star_star]`.
-/
theorem conjugateProjection_star {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : conjugateProjection Ψ (star w) = star (Ψ w) := by
  change star (Ψ (star (star w))) = _
  rw [star_star]

/- English proof (translation)
Use `⟨0, fun k => by simp [hA], ?_, ?_⟩` and prove the remaining obligations. Introduce `m hm k`. Establish `hm0 : m = 0` using `by classical`. Use `MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k) ▸ hm` as an intermediate fact. Simplify using `using this`.

Simplify using `[hm0]`. Conclude with `(Ideal.ne_top_iff_one P).1 hP.2.1.1.ne_top`.
-/
theorem isSectionOn_one_of_degree_zero {P : Ideal (MRing ι)} {d : ℕ} {A : HermLine ι}
    (hP : IsArithVar P d) (hA : A.a = 0) : IsSectionOn P A 1 := by
  refine ⟨0, fun k => by simp [hA], ?_, ?_⟩
  · intro m hm k
    have hm0 : m = 0 := by
      classical
      have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k) ▸ hm
      simpa using this
    simp [hm0]
  · exact (Ideal.ne_top_iff_one P).1 hP.2.1.1.ne_top

open Classical in

/- English proof (translation)
Introduce `z hz`. Take `⟨s, hs, hs'⟩` from `huniq z hz`. Establish `hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1` using `by simp`. Unfold `logNorm`. Rewrite using `[hone, hB z hz s hs]`.

Distinguish the cases in `hst : s = tg`. Substitute `hst` using the available equality. Rewrite using `[Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), if_pos rfl, one_div, Real.log_inv, Real.log_exp, neg_neg]`. Rewrite using `[Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), if_neg hst]`. Simplify using the standard rewrite rules.
-/
theorem logNorm_one_eq_indicator {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω}
    {P : Ideal (MRing ι)} {tg : F →+* ℂ} {B : HermLine ι}
    (huniq : ∀ z ∈ mcPts P, ∃! s : F →+* ℂ, LiesOver y s z)
    (hB : ∀ z ∈ mcPts P, ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = tg then Real.exp (-1) else 1) :
    ∀ z ∈ mcPts P, logNorm B 1 z = ({z | LiesOver y tg z}.indicator fun _ => (1 : ℝ)) z := by
  classical
  intro z hz
  obtain ⟨s, hs, hs'⟩ := huniq z hz
  have hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1 := by simp
  unfold logNorm
  rw [hone, hB z hz s hs]
  by_cases hst : s = tg
  · subst hst
    rw [Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), if_pos rfl, one_div,
      Real.log_inv, Real.log_exp, neg_neg]
  · rw [Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), if_neg hst]
    simp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hRes K _ ι _ Ω _ F _ _ _ y D L sg hP hL hC huniq`. Establish `hpos : ∀ tg s : F →+* ℂ, 0 < (if s = tg then Real.exp (-1) else (1 : ℝ))`. Introduce `tg s`. Use `split_ifs`. Conclude with `Real.exp_pos _`.

Conclude with `one_pos`. Take `⟨B, hBa, hBs, hB⟩` from `exists_smooth_weight_const_near_embeddings K ι Ω F y (fun s => if s = sg then Real.exp (-1) else 1) (hpos sg) huniq`. Take `⟨B', hBa', hBs', hB'⟩` from `exists_smooth_weight_const_near_embeddings K ι Ω F y (fun s => if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1) (hpos (ComplexEmbedding.conjugate sg)) huniq`. Establish `hBv : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = sg then Real.exp (-1) else 1` using `fun z hz s hs => (hB z hz s hs).self_of_nhds`. Establish `hBv' : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z → B'.h z = if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1` using `fun z hz s hs => (hB' z hz s hs).self_of_nhds`.

Rewrite using `[← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y) (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv'), ← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y) (fun _ _ _ => rfl) (logNorm_one_eq_indicator hu …`. Distinguish the cases in `hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal y) Ψ`. Take `⟨Ψ, hΨ⟩` from `hex`. Establish `hstar : ∀ z ∈ mcPts (mCoordIdeal y), B'.h (star z) = B.h z`. Introduce `z hz`.

Take `⟨s, hs, -⟩` from `huniq z hz`. Establish `hzc : star z ∈ mcPts (mCoordIdeal y)` using `conjVec_mem_mcPts hz`. Establish `hsc : LiesOver y (ComplexEmbedding.conjugate s) (star z)` using `liesOver_conjVec hs`. Establish `hiff : ComplexEmbedding.conjugate s = ComplexEmbedding.conjugate sg ↔ s = sg` using `⟨fun h => by simpa using congrArg ComplexEmbedding.conjugate h, fun h => by rw [h]⟩`. Rewrite using `[hBv' _ hzc _ hsc, hBv z hz s hs]`.

Simplify using `only [hiff]`. Apply the tactic sequence `obtain ⟨hΨ', hI⟩ := GlobalTheory.T.points_integral_conjugation_symmetry K ι (mCoordIdeal y) D Ψ (conjugateProjection Ψ) L B B' hP hΨ (conjugateProjection_star Ψ) hL hC hBa hBs hBa' hBs' hstar`. Rewrite using `[ptsIntegral_eq_at hRes resBridge hP hΨ' hL hBs' (isSectionOn_one_of_degree_zero hP hBa'), ptsIntegral_eq_at hRes resBridge hP hΨ hL hBs (isSectionOn_one_of_degree_zero hP hBa), hI]`. Unfold `ptsIntegral`. Rewrite using `[dif_neg hex, dif_neg hex]`.
-/
theorem conjugate_pieces_same_mass :
    ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hRes K _ ι _ Ω _ F _ _ _ y D L sg hP hL hC huniq
  classical
  have hpos : ∀ tg s : F →+* ℂ, 0 < (if s = tg then Real.exp (-1) else (1 : ℝ)) := by
    intro tg s
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  obtain ⟨B, hBa, hBs, hB⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = sg then Real.exp (-1) else 1) (hpos sg) huniq
  obtain ⟨B', hBa', hBs', hB'⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1)
    (hpos (ComplexEmbedding.conjugate sg)) huniq
  have hBv : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B.h z = if s = sg then Real.exp (-1) else 1 := fun z hz s hs => (hB z hz s hs).self_of_nhds
  have hBv' : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B'.h z = if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1 :=
    fun z hz s hs => (hB' z hz s hs).self_of_nhds
  rw [← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv'),
    ← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv)]
  by_cases hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal y) Ψ
  · obtain ⟨Ψ, hΨ⟩ := hex
    have hstar : ∀ z ∈ mcPts (mCoordIdeal y), B'.h (star z) = B.h z := by
      intro z hz
      obtain ⟨s, hs, -⟩ := huniq z hz
      have hzc : star z ∈ mcPts (mCoordIdeal y) := conjVec_mem_mcPts hz
      have hsc : LiesOver y (ComplexEmbedding.conjugate s) (star z) := liesOver_conjVec hs
      have hiff : ComplexEmbedding.conjugate s = ComplexEmbedding.conjugate sg ↔ s = sg :=
        ⟨fun h => by simpa using congrArg ComplexEmbedding.conjugate h, fun h => by rw [h]⟩
      rw [hBv' _ hzc _ hsc, hBv z hz s hs]
      simp only [hiff]
    obtain ⟨hΨ', hI⟩ := GlobalTheory.T.points_integral_conjugation_symmetry K ι (mCoordIdeal y) D Ψ (conjugateProjection Ψ) L B B' hP hΨ
      (conjugateProjection_star Ψ) hL hC hBa hBs hBa' hBs' hstar
    rw [ptsIntegral_eq_at hRes resBridge hP hΨ' hL hBs' (isSectionOn_one_of_degree_zero hP hBa'),
      ptsIntegral_eq_at hRes resBridge hP hΨ hL hBs (isSectionOn_one_of_degree_zero hP hBa), hI]
  · unfold ptsIntegral
    rw [dif_neg hex, dif_neg hex]

end GlobalTheory.CompanionTheory.Ar.Giv
