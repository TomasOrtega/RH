import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLeviGen
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FS

open MvPolynomial Filter Topology
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.FubiniStudyLeviForm

/- English proof (translation)
Use function extensionality and compare the values at `z`. Express the relevant statement in the definitionally equal form `Real.log ‖WithLp.toLp 2 z‖ = _`. Rewrite using `[EuclideanSpace.norm_eq, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `only [FubiniLevi.phi, FubiniLevi.sqSum, PiLp.toLp_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_rho_eq_phi (I : Type) [Fintype I] :
    (fun z : I → ℂ => Real.log ((fsMetric I).ρ z)) = FubiniLevi.phi := by
  funext z
  change Real.log ‖WithLp.toLp 2 z‖ = _
  rw [EuclideanSpace.norm_eq, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [FubiniLevi.phi, FubiniLevi.sqSum, PiLp.toLp_apply]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `choose c hc using h`. Conclude with `hw c (funext fun p => by`. Take `⟨k, i⟩` from `p`.

Conclude with `congrFun (hc k) i)`.
-/
theorem exists_block_ne {z w : (Σ k, J k) → ℂ} (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    ∃ k, ∀ c : ℂ, (fun i => w ⟨k, i⟩) ≠ fun i => c * z ⟨k, i⟩ := by
  by_contra h
  push_neg at h
  choose c hc using h
  exact hw c (funext fun p => by
    obtain ⟨k, i⟩ := p
    exact congrFun (hc k) i)

/- English proof (translation)
Take `⟨k₀, hk₀⟩` from `exists_block_ne hw`. Use `set F : K → ((Σ k, J k) → ℂ) → ℝ := fun k y => Real.log ((fsMetric (J k)).ρ (fun i => y ⟨k, i⟩)) with hF`. Establish `hev : (fun y => Real.log ((fsMulti J).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y`. Establish `hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hz k`.

Conclude with `Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi) fun y hy => ⟨i, hy⟩`. Use `filter_upwards [Filter.eventually_all.mpr hopen] with y hy`. Establish `hpos : ∀ k, 0 < (fsMetric (J k)).ρ (fun i => y ⟨k, i⟩)` using `fun k => by`. Take `⟨i, hi⟩` from `hy k`. Conclude with `(fsMetric (J k)).pos _ fun h0 => hi (congrFun h0 i)`.

Simplify using `only [fsMulti, HermLine.ofMetrics, zpow_one, hF]`. Conclude with `Real.log_prod fun k _ => (hpos k).ne'`. Establish `hk0 : ∀ k, (fun i => z ⟨k, i⟩) ≠ 0` using `fun k h0 => by`. Take `⟨i, hi⟩` from `hz k`. Conclude with `hi (congrFun h0 i)`.

Establish `hφ : ∀ k, ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric (J k)).ρ u)) (blockProj J k z)` using `fun k => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := J k)) (hk0 k)`. Establish `hFk : ∀ k, F k = (fun u => Real.log ((fsMetric (J k)).ρ u)) ∘ blockProj J k` using `fun k => rfl`. Establish `hC : ∀ k, ContDiffAt ℝ 2 (F k) z` using `fun k => hFk k ▸ (hφ k).comp z ((blockProj J k).restrictScalars ℝ).contDiff.contDiffAt`. Establish `hL : ∀ k v, ReciprocityTheory.AnForm.levi (F k) z v = leviForm (fun u => Real.log ((fsMetric (J k)).ρ u)) (fun i => z ⟨k, i⟩) (fun i => v ⟨k, i⟩)` using `fun k v => by`. Rewrite using `[hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj J k).analyticAt z) (hφ k), (blockProj J k).fderiv]`.

Both sides reduce to the same expression. Establish `hnn : ∀ k v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v` using `fun k v => by`. Rewrite using `[hL]`. Conclude with `HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hk0 k) _`. Establish `hpos : 0 < ReciprocityTheory.AnForm.levi (F k₀) z w`.

Rewrite using `[hL, log_rho_eq_phi]`. Conclude with `FubiniLevi.levi_phi_pos_of_ne (hz k₀) hk₀`. Establish `hsum` using `levi_sum_nonneg F (fun k => hC k) hnn w (Finset.univ.erase k₀)`. Express the relevant statement in the definitionally equal form `0 < ReciprocityTheory.AnForm.levi _ z w`. Rewrite using `[ReciprocityTheory.AnForm.levi_congr hev]`.

Establish `hsplit : (fun y => ∑ k ∈ Finset.univ, F k y) = fun y => F k₀ y + 1 * ∑ k ∈ Finset.univ.erase k₀, F k y`. Use function extensionality and compare the values at `y`. Rewrite using `[_root_.one_mul]`. Conclude with `(Finset.add_sum_erase Finset.univ (fun k => F k y) (Finset.mem_univ k₀)).symm`. Rewrite using `[hsplit, ReciprocityTheory.AnForm.levi_add_smul 1 (hC k₀) hsum.1 w]`.

Combine the linear relations using `[hsum.2]`.
-/
theorem levi_fsMulti_pos {z w : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < leviForm (fun y => Real.log ((fsMulti J).h y)) z w := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_block_ne hw
  set F : K → ((Σ k, J k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (J k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti J).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric (J k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric (J k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hk0 : ∀ k, (fun i => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  have hφ : ∀ k, ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric (J k)).ρ u)) (blockProj J k z) := fun k =>
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := J k)) (hk0 k)
  have hFk : ∀ k, F k = (fun u => Real.log ((fsMetric (J k)).ρ u)) ∘ blockProj J k := fun k => rfl
  have hC : ∀ k, ContDiffAt ℝ 2 (F k) z := fun k =>
    hFk k ▸ (hφ k).comp z ((blockProj J k).restrictScalars ℝ).contDiff.contDiffAt
  have hL : ∀ k v, ReciprocityTheory.AnForm.levi (F k) z v = leviForm (fun u => Real.log ((fsMetric (J k)).ρ u))
      (fun i => z ⟨k, i⟩) (fun i => v ⟨k, i⟩) := fun k v => by
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj J k).analyticAt z) (hφ k), (blockProj J k).fderiv]
    rfl
  have hnn : ∀ k v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := fun k v => by
    rw [hL]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hk0 k) _
  have hpos : 0 < ReciprocityTheory.AnForm.levi (F k₀) z w := by
    rw [hL, log_rho_eq_phi]
    exact FubiniLevi.levi_phi_pos_of_ne (hz k₀) hk₀
  have hsum := levi_sum_nonneg F (fun k => hC k) hnn w (Finset.univ.erase k₀)
  change 0 < ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  have hsplit : (fun y => ∑ k ∈ Finset.univ, F k y) =
      fun y => F k₀ y + 1 * ∑ k ∈ Finset.univ.erase k₀, F k y := by
    funext y
    rw [_root_.one_mul]
    exact (Finset.add_sum_erase Finset.univ (fun k => F k y) (Finset.mem_univ k₀)).symm
  rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul 1 (hC k₀) hsum.1 w]
  linarith [hsum.2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨FsLineSmooth.proof K J, fun _ hz _ _ hw => levi_fsMulti_pos hz.1 hw⟩`.
-/
theorem isPositiveRel_fsMulti (P : Ideal (MRing J)) : IsPositiveRel P (fsMulti J) :=
  ⟨FsLineSmooth.proof K J, fun _ hz _ _ hw => levi_fsMulti_pos hz.1 hw⟩

/- English proof (translation)
Introduce `z`. Simplify using `[fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]`.
-/
theorem isConjInvariantH_fsMulti : IsConjInvariantH (fsMulti J) := by
  intro z
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

def chartForm (c : ∀ k, J k) : MRing J := ∏ k, X ⟨k, c k⟩

/- English proof (translation)
Establish `h` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c (fun _ : K => 1)`. Simplify `h` using `[chartForm, fsMulti, HermLine.ofMetrics, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow]`.
-/
theorem isMultiHomog_chartForm (c : ∀ k, J k) :
    IsMultiHomog (chartForm c) fun k => ((fsMulti J).a k).toNat := by
  classical
  have h := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c (fun _ : K => 1)
  simpa [chartForm, fsMulti, HermLine.ofMetrics, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow] using h

/- English proof (translation)
Establish `e : eval z (map (Int.castRingHom ℂ) (chartForm c)) = ∏ k, z ⟨k, c k⟩`. Simplify using `[chartForm, map_prod]`. Rewrite using `[e, norm_prod]`. Simplify using `only [fsMulti, HermLine.ofMetrics, zpow_one]`. Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_` and prove the remaining obligations.

Conclude with `PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) (c k)`.
-/
theorem chartForm_le (c : ∀ k, J k) (z : (Σ k, J k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (chartForm c))‖ ≤ (fsMulti J).h z := by
  have e : eval z (map (Int.castRingHom ℂ) (chartForm c)) = ∏ k, z ⟨k, c k⟩ := by
    simp [chartForm, map_prod]
  rw [e, norm_prod]
  simp only [fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) (c k)

/- English proof (translation)
Use `choose c hc using hQ.2.2`. Use `⟨c, fun h => ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `(hQ.1.prod_mem_iff).1 h`. Conclude with `hc k hk`.
-/
theorem exists_chartForm_notMem {Q : Ideal (MRing J)} (hQ : IsMultiProjPrime Q) :
    ∃ c, chartForm c ∉ Q := by
  choose c hc using hQ.2.2
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hQ.1.prod_mem_iff).1 h
  exact hc k hk

/- English proof (translation)
Set `e` to `Fintype.equivFin (∀ k, J k)`. Use `HilbertSamuel.SmallGenHeightsNonneg.proof K J ⊥ (fsMulti J) II _ (fun j => chartForm (e.symm j)) hII (FsLineSmooth.proof K J) (fun k => ?_) (fun j => isMultiHomog_chartForm _) (fun Q hQ _ => ?_) (fun j z _ => chartForm_le _ z) W hW bot_le` and prove the remaining obligations. Use `show (0 : ℤ) ≤ 1`. Conclude with `zero_le_one`. Take `⟨c, hc⟩` from `exists_chartForm_notMem hQ`.

Conclude with `⟨e c, by simpa using hc⟩`.
-/
theorem heights_fsMulti {II : IntersectionSystem} (hII : IsIntersectionSystem II) {W : Ideal (MRing J)}
    (hW : IsArithVar W 1) : 0 ≤ II K J W 1 ![fsMulti J] := by
  classical
  let e := Fintype.equivFin (∀ k, J k)
  refine HilbertSamuel.SmallGenHeightsNonneg.proof K J ⊥ (fsMulti J) II _ (fun j => chartForm (e.symm j)) hII
    (FsLineSmooth.proof K J) (fun k => ?_) (fun j => isMultiHomog_chartForm _) (fun Q hQ _ => ?_)
    (fun j z _ => chartForm_le _ z) W hW bot_le
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · obtain ⟨c, hc⟩ := exists_chartForm_notMem hQ
    exact ⟨e c, by simpa using hc⟩

end GlobalTheory.CompanionTheory.Ar.FS

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Introduce `_ _ _ _ _ P hII` and use `⟨GroundTheory.Heights₂.Heights.fsMulti _, fun _ => rfl, FS.isPositiveRel_fsMulti P, FS.isConjInvariantH_fsMulti, fun _ hW => FS.heights_fsMulti hII.1 hW⟩`.
-/
theorem exists_fubiniStudy_line :
    ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)),
      IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧
        ∀ W : Ideal (MRing J), IsArithVar W 1 → 0 ≤ II K J W 1 ![A] :=
  fun _ _ _ _ _ P hII => ⟨GroundTheory.Heights₂.Heights.fsMulti _, fun _ => rfl, FS.isPositiveRel_fsMulti P,
    FS.isConjInvariantH_fsMulti, fun _ hW => FS.heights_fsMulti hII.1 hW⟩

end GlobalTheory.CompanionTheory.Ar
