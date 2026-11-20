import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open scoped ContDiff

/- English proof (translation)
Introduce `e σ S`. Establish `hcl : IsClosed (bdry S.s)` using `LeviFormBoundaryTopology.isClosed_bdry S.sec`. Use `⟨hcl.isOpen_compl, ?_, ?_, ?_, fun y _ => rW_ge S.L S.s S.norm_le y⟩` and prove the remaining obligations. Establish `hAn : S.A.IsAnalyticSubset (bdry S.s)`. Introduce `x`.

Use `⟨S.L.U x, S.L.isOpen_U x, S.L.mem_U x, 1, fun _ => S.s x, fun _ => S.sec.1 x, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hzU⟩`. Conclude with `⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff S.sec hzU).1 hz⟩`.

Introduce and unpack `⟨hzU, hz⟩`. Conclude with `⟨(LeviFormBoundaryTopology.bdry_iff S.sec hzU).2 (hz 0), hzU⟩`. Establish `hInt` using `LeviFormBoundaryTopology.interior_bdry_eq_empty S.sec S.snc`. Introduce `j`. Establish `h` using `analyticNull S.A (bdry S.s) hAn hInt j`.

Establish `hc : S.open'ᶜ = bdry S.s` using `compl_compl _`. Rewrite using `[hc]`. Rewrite `h` using `[Set.inter_comm, (S.A.chart j).image_source_inter_eq']`. Conclude with `h`. Introduce `a x hx j hj`.

Take `⟨hth, hph, -, -⟩` from `S.sing a`. Establish `h1` using `hth.1 x j`. Establish `h2` using `hph j`. Establish `hO1 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x)` using `(S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U x)`. Establish `hO2 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ)` using `(S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl`.

Establish `hm1 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x` using `⟨(S.A.chart j).map_source hj, by`. Simplify `(S.th a).mem_U x⟩` using `[(S.A.chart j).left_inv hj]`. Establish `hm2 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ` using `⟨(S.A.chart j).map_source hj, by`. Establish `hx' : x ∈ (bdry S.s)ᶜ` using `hx`. Simplify `hx'⟩` using `[(S.A.chart j).left_inv hj]`.

Establish `hle : (2 : WithTop ℕ∞) ≤ ∞` using `ENat.LEInfty.out`. Establish `hA` using `(h1.contDiffAt (hO1.mem_nhds hm1)).of_le hle`. Establish `hB` using `(h2.contDiffAt (hO2.mem_nhds hm2)).of_le hle`. Conclude with `hA.add hB`. Introduce `a t ht ht'`.

Conclude with `isPotentialAdd S.A _ _ (S.sing a).1 (isPotential_ofFun S.A _ ((S.reg a).2.2 t ht ht').1)`.
-/
theorem GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics : ∀ (e : ℕ) (σ : Type) (S : AnSys e σ), IsOpen S.open' ∧ IsNull S.A S.open'ᶜ ∧ (∀ a, ∀ x ∈ S.open', IsTwiceDifferentiableAt S.A (S.potH a) x) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t)) ∧ ∀ y ∈ S.open', Real.exp 1 ≤ rW S.L S.s y := by
  intro e σ S
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  refine ⟨hcl.isOpen_compl, ?_, ?_, ?_, fun y _ => rW_ge S.L S.s S.norm_le y⟩
  · have hAn : S.A.IsAnalyticSubset (bdry S.s) := by
      intro x
      refine ⟨S.L.U x, S.L.isOpen_U x, S.L.mem_U x, 1, fun _ => S.s x, fun _ => S.sec.1 x, ?_⟩
      ext z
      constructor
      · rintro ⟨hz, hzU⟩
        exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff S.sec hzU).1 hz⟩
      · rintro ⟨hzU, hz⟩
        exact ⟨(LeviFormBoundaryTopology.bdry_iff S.sec hzU).2 (hz 0), hzU⟩
    have hInt := LeviFormBoundaryTopology.interior_bdry_eq_empty S.sec S.snc
    intro j
    have h := analyticNull S.A (bdry S.s) hAn hInt j
    have hc : S.open'ᶜ = bdry S.s := compl_compl _
    rw [hc]
    rw [Set.inter_comm, (S.A.chart j).image_source_inter_eq'] at h
    exact h
  · intro a x hx j hj
    obtain ⟨hth, hph, -, -⟩ := S.sing a
    have h1 := hth.1 x j
    have h2 := hph j
    have hO1 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x) :=
      (S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U x)
    have hO2 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ) :=
      (S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl
    have hm1 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x :=
      ⟨(S.A.chart j).map_source hj, by
        simpa [(S.A.chart j).left_inv hj] using (S.th a).mem_U x⟩
    have hm2 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ :=
      ⟨(S.A.chart j).map_source hj, by
        have hx' : x ∈ (bdry S.s)ᶜ := hx
        simpa [(S.A.chart j).left_inv hj] using hx'⟩
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
    have hA := (h1.contDiffAt (hO1.mem_nhds hm1)).of_le hle
    have hB := (h2.contDiffAt (hO2.mem_nhds hm2)).of_le hle
    exact hA.add hB
  · intro a t ht ht'
    exact isPotentialAdd S.A _ _ (S.sing a).1 (isPotential_ofFun S.A _ ((S.reg a).2.2 t ht ht').1)
