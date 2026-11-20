import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemMinimalPrimesOfMemSupport
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DifferentiableOnSheet
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GroundTheory.Heights₂.Heights (HermNorm coneBall fsLog coneIntegral coordBall_mass IsProjPrime)
open scoped ENNReal

namespace ChowFormHeightComparison₂.CF.C

/- English proof (translation)
Establish `hG1 : Measurable fun t : ℝ => ‖t‖ₑ` using `measurable_enorm`. Establish `hgi : Integrable g ν`. Use `⟨hg.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hfin : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤` using `hf.2`. Rewrite `hfin` using `[h _ hG1]`.

Conclude with `ENNReal.lt_top_of_mul_ne_top_right hfin.ne hb`. Use `⟨hgi, ?_⟩` and prove the remaining obligations. Establish `hp` using `h _ ENNReal.measurable_ofReal`. Establish `hn` using `h (fun t => ENNReal.ofReal (-t)) (ENNReal.measurable_ofReal.comp measurable_neg)`. Establish `hb0 : b.toReal ≠ 0` using `ENNReal.toReal_ne_zero.2 ⟨hb, hb'⟩`.

Rewrite using `[integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi, hp, hn, ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_of_lintegral {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {b : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ⊤) {f : X → ℝ} {g : Y → ℝ} (hg : Measurable g) (hf : Integrable f μ)
    (h : ∀ G : ℝ → ℝ≥0∞, Measurable G → ∫⁻ x, G (f x) ∂μ = b * ∫⁻ y, G (g y) ∂ν) :
    Integrable g ν ∧ ∫ y, g y ∂ν = (∫ x, f x ∂μ) / b.toReal := by
  have hG1 : Measurable fun t : ℝ => ‖t‖ₑ := measurable_enorm
  have hgi : Integrable g ν := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    have hfin : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := hf.2
    rw [h _ hG1] at hfin
    exact ENNReal.lt_top_of_mul_ne_top_right hfin.ne hb
  refine ⟨hgi, ?_⟩
  have hp := h _ ENNReal.measurable_ofReal
  have hn := h (fun t => ENNReal.ofReal (-t)) (ENNReal.measurable_ofReal.comp measurable_neg)
  have hb0 : b.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hb, hb'⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi, hp, hn,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub]
  field_simp

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin m) (𝓞 K)) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial`. Use `haveI hloc := MvPolynomial.isLocalization (σ := Fin m) (nonZeroDivisors (𝓞 K)) K`. Establish `hdisj : Disjoint (((nonZeroDivisors (𝓞 K)).map (C (σ` using `Fin m)) : Submonoid (MvPolynomial (Fin m) (𝓞 K))) : Set (MvPolynomial (Fin m) (𝓞 K))) (P : Set (MvPolynomial (Fin m) (𝓞 K))) := by`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨a, ha, rfl⟩ haP`.

Apply `hI` to reduce the goal to its premises. Establish `hmem : MvPolynomial.map (algebraMap (𝓞 K) K) (C a) ∈ P.map (MvPolynomial.map (algebraMap (𝓞 K) K))` using `Ideal.mem_map_of_mem _ haP`. Rewrite `hmem` using `[map_C]`. Establish `ha0 : algebraMap (𝓞 K) K a ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]`.

Conclude with `nonZeroDivisors.ne_zero ha`. Conclude with `Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit ha0).map C)`. Introduce `hmem`. Apply `hq` to reduce the goal to its premises. Establish `hc` using `IsLocalization.comap_map_of_isPrime_disjoint (M := (nonZeroDivisors (𝓞 K)).map (C (σ := Fin m))) (S := MvPolynomial (Fin m) K) hP hdisj`.

Rewrite using `[← hc, Ideal.mem_comap]`. Conclude with `hmem`.
-/
theorem map_notMem {K : Type} [Field K] [NumberField K] {m : ℕ} {P : Ideal (MvPolynomial (Fin m) (𝓞 K))}
    (hP : P.IsPrime) (hI : P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) ≠ ⊤) {q : MvPolynomial (Fin m) (𝓞 K)}
    (hq : q ∉ P) : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) (𝓞 K)) (MvPolynomial (Fin m) K) :=
    MvPolynomial.algebraMvPolynomial
  haveI hloc := MvPolynomial.isLocalization (σ := Fin m) (nonZeroDivisors (𝓞 K)) K
  have hdisj : Disjoint (((nonZeroDivisors (𝓞 K)).map (C (σ := Fin m)) : Submonoid (MvPolynomial (Fin m) (𝓞 K))) :
      Set (MvPolynomial (Fin m) (𝓞 K))) (P : Set (MvPolynomial (Fin m) (𝓞 K))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haP
    apply hI
    have hmem : MvPolynomial.map (algebraMap (𝓞 K) K) (C a) ∈ P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) :=
      Ideal.mem_map_of_mem _ haP
    rw [map_C] at hmem
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero ha
    exact Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit ha0).map C)
  intro hmem
  apply hq
  have hc := IsLocalization.comap_map_of_isPrime_disjoint (M := (nonZeroDivisors (𝓞 K)).map (C (σ := Fin m)))
    (S := MvPolynomial (Fin m) K) hP hdisj
  rw [← hc, Ideal.mem_comap]
  exact hmem

/- English proof (translation)
Rewrite using `[← (stdOrthonormalBasis ℝ (V 0)).volume_parallelepiped]`. Use `congr 1`. Use `(Set.eq_univ_of_forall fun x => ?_).symm` and prove the remaining obligations. Establish `hx : x = 0`. Use extensionality with `i`.

Conclude with `i.elim0`. Rewrite using `[hx]`. Conclude with `(mem_parallelepiped_iff _ _).2 ⟨0, Set.left_mem_Icc.2 zero_le_one, by simp⟩`.
-/
theorem volume_univ_zero : (volume : Measure (V 0)) univ = 1 := by
  rw [← (stdOrthonormalBasis ℝ (V 0)).volume_parallelepiped]
  congr 1
  refine (Set.eq_univ_of_forall fun x => ?_).symm
  have hx : x = 0 := by
    ext i
    exact i.elim0
  rw [hx]
  exact (mem_parallelepiped_iff _ _).2 ⟨0, Set.left_mem_Icc.2 zero_le_one, by simp⟩

/- English proof (translation)
Establish `hV : ∀ a b : V 0, a = b` using `fun a b => by`. Use extensionality with `i`. Conclude with `i.elim0`. Establish `hsrc : ∀ (c : AlgChart p σ 0) (y : CxPts p σ), y ∈ c.e.source → c.e.source = {y}`. Introduce `c y hy`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `c.e.injOn hz hy (hV _ _)`. Introduce and unpack `rfl`.

Conclude with `hy`. Use `haveI : DiscreteTopology (CxPts p σ) := by`. Rewrite using `[discreteTopology_iff_isOpen_singleton]`. Introduce `y`. Take `⟨c, hcy⟩` from `hc y`.

Rewrite using `[← hsrc c y hcy]`. Conclude with `c.e.open_source`. Use `haveI : Finite (CxPts p σ) := finite_of_compact_of_discrete`. Use `letI := Fintype.ofFinite (CxPts p σ)`. Establish `hμ : φ.chernPart 0 1 = Measure.count`.

Rewrite using `[Measure.ext_iff_singleton]`. Introduce `y`. Take `⟨c, hcy⟩` from `hc y`. Establish `himg : (c.e '' {y}) = Set.univ` using `Set.eq_univ_of_forall fun v => ⟨y, rfl, hV _ _⟩`. Rewrite using `[Measure.count_singleton, Weight.chernPart_apply hφ 1 c (measurableSet_singleton y) (Set.singleton_subset_iff.2 hcy), himg]`.

Simplify using `[GlobalTheory.AlgChart.chernDens_zero, volume_univ_zero]`. Rewrite using `[hμ, finsum_eq_sum_of_fintype, integral_fintype Integrable.of_finite]`. Simplify using `[Measure.real, Measure.count_singleton]`.
-/
theorem integral_zero {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R} {σ : R →+* ℂ}
    [SecondCountableTopology (CxPts p σ)] [CompactSpace (CxPts p σ)] {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hc : ∀ y : CxPts p σ, ∃ c : AlgChart p σ 0, y ∈ c.e.source) (G : CxPts p σ → ℝ) :
    ∑ᶠ y, G y = ∫ y, G y ∂φ.chernPart 0 1 := by
  classical
  have hV : ∀ a b : V 0, a = b := fun a b => by
    ext i
    exact i.elim0
  have hsrc : ∀ (c : AlgChart p σ 0) (y : CxPts p σ), y ∈ c.e.source → c.e.source = {y} := by
    intro c y hy
    ext z
    constructor
    · intro hz
      exact c.e.injOn hz hy (hV _ _)
    · rintro rfl
      exact hy
  haveI : DiscreteTopology (CxPts p σ) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro y
    obtain ⟨c, hcy⟩ := hc y
    rw [← hsrc c y hcy]
    exact c.e.open_source
  haveI : Finite (CxPts p σ) := finite_of_compact_of_discrete
  letI := Fintype.ofFinite (CxPts p σ)
  have hμ : φ.chernPart 0 1 = Measure.count := by
    rw [Measure.ext_iff_singleton]
    intro y
    obtain ⟨c, hcy⟩ := hc y
    have himg : (c.e '' {y}) = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, hV _ _⟩
    rw [Measure.count_singleton,
      Weight.chernPart_apply hφ 1 c (measurableSet_singleton y) (Set.singleton_subset_iff.2 hcy), himg]
    simp [GlobalTheory.AlgChart.chernDens_zero, volume_univ_zero]
  rw [hμ, finsum_eq_sum_of_fintype, integral_fintype Integrable.of_finite]
  simp [Measure.real, Measure.count_singleton]

end ChowFormHeightComparison₂.CF.C

namespace ChowFormHeightComparison₂.CF

open C

/- English proof (translation)
Unfold `StArch`. Introduce `K _ _ Z _ p B m s e hE hAV hChow hproj σ φ h hφ hFS u hu`. Take `⟨f, hf⟩` from `hChow`. Use `haveI : CompactSpace (CxPts p (σ.comp (algebraMap (𝓞 K) K))) := hAV.compactSpace _`. Use `haveI : SecondCountableTopology (CxPts p (σ.comp (algebraMap (𝓞 K) K))) := GlobalTheory.CxPts.secondCountableTopology_of_isProjOver _ hAV.isProjOver`.

Take `⟨hem, hint, hcyc, hnull⟩` from `C.cone_side hproj hf σ h hu`. Take `⟨n, q, hqh, hqP, hqc⟩` from `h2 K Z p B m s e hE hAV`. Establish `hPprime : (ptIdeal p s (genericPoint Z)).IsPrime` using `((h1 (𝓞 K) Z p B m s hE).1 (genericPoint Z)).isPrime`. Establish `hq' : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ genIdeal p s` using `C.map_notMem hPprime hproj.isPrime.ne_top hqP`. Establish `hJzero : ∀ x : Fin m → ℂ, (∀ r ∈ Ideal.map (MvPolynomial.map σ) (genIdeal p s), MvPolynomial.eval x r = 0) ↔ ∀ r ∈ ptIdeal p s (genericPoint Z), eval₂ (σ.comp (algebraMap (𝓞 K) K)) x r = 0`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx r hr`. Establish `hx'` using `hx _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))`. Rewrite `hx'` using `[MvPolynomial.map_map, MvPolynomial.eval_map]`.

Conclude with `hx'`. Introduce `hx r hr`. Establish `hle : Ideal.map (MvPolynomial.map σ) (genIdeal p s) ≤ RingHom.ker (MvPolynomial.eval x)`. Rewrite using `[Ideal.map_le_iff_le_comap, genIdeal, Ideal.map_le_iff_le_comap]`. Introduce `r' hr'`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.map_map, MvPolynomial.eval_map]`. Conclude with `hx r' hr'`. Conclude with `hle hr`. Establish `hμ0 : μH[↑(2 * (e + 1))] ({0} ∪ coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)) ∩ {y : EuclideanSpace ℂ (Fin m) | eval₂ (σ.comp (algebraMap (𝓞 K) K)) (h.pointOf y) q = 0}) = 0`. Use `measure_union_null (C.hausdorffMeasure_zero e) ?_` and prove the remaining obligations.

Use `measure_mono_null ?_ (hnull _ hq')` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, hy2⟩`. Use `⟨hy1, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hy2 ⊢`. Rewrite using `[MvPolynomial.map_map, MvPolynomial.eval_map]`.

Conclude with `hy2`. Establish `hℓs : ∀ t : ℂ, t ≠ 0 → ∀ x : EuclideanSpace ℂ (Fin m), fsLog h (fun k => σ (u k)) (h.pointOf (t • x)) = fsLog h (fun k => σ (u k)) (h.pointOf x)`. Introduce `t ht x`. Rewrite using `[HermNorm.pointOf_smul']`. Establish `hsum : ∑ j : Fin m, σ (u j) * (t • h.pointOf x) j = t * ∑ j : Fin m, σ (u j) * h.pointOf x j`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [fsLog]`.

Rewrite using `[hsum, HermNorm.dualNorm_smul, norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]`. Establish `hpc : Continuous fun y : EuclideanSpace ℂ (Fin m) => h.pointOf y`. Unfold `HermNorm.pointOf`. Use `fun_prop`. Establish `hℓm : Measurable fun y : EuclideanSpace ℂ (Fin m) => fsLog h (fun k => σ (u k)) (h.pointOf y)`.

Simplify using `only [GroundTheory.Heights₂.Heights.ConeFsLog.fsLog_pointOf]`. Establish `hc : Continuous fun y : EuclideanSpace ℂ (Fin m) => ∑ j : Fin m, σ (u j) * h.pointOf y j` using `continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hpc)`. Conclude with `Real.measurable_log.comp (hc.norm.measurable.div measurable_norm)`. Establish `hgm : Measurable fun y : CxPts p (σ.comp (algebraMap (𝓞 K) K)) => fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y)`. Use `C.measurable_coords (h := h) (s := s) (p := p) (σ := σ.comp (algebraMap (𝓞 K) K)) hE.isLB hℓm hℓs` as an intermediate fact.

Simplify `this` using `only [C.pointOf_euc]`. Establish `hkey : ∀ G : ℝ → ℝ≥0∞, Measurable G → ∫⁻ y in coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)), G (fsLog h (fun k => σ (u k)) (h.pointOf y)) ∂μH[↑(2 * (e + 1))] = μH[↑(2 * (e + 1))] {y : EuclideanSpace ℂ (Fin m) | ‖y‖ < 1 ∧ ∀ j : Fin m, e + 1 ≤ ↑j → y.ofLp j = 0} * ∫⁻ y …`. Introduce `G hG`. Establish `hc` using `C.lintegral_cone hE hφ hFS hJzero hqh (hqc _) hμ0 (F := fun y => G (fsLog h (fun k => σ (u k)) (h.pointOf y))) (hG.comp hℓm) (fun t ht x => by`. Simplify using `only [hℓs t ht])`.

Rewrite using `[hc]`. Simplify using `only [C.pointOf_euc]`. Take `⟨-, hgint⟩` from `C.integral_of_lintegral (coordBall_mass hem).1.ne' (coordBall_mass hem).2.ne hgm hint hkey`. Prove the components needed by the constructor for the conclusion. Unfold `Weight.chernInt`.

Rewrite using `[C.chernPart_neg hE hφ hFS, Measure.restrict_zero, integral_zero_measure, sub_zero, setIntegral_eq_integral_of_forall_compl_eq_zero, hgint, hcyc]`. Both sides reduce to the same expression. Introduce `y hy`. Simplify using `only [Set.mem_setOf_eq, not_not] at hy`. Rewrite using `[fsLog, hy, norm_zero, zero_div, Real.log_zero]`.

Introduce `he0`. Substitute `he0` using the available equality. Establish `hch : ∀ y : CxPts p (σ.comp (algebraMap (𝓞 K) K)), ∃ c : AlgChart p (σ.comp (algebraMap (𝓞 K) K)) 0, y ∈ c.e.source`. Introduce `y`. Use `hqc _ y ?_` and prove the remaining obligations.

Conclude with `C.eval₂_loc_ne_zero (GlobalTheory.TwistTop.under_eq_genericPoint hAV y) (GlobalTheory.CxPts.mem_pick hE.isLB y) hqh hqP`. Rewrite using `[C.integral_zero hφ hch, hgint, hcyc]`. Both sides reduce to the same expression.
-/
theorem stArch (h1 : StPts) (h2 : StCharts) : StArch := by
  unfold StArch
  intro K _ _ Z _ p B m s e hE hAV hChow hproj σ φ h hφ hFS u hu
  obtain ⟨f, hf⟩ := hChow
  haveI : CompactSpace (CxPts p (σ.comp (algebraMap (𝓞 K) K))) := hAV.compactSpace _
  haveI : SecondCountableTopology (CxPts p (σ.comp (algebraMap (𝓞 K) K))) :=
    GlobalTheory.CxPts.secondCountableTopology_of_isProjOver _ hAV.isProjOver
  obtain ⟨hem, hint, hcyc, hnull⟩ := C.cone_side hproj hf σ h hu
  obtain ⟨n, q, hqh, hqP, hqc⟩ := h2 K Z p B m s e hE hAV
  have hPprime : (ptIdeal p s (genericPoint Z)).IsPrime :=
    ((h1 (𝓞 K) Z p B m s hE).1 (genericPoint Z)).isPrime
  have hq' : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ genIdeal p s :=
    C.map_notMem hPprime hproj.isPrime.ne_top hqP
  have hJzero : ∀ x : Fin m → ℂ,
      (∀ r ∈ Ideal.map (MvPolynomial.map σ) (genIdeal p s), MvPolynomial.eval x r = 0) ↔
        ∀ r ∈ ptIdeal p s (genericPoint Z), eval₂ (σ.comp (algebraMap (𝓞 K) K)) x r = 0 := by
    intro x
    constructor
    · intro hx r hr
      have hx' := hx _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
      rw [MvPolynomial.map_map, MvPolynomial.eval_map] at hx'
      exact hx'
    · intro hx r hr
      have hle : Ideal.map (MvPolynomial.map σ) (genIdeal p s) ≤ RingHom.ker (MvPolynomial.eval x) := by
        rw [Ideal.map_le_iff_le_comap, genIdeal, Ideal.map_le_iff_le_comap]
        intro r' hr'
        rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.map_map, MvPolynomial.eval_map]
        exact hx r' hr'
      exact hle hr
  have hμ0 : μH[↑(2 * (e + 1))] ({0} ∪ coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)) ∩
      {y : EuclideanSpace ℂ (Fin m) | eval₂ (σ.comp (algebraMap (𝓞 K) K)) (h.pointOf y) q = 0}) = 0 := by
    refine measure_union_null (C.hausdorffMeasure_zero e) ?_
    refine measure_mono_null ?_ (hnull _ hq')
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, ?_⟩
    simp only [Set.mem_setOf_eq] at hy2 ⊢
    rw [MvPolynomial.map_map, MvPolynomial.eval_map]
    exact hy2
  have hℓs : ∀ t : ℂ, t ≠ 0 → ∀ x : EuclideanSpace ℂ (Fin m),
      fsLog h (fun k => σ (u k)) (h.pointOf (t • x)) = fsLog h (fun k => σ (u k)) (h.pointOf x) := by
    intro t ht x
    rw [HermNorm.pointOf_smul']
    have hsum : ∑ j : Fin m, σ (u j) * (t • h.pointOf x) j = t * ∑ j : Fin m, σ (u j) * h.pointOf x j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [fsLog]
    rw [hsum, HermNorm.dualNorm_smul, norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]
  have hpc : Continuous fun y : EuclideanSpace ℂ (Fin m) => h.pointOf y := by
    unfold HermNorm.pointOf
    fun_prop
  have hℓm : Measurable fun y : EuclideanSpace ℂ (Fin m) => fsLog h (fun k => σ (u k)) (h.pointOf y) := by
    simp only [GroundTheory.Heights₂.Heights.ConeFsLog.fsLog_pointOf]
    have hc : Continuous fun y : EuclideanSpace ℂ (Fin m) => ∑ j : Fin m, σ (u j) * h.pointOf y j :=
      continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hpc)
    exact Real.measurable_log.comp (hc.norm.measurable.div measurable_norm)
  have hgm : Measurable fun y : CxPts p (σ.comp (algebraMap (𝓞 K) K)) =>
      fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y) := by
    have := C.measurable_coords (h := h) (s := s) (p := p) (σ := σ.comp (algebraMap (𝓞 K) K)) hE.isLB hℓm hℓs
    simpa only [C.pointOf_euc] using this
  have hkey : ∀ G : ℝ → ℝ≥0∞, Measurable G →
      ∫⁻ y in coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)),
          G (fsLog h (fun k => σ (u k)) (h.pointOf y)) ∂μH[↑(2 * (e + 1))] =
        μH[↑(2 * (e + 1))] {y : EuclideanSpace ℂ (Fin m) | ‖y‖ < 1 ∧ ∀ j : Fin m, e + 1 ≤ ↑j → y.ofLp j = 0} *
          ∫⁻ y, G (fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y))
            ∂φ.chernPart e 1 := by
    intro G hG
    have hc := C.lintegral_cone hE hφ hFS hJzero hqh (hqc _) hμ0
      (F := fun y => G (fsLog h (fun k => σ (u k)) (h.pointOf y))) (hG.comp hℓm) (fun t ht x => by
        simp only [hℓs t ht])
    rw [hc]
    simp only [C.pointOf_euc]
  obtain ⟨-, hgint⟩ := C.integral_of_lintegral (coordBall_mass hem).1.ne' (coordBall_mass hem).2.ne hgm hint hkey
  constructor
  · unfold Weight.chernInt
    rw [C.chernPart_neg hE hφ hFS, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero, hgint, hcyc]
    · rfl
    · intro y hy
      simp only [Set.mem_setOf_eq, not_not] at hy
      rw [fsLog, hy, norm_zero, zero_div, Real.log_zero]
  · intro he0
    subst he0
    have hch : ∀ y : CxPts p (σ.comp (algebraMap (𝓞 K) K)), ∃ c : AlgChart p (σ.comp (algebraMap (𝓞 K) K)) 0,
        y ∈ c.e.source := by
      intro y
      refine hqc _ y ?_
      exact C.eval₂_loc_ne_zero (GlobalTheory.TwistTop.under_eq_genericPoint hAV y) (GlobalTheory.CxPts.mem_pick hE.isLB y) hqh hqP
    rw [C.integral_zero hφ hch, hgint, hcyc]
    rfl

end ChowFormHeightComparison₂.CF
