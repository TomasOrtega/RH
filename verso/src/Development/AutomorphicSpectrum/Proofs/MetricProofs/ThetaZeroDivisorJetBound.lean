import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.TorsOff

def proj {n : ℕ} (p : Fin n → ℝ) : Fin n → AddCircle (1 : ℝ) :=
  fun j => ((p j : ℝ) : AddCircle (1 : ℝ))

/- English proof (translation)
Introduce `x`. Use `choose p hp using fun j => QuotientAddGroup.mk_surjective (x j)`. Conclude with `⟨p, funext hp⟩`.
-/
theorem proj_surjective {n : ℕ} : Function.Surjective (proj (n := n)) := by
  intro x
  choose p hp using fun j => QuotientAddGroup.mk_surjective (x j)
  exact ⟨p, funext hp⟩

/- English proof (translation)
The claim follows from `continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)`.
-/
theorem continuous_proj {n : ℕ} : Continuous (proj (n := n)) :=
  continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `key : ∀ j, ∃ k : ℤ, p j - q j = k`. Introduce `j`. Establish `h1` using `congrFun h j`.

Establish `h2 : ((p j - q j : ℝ) : AddCircle (1 : ℝ)) = 0`. Rewrite using `[AddCircle.coe_sub]`. Conclude with `sub_eq_zero.2 h1`. Take `⟨k, hk⟩` from `(AddCircle.coe_eq_zero_iff 1).1 h2`. Conclude with `⟨k, by simpa using hk.symm⟩`.

Use `choose k hk using key`. Conclude with `⟨k, funext hk⟩`. Introduce and unpack `⟨k, hk⟩`. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun hk j`.

Simplify using `only [Pi.sub_apply] at h1`. Establish `h3 : p j = q j + k j` using `by linarith`. Simplify using `only [proj]`. Rewrite using `[h3, AddCircle.coe_add, TorsionEquidistribution.coe_intCast_eq_zero, add_zero]`.
-/
theorem proj_eq_iff {n : ℕ} {p q : Fin n → ℝ} :
    proj p = proj q ↔ ∃ k : Fin n → ℤ, p - q = fun α => (k α : ℝ) := by
  constructor
  · intro h
    have key : ∀ j, ∃ k : ℤ, p j - q j = k := by
      intro j
      have h1 := congrFun h j
      have h2 : ((p j - q j : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.2 h1
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 h2
      exact ⟨k, by simpa using hk.symm⟩
    choose k hk using key
    exact ⟨k, funext hk⟩
  · rintro ⟨k, hk⟩
    funext j
    have h1 := congrFun hk j
    simp only [Pi.sub_apply] at h1
    have h3 : p j = q j + k j := by linarith
    simp only [proj]
    rw [h3, AddCircle.coe_add, TorsionEquidistribution.coe_intCast_eq_zero, add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[proj]`.
-/
theorem proj_zero {n : ℕ} : proj (0 : Fin n → ℝ) = 0 := by
  funext j
  simp [proj]

/- English proof (translation)
Rewrite using `[← proj_zero, proj_eq_iff, sub_zero]`.
-/
theorem proj_eq_zero_iff {n : ℕ} {p : Fin n → ℝ} :
    proj p = 0 ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ) := by
  rw [← proj_zero, proj_eq_iff, sub_zero]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [proj, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← nsmul_eq_mul, AddCircle.coe_nsmul]`.
-/
theorem nsmul_proj {n : ℕ} (m : ℕ) (p : Fin n → ℝ) : m • proj p = proj ((m : ℝ) • p) := by
  funext j
  simp only [proj, Pi.smul_apply, smul_eq_mul]
  rw [← nsmul_eq_mul, AddCircle.coe_nsmul]

/- English proof (translation)
Establish `h1 : ‖((t : ℝ) : AddCircle (1 : ℝ))‖ = |t - round t|` using `UnitAddCircle.norm_eq`. Rewrite using `[h1]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Metric.le_infDist (Set.range_nonempty _)]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Rewrite using `[Real.dist_eq]`. Conclude with `round_le t k`. Establish `h2` using `Metric.infDist_le_dist_of_mem (x := t) (s := Set.range ((↑) : ℤ → ℝ)) (y := (round t : ℝ)) (Set.mem_range_self (round t))`. Rewrite `h2` using `[Real.dist_eq]`. Then use the resulting hypothesis.
-/
theorem norm_coe_eq_infDist (t : ℝ) :
    ‖((t : ℝ) : AddCircle (1 : ℝ))‖ = Metric.infDist t (Set.range ((↑) : ℤ → ℝ)) := by
  have h1 : ‖((t : ℝ) : AddCircle (1 : ℝ))‖ = |t - round t| := UnitAddCircle.norm_eq
  rw [h1]
  apply le_antisymm
  · rw [Metric.le_infDist (Set.range_nonempty _)]
    rintro _ ⟨k, rfl⟩
    rw [Real.dist_eq]
    exact round_le t k
  · have h2 := Metric.infDist_le_dist_of_mem (x := t) (s := Set.range ((↑) : ℤ → ℝ))
      (y := (round t : ℝ)) (Set.mem_range_self (round t))
    rwa [Real.dist_eq] at h2

/- English proof (translation)
Establish `hmp : ∀ _ : Fin n, MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) volume` using `fun _ => AddCircle.measurePreserving_mk 1 0`. Establish `hpi` using `measurePreserving_pi _ _ hmp`. Rewrite using `[volume_pi, ← hpi.measure_preimage hZ.nullMeasurableSet, ← Measure.restrict_pi_pi]`. Use `le_antisymm ?_ zero_le` and prove the remaining obligations. Use `(Measure.restrict_apply_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[← volume_pi]`. Conclude with `h.le`.
-/
theorem volume_eq_zero_of_proj {n : ℕ} {Z : Set (Fin n → AddCircle (1 : ℝ))}
    (hZ : MeasurableSet Z) (h : volume (proj ⁻¹' Z) = 0) : volume Z = 0 := by
  have hmp : ∀ _ : Fin n, MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) volume :=
    fun _ => AddCircle.measurePreserving_mk 1 0
  have hpi := measurePreserving_pi _ _ hmp
  rw [volume_pi, ← hpi.measure_preimage hZ.nullMeasurableSet, ← Measure.restrict_pi_pi]
  refine le_antisymm ?_ zero_le
  refine (Measure.restrict_apply_le _ _).trans ?_
  rw [← volume_pi]
  exact h.le

/- English proof (translation)
Establish `han` using `ReciprocityTheory.AnForm.Osgood.osgood g Set.univ θ isOpen_univ hθ.differentiableOn`. Establish `h0` using `ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ han ⟨w, Set.mem_univ _, hw⟩`. Establish `h0' : volume {z : Fin g → ℂ | θ z = 0} = 0` using `by simpa using h0`. Set `Lc : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)` to `L.toContinuousLinearEquiv`. Set `e : (Fin n → ℝ) ≃ᵐ (Fin g → ℂ)` to `Lc.toHomeomorph.toMeasurableEquiv`.

Establish `he : (e : (Fin n → ℝ) → Fin g → ℂ) = Lc` using `rfl`. Establish `hμ` using `Measure.isAddLeftInvariant_eq_smul (Measure.map Lc volume) (volume : Measure (Fin g → ℂ))`. Establish `h1 : (Measure.map Lc volume) {z : Fin g → ℂ | θ z = 0} = 0`. Rewrite using `[hμ, Measure.smul_apply, h0', smul_zero]`. Rewrite `h1` using `[← he, e.map_apply]`.

Conclude with `h1`.
-/
theorem volume_zero_set {n g : ℕ} {θ : (Fin g → ℂ) → ℂ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin g → ℂ))
    (hθ : Differentiable ℂ θ) {w : Fin g → ℂ} (hw : θ w ≠ 0) :
    volume {p : Fin n → ℝ | θ (L p) = 0} = 0 := by
  have han := ReciprocityTheory.AnForm.Osgood.osgood g Set.univ θ isOpen_univ hθ.differentiableOn
  have h0 := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ han
    ⟨w, Set.mem_univ _, hw⟩
  have h0' : volume {z : Fin g → ℂ | θ z = 0} = 0 := by simpa using h0
  let Lc : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ) := L.toContinuousLinearEquiv
  let e : (Fin n → ℝ) ≃ᵐ (Fin g → ℂ) := Lc.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → Fin g → ℂ) = Lc := rfl
  have hμ := Measure.isAddLeftInvariant_eq_smul (Measure.map Lc volume) (volume : Measure (Fin g → ℂ))
  have h1 : (Measure.map Lc volume) {z : Fin g → ℂ | θ z = 0} = 0 := by
    rw [hμ, Measure.smul_apply, h0', smul_zero]
  rw [← he, e.map_apply] at h1
  exact h1

section Lattice

variable {n g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} {θ : (Fin g → ℂ) → ℂ}
  {L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)}

def zeroSet (θ : (Fin g → ℂ) → ℂ) (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)) :
    Set (Fin n → AddCircle (1 : ℝ)) :=
  proj '' {p | θ (L p) = 0}

/- English proof (translation)
Take `⟨k, hk⟩` from `proj_eq_iff.1 h`. Establish `hmem : L (p - q) ∈ Λ` using `(hL _).2 ⟨k, hk⟩`. Establish `h1` using `hΛ _ hmem (L q)`. Rewrite `h1` using `[← map_add, add_comm, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem zero_iff_of_proj_eq (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) {p q : Fin n → ℝ} (h : proj p = proj q) :
    θ (L p) = 0 ↔ θ (L q) = 0 := by
  obtain ⟨k, hk⟩ := proj_eq_iff.1 h
  have hmem : L (p - q) ∈ Λ := (hL _).2 ⟨k, hk⟩
  have h1 := hΛ _ hmem (L q)
  rwa [← map_add, add_comm, sub_add_cancel] at h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, hqp⟩`. Conclude with `(zero_iff_of_proj_eq hL hΛ hqp).1 hq`. Conclude with `fun h => ⟨p, h, rfl⟩`.
-/
theorem proj_mem_zeroSet (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) (p : Fin n → ℝ) :
    proj p ∈ zeroSet θ L ↔ θ (L p) = 0 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact (zero_iff_of_proj_eq hL hΛ hqp).1 hq
  · exact fun h => ⟨p, h, rfl⟩

/- English proof (translation)
Establish `hLc : Continuous L` using `L.toLinearMap.continuous_of_finiteDimensional`. Establish `hcl : IsClosed {p : Fin n → ℝ | θ (L p) = 0}` using `isClosed_eq (hθ.comp hLc) continuous_const`. Establish `hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)` using `isCompact_univ_pi fun _ => isCompact_Icc`. Establish `hcomp` using `(hbox.inter_left hcl).image (continuous_proj (n := n))`. Establish `hEq : zeroSet θ L = proj '' ({p | θ (L p) = 0} ∩ Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `hq : proj (fun j => Int.fract (p j)) = proj p` using `proj_eq_iff.2 ⟨fun j => -⌊p j⌋, by`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.sub_apply, Int.cast_neg, Int.fract]`.

Use the proof step `ring⟩`. Use `⟨fun j => Int.fract (p j), ⟨?_, ?_⟩, hq⟩` and prove the remaining obligations. Conclude with `(zero_iff_of_proj_eq hL hΛ hq).2 hp`. Introduce `j _`. Conclude with `⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩`.

Conclude with `Set.image_mono Set.inter_subset_left`. Rewrite using `[hEq]`. Conclude with `hcomp.isClosed`.
-/
theorem isClosed_zeroSet (hθ : Continuous θ)
    (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) : IsClosed (zeroSet θ L) := by
  have hLc : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hcl : IsClosed {p : Fin n → ℝ | θ (L p) = 0} :=
    isClosed_eq (hθ.comp hLc) continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcomp := (hbox.inter_left hcl).image (continuous_proj (n := n))
  have hEq : zeroSet θ L =
      proj '' ({p | θ (L p) = 0} ∩ Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hq : proj (fun j => Int.fract (p j)) = proj p :=
        proj_eq_iff.2 ⟨fun j => -⌊p j⌋, by
          funext j
          simp only [Pi.sub_apply, Int.cast_neg, Int.fract]
          ring⟩
      refine ⟨fun j => Int.fract (p j), ⟨?_, ?_⟩, hq⟩
      · exact (zero_iff_of_proj_eq hL hΛ hq).2 hp
      · intro j _
        exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · exact Set.image_mono Set.inter_subset_left
  rw [hEq]
  exact hcomp.isClosed

/- English proof (translation)
Use `volume_eq_zero_of_proj (isClosed_zeroSet hθ.continuous hL hΛ).measurableSet ?_` and prove the remaining obligations. Establish `hpre : proj ⁻¹' zeroSet θ L = {p | θ (L p) = 0}`. Use extensionality with `p`. Conclude with `proj_mem_zeroSet hL hΛ p`. Rewrite using `[hpre]`.

Conclude with `volume_zero_set L hθ hw`.
-/
theorem volume_zeroSet (hθ : Differentiable ℂ θ) {w : Fin g → ℂ} (hw : θ w ≠ 0)
    (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) : volume (zeroSet θ L) = 0 := by
  refine volume_eq_zero_of_proj (isClosed_zeroSet hθ.continuous hL hΛ).measurableSet ?_
  have hpre : proj ⁻¹' zeroSet θ L = {p | θ (L p) = 0} := by
    ext p
    exact proj_mem_zeroSet hL hΛ p
  rw [hpre]
  exact volume_zero_set L hθ hw

/- English proof (translation)
Rewrite using `[map_smul]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.
-/
theorem natCast_smul_map (m : ℕ) (p : Fin n → ℝ) : (m : ℂ) • L p = L ((m : ℝ) • p) := by
  rw [map_smul]
  funext j
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `m • proj p = 0 ↔ _`. Rewrite using `[nsmul_proj, natCast_smul_map, hL, proj_eq_zero_iff]`.
-/
theorem proj_mem_torsion_iff (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (m : ℕ) (p : Fin n → ℝ) : proj p ∈ torusTorsion n m ↔ (m : ℂ) • L p ∈ Λ := by
  change m • proj p = 0 ↔ _
  rw [nsmul_proj, natCast_smul_map, hL, proj_eq_zero_iff]

/- English proof (translation)
Establish `hLc : Continuous L` using `L.toLinearMap.continuous_of_finiteDimensional`. Establish `hopen : IsOpen {p : Fin n → ℝ | θ (L p) ≠ 0}` using `isOpen_ne_fun (hθ.comp hLc) continuous_const`. Establish `hmem : L.symm w ∈ {p : Fin n → ℝ | θ (L p) ≠ 0}` using `by simpa using hw`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hopen _ hmem`. Establish `hev : ∀ᶠ m : ℕ in Filter.atTop, 1 / (m : ℝ) < ε` using `tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)`.

Use `filter_upwards [hev, Filter.eventually_gt_atTop 0] with m hm hm0`. Establish `hmR : (0 : ℝ) < m` using `Nat.cast_pos.2 hm0`. Use `⟨fun j => (⌊(m : ℝ) * L.symm w j⌋ : ℝ) / m, ⟨fun j => ⌊(m : ℝ) * L.symm w j⌋, ?_⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Apply `hball` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hε]`. Introduce `j`. Rewrite using `[Real.dist_eq]`.

Use `set x := L.symm w j`. Establish `h1` using `Int.floor_le ((m : ℝ) * x)`. Establish `h2` using `Int.lt_floor_add_one ((m : ℝ) * x)`. Establish `h3 : (⌊(m : ℝ) * x⌋ : ℝ) / m - x = ((⌊(m : ℝ) * x⌋ : ℝ) - m * x) / m`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h3, abs_div, abs_of_pos hmR]`. Use `lt_of_le_of_lt ?_ hm` and prove the remaining obligations. Apply `div_le_div_of_nonneg_right _ hmR.le` to reduce the goal to its premises. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem eventually_exists_off (hθ : Continuous θ) {w : Fin g → ℂ} (hw : θ w ≠ 0) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ p : Fin n → ℝ,
      (∃ k : Fin n → ℤ, (m : ℝ) • p = fun α => (k α : ℝ)) ∧ θ (L p) ≠ 0 := by
  have hLc : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hopen : IsOpen {p : Fin n → ℝ | θ (L p) ≠ 0} :=
    isOpen_ne_fun (hθ.comp hLc) continuous_const
  have hmem : L.symm w ∈ {p : Fin n → ℝ | θ (L p) ≠ 0} := by simpa using hw
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen _ hmem
  have hev : ∀ᶠ m : ℕ in Filter.atTop, 1 / (m : ℝ) < ε :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hev, Filter.eventually_gt_atTop 0] with m hm hm0
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm0
  refine ⟨fun j => (⌊(m : ℝ) * L.symm w j⌋ : ℝ) / m, ⟨fun j => ⌊(m : ℝ) * L.symm w j⌋, ?_⟩, ?_⟩
  · funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  · apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    rw [Real.dist_eq]
    set x := L.symm w j
    have h1 := Int.floor_le ((m : ℝ) * x)
    have h2 := Int.lt_floor_add_one ((m : ℝ) * x)
    have h3 : (⌊(m : ℝ) * x⌋ : ℝ) / m - x = ((⌊(m : ℝ) * x⌋ : ℝ) - m * x) / m := by
      field_simp
    rw [h3, abs_div, abs_of_pos hmR]
    refine lt_of_le_of_lt ?_ hm
    apply div_le_div_of_nonneg_right _ hmR.le
    rw [abs_le]
    constructor <;> linarith

/- English proof (translation)
Take `⟨w, hw⟩` from `hw`. Establish `hfull` using `TorsionEquidistribution.full n hn (zeroSet θ L) c₀ (isClosed_zeroSet hθ.continuous hL hΛ) (volume_zeroSet hθ hw hL hΛ) hc`. Use `filter_upwards [hfull, eventually_exists_off (L := L) hθ.continuous hw]`. Introduce and unpack `m h1 ⟨p, hp1, hp2⟩ Ix _ r hr hu`. Establish `hmp : (m : ℂ) • L p ∈ Λ`.

Rewrite using `[natCast_smul_map]`. Conclude with `(hL _).2 hp1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨i, -, -⟩` from `hu (L p) hmp hp2`. Conclude with `⟨i⟩`.

Set `f : Ix → Fin n → AddCircle (1 : ℝ)` to `fun i => proj (L.symm (r i))`. Establish `hinj : Function.Injective f`. Introduce `i j hij`. Take `⟨k, hk⟩` from `proj_eq_iff.1 hij`. Establish `hmem : r i - r j ∈ Λ`.

Establish `h2` using `(hL _).2 ⟨k, hk⟩`. Simplify using `using h2`. Take `⟨i', -, huniq⟩` from `hu (r i) (hr i).1 (hr i).2`. Rewrite using `[huniq i (by simp), huniq j hmem]`. Establish `hrange : Set.range f = torusTorsion n m \ zeroSet θ L`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[proj_mem_torsion_iff hL]`.

Simplify using `using (hr i).1`. Rewrite using `[proj_mem_zeroSet hL hΛ]`. Simplify using `using (hr i).2`. Introduce and unpack `⟨hx1, hx2⟩`. Take `⟨q, rfl⟩` from `proj_surjective x`.

Rewrite `hx1` using `[proj_mem_torsion_iff hL]`. Rewrite `hx2` using `[proj_mem_zeroSet hL hΛ]`. Take `⟨i, hi, -⟩` from `hu (L q) hx1 hx2`. Use `⟨i, (proj_eq_iff (p := q) (q := L.symm (r i))).2 ((hL _).1 ?_) |>.symm⟩` and prove the remaining obligations. Simplify using `using hi`.

Establish `hcard : Fintype.card Ix = (torusTorsion n m \ zeroSet θ L).ncard`. Rewrite using `[← hrange, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card]`. Establish `hnorm : ∀ i, ‖f i ⟨0, hn⟩ + (c₀ : AddCircle (1 : ℝ))‖ = Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ))`. Introduce `i`. Rewrite using `[← norm_coe_eq_infDist, AddCircle.coe_add]`.

Both sides reduce to the same expression. Establish `hgood : {x ∈ torusTorsion n m \ zeroSet θ L | (1 / 4 : ℝ) ≤ ‖x ⟨0, hn⟩ + (c₀ : AddCircle (1 : ℝ))‖} = f '' {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ))}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hx2⟩`.

Rewrite `hx` using `[← hrange]`. Take `⟨i, rfl⟩` from `hx`. Conclude with `⟨i, by simpa only [Set.mem_setOf_eq, ← hnorm] using hx2, rfl⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Use `⟨hrange ▸ Set.mem_range_self i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hnorm]`. Conclude with `hi`. Rewrite `h1` using `[hgood, Set.ncard_image_of_injective _ hinj]`. Rewrite using `[hcard]`. Conclude with `h1`.
-/
theorem core (hn : 0 < n) (c₀ : ℝ) (hθ : Differentiable ℂ θ) (hw : ∃ w, θ w ≠ 0)
    (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) (hc : ∃ k : ℤ, c₀ = k / 2) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ Λ ∧ θ (r i) ≠ 0) →
      (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → θ w ≠ 0 → ∃! i, w - r i ∈ Λ) →
      Nonempty Ix ∧ Fintype.card Ix ≤
        3 * {i | (1 / 4 : ℝ) ≤
          Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ))}.ncard := by
  obtain ⟨w, hw⟩ := hw
  have hfull := TorsionEquidistribution.full n hn (zeroSet θ L) c₀
    (isClosed_zeroSet hθ.continuous hL hΛ) (volume_zeroSet hθ hw hL hΛ) hc
  filter_upwards [hfull, eventually_exists_off (L := L) hθ.continuous hw]
  rintro m h1 ⟨p, hp1, hp2⟩ Ix _ r hr hu
  have hmp : (m : ℂ) • L p ∈ Λ := by
    rw [natCast_smul_map]
    exact (hL _).2 hp1
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, -⟩ := hu (L p) hmp hp2
    exact ⟨i⟩
  let f : Ix → Fin n → AddCircle (1 : ℝ) := fun i => proj (L.symm (r i))
  have hinj : Function.Injective f := by
    intro i j hij
    obtain ⟨k, hk⟩ := proj_eq_iff.1 hij
    have hmem : r i - r j ∈ Λ := by
      have h2 := (hL _).2 ⟨k, hk⟩
      simpa using h2
    obtain ⟨i', -, huniq⟩ := hu (r i) (hr i).1 (hr i).2
    rw [huniq i (by simp), huniq j hmem]
  have hrange : Set.range f = torusTorsion n m \ zeroSet θ L := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [proj_mem_torsion_iff hL]
        simpa using (hr i).1
      · rw [proj_mem_zeroSet hL hΛ]
        simpa using (hr i).2
    · rintro ⟨hx1, hx2⟩
      obtain ⟨q, rfl⟩ := proj_surjective x
      rw [proj_mem_torsion_iff hL] at hx1
      rw [proj_mem_zeroSet hL hΛ] at hx2
      obtain ⟨i, hi, -⟩ := hu (L q) hx1 hx2
      refine ⟨i, (proj_eq_iff (p := q) (q := L.symm (r i))).2 ((hL _).1 ?_) |>.symm⟩
      simpa using hi
  have hcard : Fintype.card Ix = (torusTorsion n m \ zeroSet θ L).ncard := by
    rw [← hrange, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card]
  have hnorm : ∀ i, ‖f i ⟨0, hn⟩ + (c₀ : AddCircle (1 : ℝ))‖ =
      Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ)) := by
    intro i
    rw [← norm_coe_eq_infDist, AddCircle.coe_add]
    rfl
  have hgood : {x ∈ torusTorsion n m \ zeroSet θ L |
        (1 / 4 : ℝ) ≤ ‖x ⟨0, hn⟩ + (c₀ : AddCircle (1 : ℝ))‖} =
      f '' {i | (1 / 4 : ℝ) ≤
        Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ))} := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      rw [← hrange] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, by simpa only [Set.mem_setOf_eq, ← hnorm] using hx2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hrange ▸ Set.mem_range_self i, ?_⟩
      rw [hnorm]
      exact hi
  rw [hgood, Set.ncard_image_of_injective _ hinj] at h1
  rw [hcard]
  exact h1

end Lattice

/- English proof (translation)
Introduce `g Λ θ L i₀ c₀ hθ hw hL hΛ hc`. Establish `hn : 0 < Fintype.card (Fin g ⊕ Fin g)` using `Fintype.card_pos_iff.2 ⟨i₀⟩`. Set `e0` to `Fintype.equivFin (Fin g ⊕ Fin g)`. Set `e : (Fin g ⊕ Fin g) ≃ Fin (Fintype.card (Fin g ⊕ Fin g))` to `e0.trans (Equiv.swap (e0 i₀) ⟨0, hn⟩)`. Establish `hi0 : e i₀ = ⟨0, hn⟩` using `by simp [e]`.

Set `L' : (Fin (Fintype.card (Fin g ⊕ Fin g)) → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)` to `(LinearEquiv.funCongrLeft ℝ ℝ e).trans L`. Establish `hL'a : ∀ q, L' q = L (q ∘ e)` using `fun _ => rfl`. Establish `hsymm : ∀ w, L'.symm w ⟨0, hn⟩ = L.symm w i₀`. Introduce `w`. Establish `h1 : (L'.symm w) ∘ e = L.symm w`.

Rewrite using `[LinearEquiv.eq_symm_apply, ← hL'a]`. Conclude with `L'.apply_symm_apply w`. Rewrite using `[← h1, Function.comp_apply, hi0]`. Establish `hL' : ∀ q, L' q ∈ Λ ↔ ∃ k : Fin (Fintype.card (Fin g ⊕ Fin g)) → ℤ, q = fun α => (k α : ℝ)`. Introduce `q`.

Rewrite using `[hL'a, hL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Use `⟨k ∘ e.symm, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`.

Simplify using `using congrFun hk (e.symm j)`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨k ∘ e, rfl⟩`. Use `filter_upwards [core (L := L') hn c₀ hθ hw hL' hΛ hc] with m hm Ix _ r h1 h2`. Simplify `hm Ix r h1 h2` using `only [hsymm]`.
-/
theorem torsion_off_zeros : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (θ : (Fin g → ℂ) → ℂ)
    (L : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)) (i₀ : Fin g ⊕ Fin g) (c₀ : ℝ),
    Differentiable ℂ θ → (∃ w, θ w ≠ 0) →
    (∀ p, L p ∈ Λ ↔ ∃ k : Fin g ⊕ Fin g → ℤ, p = fun α => (k α : ℝ)) →
    (∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) →
    (∃ k : ℤ, c₀ = k / 2) →
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ Λ ∧ θ (r i) ≠ 0) →
      (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → θ w ≠ 0 → ∃! i, w - r i ∈ Λ) →
      Nonempty Ix ∧ Fintype.card Ix ≤
        3 * {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) i₀ + c₀) (Set.range ((↑) : ℤ → ℝ))}.ncard := by
  intro g Λ θ L i₀ c₀ hθ hw hL hΛ hc
  have hn : 0 < Fintype.card (Fin g ⊕ Fin g) := Fintype.card_pos_iff.2 ⟨i₀⟩
  let e0 := Fintype.equivFin (Fin g ⊕ Fin g)
  let e : (Fin g ⊕ Fin g) ≃ Fin (Fintype.card (Fin g ⊕ Fin g)) :=
    e0.trans (Equiv.swap (e0 i₀) ⟨0, hn⟩)
  have hi0 : e i₀ = ⟨0, hn⟩ := by simp [e]
  let L' : (Fin (Fintype.card (Fin g ⊕ Fin g)) → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e).trans L
  have hL'a : ∀ q, L' q = L (q ∘ e) := fun _ => rfl
  have hsymm : ∀ w, L'.symm w ⟨0, hn⟩ = L.symm w i₀ := by
    intro w
    have h1 : (L'.symm w) ∘ e = L.symm w := by
      rw [LinearEquiv.eq_symm_apply, ← hL'a]
      exact L'.apply_symm_apply w
    rw [← h1, Function.comp_apply, hi0]
  have hL' : ∀ q, L' q ∈ Λ ↔ ∃ k : Fin (Fintype.card (Fin g ⊕ Fin g)) → ℤ,
      q = fun α => (k α : ℝ) := by
    intro q
    rw [hL'a, hL]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k ∘ e.symm, ?_⟩
      funext j
      simpa using congrFun hk (e.symm j)
    · rintro ⟨k, rfl⟩
      exact ⟨k ∘ e, rfl⟩
  filter_upwards [core (L := L') hn c₀ hθ hw hL' hΛ hc] with m hm Ix _ r h1 h2
  simpa only [hsymm] using hm Ix r h1 h2

end GlobalTheory.CompanionTheory.TorsOff
