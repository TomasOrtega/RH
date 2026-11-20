import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianNondegRepresentsNonzeroScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.NullSets

/- English proof (translation)
Establish `hT : MeasurableSet {p : G × ℝ | φ p.2 + p.1 ∈ S}` using `((hφ.comp measurable_snd).add measurable_fst) hS`. Establish `h1 : (μ.prod (volume : Measure ℝ)) {p : G × ℝ | φ p.2 + p.1 ∈ S} = 0`. Rewrite using `[Measure.prod_apply hT]`. Establish `: ∀ x, (volume : Measure ℝ) (Prod.mk x ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = 0` using `h`. Conclude with `(lintegral_congr (g := fun _ => 0) this).trans (by simp)`.

Rewrite `h1` using `[Measure.prod_apply_symm hT]`. Establish `h2 : ∀ t : ℝ, μ ((fun x => (x, t)) ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = μ S` using `fun t => measure_preimage_add μ (φ t) S`. Simplify using `only [h2, lintegral_const, measure_univ, Real.volume_univ] at h1`. Assume the negation of the conclusion as `hne`. Simplify using `[hne] at h1`.
-/
theorem null_of_lines {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] (φ : ℝ → G) (hφ : Measurable φ) {S : Set G}
    (hS : MeasurableSet S) (h : ∀ x, (volume : Measure ℝ) {t | φ t + x ∈ S} = 0) : μ S = 0 := by
  have hT : MeasurableSet {p : G × ℝ | φ p.2 + p.1 ∈ S} :=
    ((hφ.comp measurable_snd).add measurable_fst) hS
  have h1 : (μ.prod (volume : Measure ℝ)) {p : G × ℝ | φ p.2 + p.1 ∈ S} = 0 := by
    rw [Measure.prod_apply hT]
    have : ∀ x, (volume : Measure ℝ) (Prod.mk x ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = 0 := h
    exact (lintegral_congr (g := fun _ => 0) this).trans (by simp)
  rw [Measure.prod_apply_symm hT] at h1
  have h2 : ∀ t : ℝ, μ ((fun x => (x, t)) ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = μ S :=
    fun t => measure_preimage_add μ (φ t) S
  simp only [h2, lintegral_const, measure_univ, Real.volume_univ] at h1
  by_contra hne
  simp [hne] at h1

section Line

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `set y : Fin M → R ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i) with hy`. Establish `hs : ∀ e : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (σ e)` using `fun e => rfl`. Establish `hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = algebraMap R (R ⊗[F] E) (algebraMap F R a)`. Establish `: Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0)`.

Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul, y, hs, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, RingHom.coe_coe]`. Rewrite using `[this, hy0, ← IsScalarTower.algebraMap_apply]`. Conclude with `(Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a`. Establish `hrk : Module.finrank R (R ⊗[F] E) = 2`. Rewrite using `[Module.finrank_baseChange, hσ.2.2.1]`.

Establish `hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y = algebraMap F R a`. Rewrite using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, hyy, Algebra.trace_algebraMap, hrk, ← map_nsmul, ← map_mul]`. Use `congr 1`. Rewrite using `[nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hst : ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t`. Introduce `t`. Use `show t ⊗ₜ[F] σ 1 = _`. Rewrite using `[map_one]`.

Both sides reduce to the same expression. Use `⟨algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x), fun t => ?_⟩` and prove the remaining obligations. Establish `e : t • y = algebraMap R (R ⊗[F] E) t • y`. Rewrite using `[algebraMap_smul]`. Rewrite using `[← hq]`.

Unfold `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR`. Generalize the expression as in `algebraMap F R (1 / 2) = u`. Rewrite using `[e, GlobalTheory.HermLineZeros.hform_expand, hst, mul_assoc (algebraMap R (R ⊗[F] E) t)]`. Simplify using `only [← Algebra.smul_def, map_add, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_line (hσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y0 : Fin M → E) (a : F)
    (hy0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0 = algebraMap F E a) (R : Type) [CommRing R] [Nontrivial R] [Algebra F R]
    (x : Fin M → R ⊗[F] E) :
    ∃ c : R, ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (x + t • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i)) =
      algebraMap F R a * t ^ 2 + c * t + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J x := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set y : Fin M → R ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i) with hy
  have hs : ∀ e : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (σ e) := fun e => rfl
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0) := by
      simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul, y, hs, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply,
        RingHom.coe_coe]
    rw [this, hy0, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have hrk : Module.finrank R (R ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hσ.2.2.1]
  have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y = algebraMap F R a := by
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, hyy, Algebra.trace_algebraMap, hrk, ← map_nsmul, ← map_mul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hst : ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl
  refine ⟨algebraMap F R (1 / 2) *
    Algebra.trace R (R ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x), fun t => ?_⟩
  have e : t • y = algebraMap R (R ⊗[F] E) t • y := by
    rw [algebraMap_smul]
  rw [← hq]
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR
  generalize algebraMap F R (1 / 2) = u
  rw [e, GlobalTheory.HermLineZeros.hform_expand, hst, mul_assoc (algebraMap R (R ⊗[F] E) t)]
  simp only [← Algebra.smul_def, map_add, map_smul, smul_eq_mul]
  ring

end Line

section Coord

open GlobalTheory.CompanionTheory.SW.RealCoord

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def diag (t : ℝ) : Ainf F := (coordHomeo F).symm fun _ => t

/- English proof (translation)
The claim follows from `(coordHomeo F).symm.continuous.comp (continuous_pi fun _ => continuous_id)`.
-/
theorem continuous_diag : Continuous (diag F) :=
  (coordHomeo F).symm.continuous.comp (continuous_pi fun _ => continuous_id)

/- English proof (translation)
Establish `h : coordHomeo F (diag F t) = fun _ => t` using `(coordHomeo F).apply_symm_apply _`. Rewrite `h` using `[coordHomeo_coe]`. Conclude with `congrFun h w`.
-/
theorem coord_diag (t : ℝ) (w : InfinitePlace F) : coord F (diag F t) w = t := by
  have h : coordHomeo F (diag F t) = fun _ => t := (coordHomeo F).apply_symm_apply _
  rw [coordHomeo_coe] at h
  exact congrFun h w

/- English proof (translation)
Establish `h : Continuous (coord F)` using `(isHomeomorph_coord F).continuous`. Conclude with `(continuous_apply w).comp h`.
-/
theorem continuous_coord (w : InfinitePlace F) : Continuous fun c : Ainf F => coord F c w := by
  have h : Continuous (coord F) := (isHomeomorph_coord F).continuous
  exact (continuous_apply w).comp h

/- English proof (translation)
Establish `sub : {X | ¬ IsUnit (f X)} ⊆ ⋃ w, {X | coord F (f X) w = 0}`. Introduce `X hX`. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hc`. Apply `hX` to reduce the goal to its premises.

Establish `h1 : IsUnit (coord F (f X))` using `Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (hc w)`. Conclude with `(isUnit_map_iff (coord F) _).1 h1`. Use `measure_mono_null sub (measure_iUnion_null fun w => ?_)` and prove the remaining obligations. Conclude with `null_of_lines μ φ hφ (hf w (measurableSet_singleton 0)) fun x => (h x w).measure_zero _`.
-/
theorem null_nonunit {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] (f : G → Ainf F)
    (hf : ∀ w, Measurable fun X => coord F (f X) w) (φ : ℝ → G) (hφ : Measurable φ)
    (h : ∀ x w, {t : ℝ | coord F (f (φ t + x)) w = 0}.Finite) : μ {X | ¬ IsUnit (f X)} = 0 := by
  have sub : {X | ¬ IsUnit (f X)} ⊆ ⋃ w, {X | coord F (f X) w = 0} := by
    intro X hX
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hc
    apply hX
    have h1 : IsUnit (coord F (f X)) := Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (hc w)
    exact (isUnit_map_iff (coord F) _).1 h1
  refine measure_mono_null sub (measure_iUnion_null fun w => ?_)
  exact null_of_lines μ φ hφ (hf w (measurableSet_singleton 0)) fun x => (h x w).measure_zero _

end Coord

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hM μ ν hμ hν`. Use `haveI : IsTotallyReal F := hσ.1`. Take `⟨hR1, hLC, hSC, hT2, -⟩` from `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1`. Use `haveI := hR1`. Use `haveI := hLC`.

Use `haveI := hSC`. Use `haveI := hT2`. Use `haveI hB : BorelSpace (Ainf F) := ⟨rfl⟩`. Take `⟨p1, p2, p3, p4, -, p6, -, p8, -, p10⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)`. Use `haveI := p1`.

Use `haveI := p2`. Use `haveI := p3`. Use `haveI := p4`. Use `haveI hB2 := p8 1 M`. Use `haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Ainf F)`.

Use `haveI : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul (Ainf F) _`. Establish `hc` using `fun w => GlobalTheory.CompanionTheory.SW.NullSets.continuous_coord F w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `null_nonunit F ν id (fun w => (hc w).measurable) (diag F) (continuous_diag F).measurable ?_` and prove the remaining obligations. Introduce `x w`.

Use `(Set.finite_singleton (-RealCoord.coord F x w)).subset fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, id, map_add, Pi.add_apply, coord_diag] at ht`. Simplify using `only [Set.mem_singleton_iff]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨y0, a, ha, hy0⟩` from `GlobalTheory.HermLineZeros.exists_anisotropic hσ hM hJ set y : Fin M → Ainf F ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf F) (y0 i) with hy`.

Establish `hcont : Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0)` using `continuous_const.mul (p6.comp ((p10 1 M J).matrix_elem 0 0))`. Use `null_nonunit F μ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0)) (fun w => ((hc w).comp hcont).measurable) (fun t _ => diag F t • y) ?_ ?_` and prove the remaining obligations. Use `Continuous.measurable (continuous_pi fun _ => continuous_pi fun i => ?_)` and prove the remaining obligations. Conclude with `(continuous_diag F).smul continuous_const`. Introduce `x w`.

Take `⟨c, hc'⟩` from `q_line hσ J y0 a hy0 (Ainf F) (x 0)`. Use `set C := RealCoord.coord F c w`. Use `set Q := RealCoord.coord F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (x 0)) w`. Establish `hne : (Polynomial.C (RealCoord.rho F w a) * Polynomial.X ^ 2 + Polynomial.C C * Polynomial.X + Polynomial.C Q : Polynomial ℝ) ≠ 0`. Introduce `h0`.

Use `congrArg (fun p => Polynomial.coeff p 2) h0` as an intermediate fact. Simplify using `[Polynomial.coeff_X, Polynomial.coeff_C] at this`. Conclude with `ha this`. Use `(Polynomial.finite_setOf_isRoot hne).subset fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at ht`.

Establish `e : (diag F t • y + x 0) = x 0 + diag F t • y` using `add_comm _ _`. Establish `e2 : (fun _ : Fin 1 => diag F t • y) + x = fun i => (fun _ : Fin 1 => diag F t • y) i + x i` using `rfl`. Rewrite `ht` using `[e2]`. Simplify using `only [e] at ht`. Rewrite `ht` using `[hc' (diag F t)]`.

Simplify using `only [map_add, map_mul, map_pow, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, coord_diag, RealCoord.coord_algebraMap] at ht`. Simplify `ht` using `[Polynomial.IsRoot]`.
-/
theorem null_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0)) X)} = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ ν hμ hν
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨hR1, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI := hR1
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨p1, p2, p3, p4, -, p6, -, p8, -, p10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := p1
  haveI := p2
  haveI := p3
  haveI := p4
  haveI hB2 := p8 1 M
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Ainf F)
  haveI : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul (Ainf F) _
  have hc := fun w => GlobalTheory.CompanionTheory.SW.NullSets.continuous_coord F w
  refine ⟨?_, ?_⟩
  · refine null_nonunit F ν id (fun w => (hc w).measurable) (diag F) (continuous_diag F).measurable ?_
    intro x w
    refine (Set.finite_singleton (-RealCoord.coord F x w)).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, id, map_add, Pi.add_apply, coord_diag] at ht
    simp only [Set.mem_singleton_iff]
    linarith
  · obtain ⟨y0, a, ha, hy0⟩ := GlobalTheory.HermLineZeros.exists_anisotropic hσ hM hJ
    set y : Fin M → Ainf F ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf F) (y0 i) with hy
    have hcont : Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0) :=
      continuous_const.mul (p6.comp ((p10 1 M J).matrix_elem 0 0))
    refine null_nonunit F μ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0))
      (fun w => ((hc w).comp hcont).measurable) (fun t _ => diag F t • y) ?_ ?_
    · refine Continuous.measurable (continuous_pi fun _ => continuous_pi fun i => ?_)
      exact (continuous_diag F).smul continuous_const
    · intro x w
      obtain ⟨c, hc'⟩ := q_line hσ J y0 a hy0 (Ainf F) (x 0)
      set C := RealCoord.coord F c w
      set Q := RealCoord.coord F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (x 0)) w
      have hne : (Polynomial.C (RealCoord.rho F w a) * Polynomial.X ^ 2 + Polynomial.C C * Polynomial.X
          + Polynomial.C Q : Polynomial ℝ) ≠ 0 := by
        intro h0
        have := congrArg (fun p => Polynomial.coeff p 2) h0
        simp [Polynomial.coeff_X, Polynomial.coeff_C] at this
        exact ha this
      refine (Polynomial.finite_setOf_isRoot hne).subset fun t ht => ?_
      simp only [Set.mem_setOf_eq] at ht
      have e : (diag F t • y + x 0) = x 0 + diag F t • y := add_comm _ _
      have e2 : (fun _ : Fin 1 => diag F t • y) + x = fun i => (fun _ : Fin 1 => diag F t • y) i + x i := rfl
      rw [e2] at ht
      simp only [e] at ht
      rw [hc' (diag F t)] at ht
      simp only [map_add, map_mul, map_pow, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        coord_diag, RealCoord.coord_algebraMap] at ht
      simpa [Polynomial.IsRoot] using ht

end GlobalTheory.CompanionTheory.SW.NullSets
