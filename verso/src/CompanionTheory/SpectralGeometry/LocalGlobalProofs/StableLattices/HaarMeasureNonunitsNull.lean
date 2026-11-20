import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianNondegRepresentsNonzeroScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.SW.NullV

/- English proof (translation)
Establish `hcov : Z = ⋃ n, Z ∩ compactCovering V n`. Rewrite using `[← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]`. Rewrite using `[hcov]`. Use `measure_iUnion_null fun n => ?_` and prove the remaining obligations. Establish `hC : IsCompact (compactCovering V n)` using `isCompact_compactCovering V n`.

Generalize the expression as in `compactCovering V n = C at hC`. Establish `hZ' : MeasurableSet (Z ∩ C)` using `hZ.inter hC.measurableSet`. Establish `hT : IsCompact (insert (0 : V) (Set.range u))` using `hu.isCompact_insert_range`. Establish `hD : IsCompact (C + insert (0 : V) (Set.range u))` using `hC.add hT`. Generalize the expression as in `hDdef : C + insert (0 : V) (Set.range u) = D at hD`.

Establish `hDm : MeasurableSet D` using `hD.measurableSet`. Establish `hDfin : μ D ≠ ∞` using `hD.measure_lt_top.ne`. Assume the negation of the conclusion as `h0`. Take `⟨N, hN⟩` from `ENNReal.exists_nat_mul_gt h0 (b := 2 * μ D) (ENNReal.mul_ne_top (by simp) hDfin)`. Establish `hA : ∀ i, MeasurableSet ((fun x => x - u i) ⁻¹' (Z ∩ C))` using `fun i => (measurable_sub_const (u i)) hZ'`.

Establish `hpt : ∀ x, ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ≤ D.indicator (fun _ => (2 : ℝ≥0∞)) x`. Introduce `x`. Establish `hsum : ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x = (((Finset.range N).filter fun i => x - u i ∈ Z ∩ C).card : ℝ≥0∞)`. Simplify using `only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]`. Rewrite using `[Finset.sum_boole]`.

Rewrite using `[hsum]`. Distinguish the cases in `hs : ((Finset.range N).filter fun i => x - u i ∈ Z ∩ C) = ∅`. Rewrite using `[hs]`. Simplify using the standard rewrite rules. Take `⟨i, hi⟩` from `Finset.nonempty_iff_ne_empty.2 hs`.

Establish `hxD : x ∈ D`. Rewrite using `[← hDdef]`. Use `Set.mem_add.2 ⟨x - u i, (Finset.mem_filter.1 hi).2.2, u i, Or.inr ⟨i, rfl⟩, by abel⟩` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem hxD]`. Use `hov x ((Finset.range N).filter fun i => x - u i ∈ Z ∩ C) (fun i hi => (Finset.mem_filter.1 hi).2.1)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `key : (N : ℝ≥0∞) * μ (Z ∩ C) ≤ 2 * μ D`. Combine the equalities or inequalities in the displayed calculation. Establish `: ∀ i, μ ((fun x => x - u i) ⁻¹' (Z ∩ C)) = μ (Z ∩ C)`. Introduce `i`.

Simplify using `only [sub_eq_add_neg]`. Conclude with `measure_preimage_add_right μ (-u i) (Z ∩ C)`. Rewrite using `[Finset.sum_congr rfl fun i _ => this i]`. Simplify using the standard rewrite rules. Use `_ = ∑ i ∈ Finset.range N, ∫⁻ x, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ∂μ := by`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_indicator_one (hA i)]`. Use `_ = ∫⁻ x, ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ∂μ := by`. Rewrite using `[lintegral_finsetSum]`. Introduce `i _`.

Conclude with `measurable_one.indicator (hA i)`. Use `_ ≤ ∫⁻ x, D.indicator (fun _ => (2 : ℝ≥0∞)) x ∂μ := lintegral_mono hpt`. Use `_ = 2 * μ D := by`. Rewrite using `[lintegral_indicator hDm, lintegral_const, Measure.restrict_apply_univ]`. Conclude with `absurd hN (not_lt.2 key)`.
-/
theorem null_of_overlap {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {Z : Set V} (hZ : MeasurableSet Z) (u : ℕ → V)
    (hu : Filter.Tendsto u Filter.atTop (𝓝 0))
    (hov : ∀ (x : V) (s : Finset ℕ), (∀ i ∈ s, x - u i ∈ Z) → s.card ≤ 2) : μ Z = 0 := by
  classical
  have hcov : Z = ⋃ n, Z ∩ compactCovering V n := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  rw [hcov]
  refine measure_iUnion_null fun n => ?_
  have hC : IsCompact (compactCovering V n) := isCompact_compactCovering V n
  generalize compactCovering V n = C at hC
  have hZ' : MeasurableSet (Z ∩ C) := hZ.inter hC.measurableSet
  have hT : IsCompact (insert (0 : V) (Set.range u)) := hu.isCompact_insert_range
  have hD : IsCompact (C + insert (0 : V) (Set.range u)) := hC.add hT
  generalize hDdef : C + insert (0 : V) (Set.range u) = D at hD
  have hDm : MeasurableSet D := hD.measurableSet
  have hDfin : μ D ≠ ∞ := hD.measure_lt_top.ne
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 (b := 2 * μ D) (ENNReal.mul_ne_top (by simp) hDfin)
  have hA : ∀ i, MeasurableSet ((fun x => x - u i) ⁻¹' (Z ∩ C)) :=
    fun i => (measurable_sub_const (u i)) hZ'
  have hpt : ∀ x, ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ≤
      D.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    intro x
    have hsum : ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x =
        (((Finset.range N).filter fun i => x - u i ∈ Z ∩ C).card : ℝ≥0∞) := by
      simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
      rw [Finset.sum_boole]
    rw [hsum]
    by_cases hs : ((Finset.range N).filter fun i => x - u i ∈ Z ∩ C) = ∅
    · rw [hs]; simp
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
      have hxD : x ∈ D := by
        rw [← hDdef]
        refine Set.mem_add.2 ⟨x - u i, (Finset.mem_filter.1 hi).2.2, u i, Or.inr ⟨i, rfl⟩, by abel⟩
      rw [Set.indicator_of_mem hxD]
      have := hov x ((Finset.range N).filter fun i => x - u i ∈ Z ∩ C)
        (fun i hi => (Finset.mem_filter.1 hi).2.1)
      exact_mod_cast this
  have key : (N : ℝ≥0∞) * μ (Z ∩ C) ≤ 2 * μ D := by
    calc (N : ℝ≥0∞) * μ (Z ∩ C)
        = ∑ i ∈ Finset.range N, μ ((fun x => x - u i) ⁻¹' (Z ∩ C)) := by
          have : ∀ i, μ ((fun x => x - u i) ⁻¹' (Z ∩ C)) = μ (Z ∩ C) := by
            intro i
            simp only [sub_eq_add_neg]
            exact measure_preimage_add_right μ (-u i) (Z ∩ C)
          rw [Finset.sum_congr rfl fun i _ => this i]
          simp
      _ = ∑ i ∈ Finset.range N, ∫⁻ x, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_indicator_one (hA i)]
      _ = ∫⁻ x, ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ∂μ := by
          rw [lintegral_finsetSum]
          intro i _
          exact measurable_one.indicator (hA i)
      _ ≤ ∫⁻ x, D.indicator (fun _ => (2 : ℝ≥0∞)) x ∂μ := lintegral_mono hpt
      _ = 2 * μ D := by
          rw [lintegral_indicator hDm, lintegral_const, Measure.restrict_apply_univ]
  exact absurd hN (not_lt.2 key)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩` from `Finset.two_lt_card.1 (not_le.1 hc)`. Establish `h1` using `h i hi`. Establish `h2` using `h j hj`. Establish `h3` using `h k hk`.

Establish `e12 : (r i - r j) * (b + (r i + r j) * q) = 0` using `by linear_combination h1 - h2`. Establish `e13 : (r i - r k) * (b + (r i + r k) * q) = 0` using `by linear_combination h1 - h3`. Establish `f12` using `(mul_eq_zero.1 e12).resolve_left (sub_ne_zero.2 fun e => hij (hr e))`. Establish `f13` using `(mul_eq_zero.1 e13).resolve_left (sub_ne_zero.2 fun e => hik (hr e))`. Establish `g : (r j - r k) * q = 0` using `by linear_combination f12 - f13`.

Conclude with `(mul_ne_zero (sub_ne_zero.2 fun e => hjk (hr e)) hq) g`.
-/
theorem card_le_two {K : Type} [Field K] (a b q : K) (hq : q ≠ 0) (r : ℕ → K)
    (hr : Function.Injective r) (s : Finset ℕ)
    (h : ∀ i ∈ s, a + r i * b + r i ^ 2 * q = 0) : s.card ≤ 2 := by
  by_contra hc
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.1 (not_le.1 hc)
  have h1 := h i hi
  have h2 := h j hj
  have h3 := h k hk
  have e12 : (r i - r j) * (b + (r i + r j) * q) = 0 := by linear_combination h1 - h2
  have e13 : (r i - r k) * (b + (r i + r k) * q) = 0 := by linear_combination h1 - h3
  have f12 := (mul_eq_zero.1 e12).resolve_left (sub_ne_zero.2 fun e => hij (hr e))
  have f13 := (mul_eq_zero.1 e13).resolve_left (sub_ne_zero.2 fun e => hik (hr e))
  have g : (r j - r k) * q = 0 := by linear_combination f12 - f13
  exact (mul_ne_zero (sub_ne_zero.2 fun e => hjk (hr e)) hq) g

section Line

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigR_algebraMap (s : R) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) s) = algebraMap R (R ⊗[F] E) s := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Establish `h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x x + algebraMap R (R ⊗[F] E) s * (Formali …`. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, map_add, map_mul, map_pow, sigR_algebraMap, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `ht : ∀ (c : R) (a : R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) c * a) = c * Algebra.trace R (R ⊗[F] E) a`.

Introduce `c a`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`. Rewrite using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, h, map_add, map_add, ht, ht, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qR_line [Module.Free F E] [Module.Finite F E] (x y : Fin M → R ⊗[F] E) (s : R) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J x +
        s * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x)) +
        s ^ 2 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (fun j => x j + algebraMap R (R ⊗[F] E) s * y j)
        (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x x +
        algebraMap R (R ⊗[F] E) s *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x) +
        algebraMap R (R ⊗[F] E) (s ^ 2) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, map_add, map_mul, map_pow, sigR_algebraMap,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have ht : ∀ (c : R) (a : R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) c * a) =
      c * Algebra.trace R (R ⊗[F] E) a := by
    intro c a
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, h, map_add, map_add, ht, ht, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR]
  ring

/- English proof (translation)
Establish `h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) R (x j)) (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x x) := by`. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 2`. Establish `h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by`.

Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `(Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β`. Rewrite using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b), Fintype.card_fin, ← map_nsmul, ← map_mul]`. Use `congr 1`. Rewrite using `[nsmul_eq_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem qR_rat [CharZero F] (b : Module.Basis (Fin 2) F E) (x : Fin M → E) (β : F)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x x = algebraMap F E β) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j)) = algebraMap F R β := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j))
      (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x x) := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (algebraMap F E β) =
      algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b),
    Fintype.card_fin, ← map_nsmul, ← map_mul]
  congr 1
  rw [nsmul_eq_mul]; push_cast; field_simp

end Line

section Place

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))`. Conclude with `NormedField.nhdsNE_neBot (0 : v.adicCompletion F)`.
-/
theorem nhdsNE_Fv : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

/- English proof (translation)
Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))`. Take `⟨x, hx0, hx1⟩` from `NormedField.exists_norm_lt_one (v.adicCompletion F)`. Use `⟨fun i => x ^ i, ?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `: ‖x‖ ^ i = ‖x‖ ^ j`.

Use `congrArg norm hij` as an intermediate fact. Simplify `this` using `only [norm_pow]`. Conclude with `(pow_right_strictAnti₀ hx0 hx1).injective this`.
-/
theorem exists_seq_Fv : ∃ t : ℕ → Fv F v, Function.Injective t ∧
    Filter.Tendsto t Filter.atTop (𝓝 0) := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one (v.adicCompletion F)
  refine ⟨fun i => x ^ i, ?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1⟩
  intro i j hij
  have : ‖x‖ ^ i = ‖x‖ ^ j := by
    have := congrArg norm hij
    simpa only [norm_pow] using this
  exact (pow_right_strictAnti₀ hx0 hx1).injective this

end Place

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hM v μ ν hμ hν`. Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := h1`. Use `haveI := h2`. Use `haveI := h3`.

Use `haveI := h4`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI : (𝓝[≠] (0 : Fv F v)).NeBot := nhdsNE_Fv F v`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)`. Use `haveI := a1`.

Use `haveI := a2`. Use `haveI := a3`. Use `haveI := a4`. Use `haveI := a8 1 M`. Prove the components needed by the constructor for the conclusion.

Establish `: {c : Fv F v | ¬ IsUnit c} = {0}`. Use extensionality with `c`. Simplify using `[isUnit_iff_ne_zero]`. Rewrite using `[this]`. Conclude with `measure_singleton 0`.

Take `⟨n, rfl⟩ : ∃ n, M = n + 1` from `⟨M - 1, by omega⟩`. Take `⟨β, y, hβ, hy⟩` from `GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ n J hJ`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `b : Module.Basis (Fin 2) F E` using `Module.finBasisOfFinrankEq F E hσ.2.2.1`. Use `haveI := GlobalTheory.CompanionTheory.SW.TopK.isModTop (F := F) (E := E) (Fv F v)`.

Use `haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _`. Take `⟨t, ht, htt⟩` from `exists_seq_Fv F v`. Set `w : Fin (n + 1) → Fv F v ⊗[F] E` to `fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Fv F v) (y j)`. Establish `hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w = algebraMap F (Fv F v) β` using `qR_rat (Fv F v) σ J b y β hy`. Establish `hq0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w ≠ 0`.

Rewrite using `[hq]`. Conclude with `(map_ne_zero _).2 hβ`. Set `φ : Fv F v → (Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E)` to `fun c _ j => algebraMap (Fv F v) (Fv F v ⊗[F] E) c * w j`. Establish `hφ : Continuous φ`. Use `continuous_pi fun _ => continuous_pi fun j => ?_` and prove the remaining obligations.

Conclude with `(continuous_algebraMap (Fv F v) (Fv F v ⊗[F] E)).mul continuous_const`. Establish `hφ0 : φ 0 = 0`. Use function extensionality and compare the values at `_ j`. Simplify using `[φ]`. Establish `hu : Filter.Tendsto (fun i => φ (t i)) Filter.atTop (𝓝 0)`.

Use `(hφ.tendsto 0).comp htt` as an intermediate fact. Rewrite `this` using `[hφ0]`. Then use the resulting hypothesis. Establish `hQ : Continuous fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)`. Establish `: Continuous fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E => HeckeCharacterZeroLocus.SiegelWeilU.gramR (Fv F v) σ J X 0 0` using `(a10 1 (n + 1) J).matrix_elem 0 0`. Conclude with `continuous_const.mul (a6.comp this)`.

Establish `hZ : MeasurableSet {X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E | ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))}`. Establish `: {X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E | ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))} = (fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' {0}`. Use extensionality with `X`. Simplify using `[isUnit_iff_ne_zero]`. Rewrite using `[this]`.

Conclude with `(isClosed_singleton.preimage hQ).measurableSet`. Use `null_of_overlap μ hZ (fun i => φ (t i)) hu ?_` and prove the remaining obligations. Introduce `X s hs`. Use `card_le_two (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (Fv F v) σ J (X 0) w + Formalism.MainNotions.GlobalT …` and prove the remaining obligations. Introduce `i hi`.

Establish `h` using `hs i hi`. Establish `h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J ((X - φ (t i)) 0) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `h (isUnit_iff_ne_zero.2 hne)`. Establish `e : (X - φ (t i)) 0 = fun j => X 0 j + algebraMap (Fv F v) (Fv F v ⊗[F] E) (- t i) * w j`.

Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `X 0 j - algebraMap (Fv F v) (Fv F v ⊗[F] E) (t i) * w j = _`. Rewrite using `[map_neg, neg_mul, sub_eq_add_neg]`. Rewrite `h'` using `[e, qR_line]`. Conclude with `h'`.
-/
theorem null_nonunits : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) X)} = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM v μ ν hμ hν
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : (𝓝[≠] (0 : Fv F v)).NeBot := nhdsNE_Fv F v
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  constructor
  · have : {c : Fv F v | ¬ IsUnit c} = {0} := by
      ext c
      simp [isUnit_iff_ne_zero]
    rw [this]
    exact measure_singleton 0
  · obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
    obtain ⟨β, y, hβ, hy⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ n J hJ
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hσ.2.2.1
    haveI := GlobalTheory.CompanionTheory.SW.TopK.isModTop (F := F) (E := E) (Fv F v)
    haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
    obtain ⟨t, ht, htt⟩ := exists_seq_Fv F v
    let w : Fin (n + 1) → Fv F v ⊗[F] E := fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Fv F v) (y j)
    have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w = algebraMap F (Fv F v) β :=
      qR_rat (Fv F v) σ J b y β hy
    have hq0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w ≠ 0 := by
      rw [hq]
      exact (map_ne_zero _).2 hβ
    let φ : Fv F v → (Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E) :=
      fun c _ j => algebraMap (Fv F v) (Fv F v ⊗[F] E) c * w j
    have hφ : Continuous φ := by
      refine continuous_pi fun _ => continuous_pi fun j => ?_
      exact (continuous_algebraMap (Fv F v) (Fv F v ⊗[F] E)).mul continuous_const
    have hφ0 : φ 0 = 0 := by
      funext _ j
      simp [φ]
    have hu : Filter.Tendsto (fun i => φ (t i)) Filter.atTop (𝓝 0) := by
      have := (hφ.tendsto 0).comp htt
      rwa [hφ0] at this
    have hQ : Continuous fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E =>
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0) := by
      have : Continuous fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E =>
          HeckeCharacterZeroLocus.SiegelWeilU.gramR (Fv F v) σ J X 0 0 := (a10 1 (n + 1) J).matrix_elem 0 0
      exact continuous_const.mul (a6.comp this)
    have hZ : MeasurableSet {X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E |
        ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))} := by
      have : {X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E |
          ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))} =
          (fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E =>
            Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' {0} := by
        ext X
        simp [isUnit_iff_ne_zero]
      rw [this]
      exact (isClosed_singleton.preimage hQ).measurableSet
    refine null_of_overlap μ hZ (fun i => φ (t i)) hu ?_
    intro X s hs
    refine card_le_two (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))
      (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (Fv F v) σ J (X 0) w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (Fv F v) σ J w (X 0)))
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w) hq0 (fun i => - t i)
      (fun i j e => ht (neg_injective e)) s ?_
    intro i hi
    have h := hs i hi
    have h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J ((X - φ (t i)) 0) = 0 := by
      by_contra hne
      exact h (isUnit_iff_ne_zero.2 hne)
    have e : (X - φ (t i)) 0 = fun j => X 0 j + algebraMap (Fv F v) (Fv F v ⊗[F] E) (- t i) * w j := by
      funext j
      change X 0 j - algebraMap (Fv F v) (Fv F v ⊗[F] E) (t i) * w j = _
      rw [map_neg, neg_mul, sub_eq_add_neg]
    rw [e, qR_line] at h'
    exact h'

end GlobalTheory.CompanionTheory.SW.NullV
