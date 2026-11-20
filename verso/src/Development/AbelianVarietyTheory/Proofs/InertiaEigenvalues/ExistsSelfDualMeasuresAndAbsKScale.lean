import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal

noncomputable section

namespace GlobalTheory.JR.MeasScale

/- English proof (translation)
Simplify using `only [fourB]`. Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.
-/
theorem fourB_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) : fourB (c • μ) B f y = (c : ℂ) * fourB μ B f y := by
  simp only [fourB]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/- English proof (translation)
Simplify using `only [fourB, mul_assoc]`. Conclude with `integral_const_mul a _`.
-/
theorem fourB_const_mul {V : Type} [MeasurableSpace V] (μ : Measure V) (a : ℂ) (B : V → V → ℂ)
    (g : V → ℂ) (y : V) : fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

/- English proof (translation)
Establish `h : fourB (c • μ) B f = fun z => (c : ℂ) * fourB μ B f z`. Use function extensionality and compare the values at `fun z => fourB_nnreal_smul μ c B f z`. Rewrite using `[fourB_nnreal_smul, h, fourB_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourB_twice_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) :
    fourB (c • μ) B (fourB (c • μ) B f) y = (c : ℂ) ^ 2 * fourB μ B (fourB μ B f) y := by
  have h : fourB (c • μ) B f = fun z => (c : ℂ) * fourB μ B f z :=
    funext fun z => fourB_nnreal_smul μ c B f z
  rw [fourB_nnreal_smul, h, fourB_const_mul]
  ring

/- English proof (translation)
Take `⟨S, hSo, hSc, s, hs⟩` from `h`. Establish `hcl : IsClosed S` using `hSc.isClosed`. Use `⟨S.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, -s, ?_⟩` and prove the remaining obligations. Introduce `t`. Use `Set.indicator_const_preimage S t (1 : ℂ)` as an intermediate fact.

Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at this`. Apply the tactic sequence `rcases this with h1 | h1 | h1 | h1 <;> rw [h1]`. Conclude with `isOpen_univ`. Conclude with `hSo`. Conclude with `hcl.isOpen_compl`.

Conclude with `isOpen_empty`. Conclude with `HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _`. Simplify using `[hs]`.
-/
theorem exists_test_ne_zero {V : Type} [AddCommGroup V] [TopologicalSpace V] [T2Space V]
    (h : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) : ∃ f : V → ℂ, IsTest f ∧ ∃ y, f (-y) ≠ 0 := by
  obtain ⟨S, hSo, hSc, s, hs⟩ := h
  have hcl : IsClosed S := hSc.isClosed
  refine ⟨S.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, -s, ?_⟩
  · intro t
    have := Set.indicator_const_preimage S t (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact isOpen_univ
    · exact hSo
    · exact hcl.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _
  · simp [hs]

/- English proof (translation)
Take `⟨hμ, hF⟩` from `h`. Take `⟨hμ', hF'⟩` from `h'`. Establish `e` using `Measure.isAddLeftInvariant_eq_smul μ' μ`. Take `⟨f, hf, y, hy⟩` from `exists_test_ne_zero hS`. Establish `h1` using `hF' f hf y`.

Rewrite `h1` using `[e, fourB_twice_nnreal_smul, hF f hf y]`. Establish `hc : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℂ) ^ 2 = 1` using `mul_right_cancel₀ hy (h1.trans (one_mul _).symm)`. Establish `hc2 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) ^ 2 = 1` using `by exact_mod_cast hc`. Establish `hc0 : (0 : ℝ) ≤ (μ'.addHaarScalarFactor μ : ℝ≥0)` using `NNReal.coe_nonneg _`. Establish `hc1 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) = 1` using `by nlinarith`.

Establish `hc3 : μ'.addHaarScalarFactor μ = 1` using `by exact_mod_cast hc1`. Rewrite using `[e, hc3, one_smul]`.
-/
theorem selfDual_unique {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (hS : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) (B : V → V → ℂ) {μ μ' : Measure V}
    (h : SelfDual μ B) (h' : SelfDual μ' B) : μ' = μ := by
  obtain ⟨hμ, hF⟩ := h
  obtain ⟨hμ', hF'⟩ := h'
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ
  obtain ⟨f, hf, y, hy⟩ := exists_test_ne_zero hS
  have h1 := hF' f hf y
  rw [e, fourB_twice_nnreal_smul, hF f hf y] at h1
  have hc : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℂ) ^ 2 = 1 :=
    mul_right_cancel₀ hy (h1.trans (one_mul _).symm)
  have hc2 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) ^ 2 = 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (μ'.addHaarScalarFactor μ : ℝ≥0) := NNReal.coe_nonneg _
  have hc1 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) = 1 := by nlinarith
  have hc3 : μ'.addHaarScalarFactor μ = 1 := by exact_mod_cast hc1
  rw [e, hc3, one_smul]

/- English proof (translation)
Set `φ` to `Homeomorph.smul (α := L) u`. Establish `hmap : μ.map (fun y => u • y) = (distribHaarChar L u⁻¹) • μ`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (continuous_const_smul u).measurable hs, Set.preimage_smul, Measure.smul_apply, ← distribHaarChar_mul μ u⁻¹ s]`. Both sides reduce to the same expression.

Establish `: ∫ y, G y ∂(μ.map fun y => u • y) = ∫ y, G (u • y) ∂μ` using `φ.measurableEmbedding.integral_map (μ := μ) G`. Rewrite using `[← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, map_inv]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem integral_units_smul {L : Type} [CommRing L] [TopologicalSpace L] [IsTopologicalRing L]
    [LocallyCompactSpace L] [T2Space L] [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μ : Measure L) [μ.IsAddHaarMeasure] (u : Lˣ) (G : L → ℂ) :
    ∫ y, G (u • y) ∂μ = ((distribHaarChar L u : ℝ≥0) : ℂ)⁻¹ * ∫ y, G y ∂μ := by
  let φ := Homeomorph.smul (α := L) u
  have hmap : μ.map (fun y => u • y) = (distribHaarChar L u⁻¹) • μ := by
    ext s hs
    rw [Measure.map_apply (continuous_const_smul u).measurable hs, Set.preimage_smul, Measure.smul_apply,
      ← distribHaarChar_mul μ u⁻¹ s]
    rfl
  have : ∫ y, G y ∂(μ.map fun y => u • y) = ∫ y, G (u • y) ∂μ :=
    φ.measurableEmbedding.integral_map (μ := μ) G
  rw [← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, map_inv]
  push_cast
  rfl

end GlobalTheory.JR.MeasScale

namespace GlobalTheory.JR.MeasScale

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def unitL (A : Et F E) (x : A.Kˣ) : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitL_smul (A : Et F E) (x : A.Kˣ) (y : A.L) : unitL A x • y = algebraMap A.K A.L x * y := rfl

/- English proof (translation)
Simplify using `only [Et.kerL, unitL_smul, Units.val_one, one_mul]`. Use `congr 1`. Establish `: star y' * (algebraMap A.K A.L x * y) = (x : A.K) • (star y' * y)`. Rewrite using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, map_smul, smul_eq_mul]`.
-/
theorem kerL_eq (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ x y' y = A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) := by
  simp only [Et.kerL, unitL_smul, Units.val_one, one_mul]
  congr 1
  have : star y' * (algebraMap A.K A.L x * y) = (x : A.K) • (star y' * y) := by
    rw [Algebra.smul_def]; ring
  rw [this, map_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [Et.kerL, unitL_smul]`. Rewrite using `[star_mul', A.star_K]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kerL_swap (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) = A.kerL ψ ((1 : A.Kˣ) : A.K) (unitL A x • y') y := by
  simp only [Et.kerL, unitL_smul]
  rw [star_mul', A.star_K]
  congr 3
  ring

/- English proof (translation)
Use `U.charZero` as an intermediate fact. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Use `EtMeas.finite_L A` as an intermediate fact. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.L`.

Establish `: IsTopologicalRing A.L` using `IsModuleTopology.isTopologicalRing F A.L`. Establish `hN : distribHaarChar A.L (unitL A x) = distribHaarChar A.K x ^ 2`. Take `⟨⟨b⟩, -, -, -, -⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.K`. Establish `: ContinuousStar A.L` using `⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩`.

Rewrite using `[← map_pow]`. Use `GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)) (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_` and prove the remaining obligations. Simplify using `[unitL, A.star_K, pow_two]`. Take `⟨hμ, hF⟩` from `h`. Establish `hc : distribHaarChar A.K x ≠ 0` using `distribHaarChar_pos.ne'`.

Use `⟨Measure.IsAddHaarMeasure.nnreal_smul _ hc, fun f hf y => ?_⟩` and prove the remaining obligations. Use `set c := distribHaarChar A.K x with hcdef`. Use `set B1 := A.kerL ψ ((1 : A.Kˣ) : A.K)`. Establish `h1 : ∀ g z, fourB (c • μ) (A.kerL ψ x) g z = (c : ℂ) * fourB μ B1 g (unitL A x • z)`. Introduce `g z`.

Rewrite using `[fourB_nnreal_smul]`. Simplify using `only [fourB, kerL_eq A ψ x, B1]`. Establish `h2 : fourB (c • μ) (A.kerL ψ x) f = fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)`. Use function extensionality and compare the values at `(h1 f)`. Rewrite using `[h1, h2]`.

Establish `h3 : fourB μ B1 (fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)) (unitL A x • y) = (c : ℂ) * ((distribHaarChar A.L (unitL A x) : ℝ≥0) : ℂ)⁻¹ * fourB μ B1 (fourB μ B1 f) y`. Rewrite using `[fourB_const_mul, mul_assoc]`. Use `congr 1`. Establish `e` using `integral_units_smul μ (unitL A x) (fun z => fourB μ B1 f z * B1 z y)`. Use `Eq.trans ?_ e` and prove the remaining obligations.

Use `show ∫ y', fourB μ B1 f (unitL A x • y') * B1 y' (unitL A x • y) ∂μ = _`. Use `integral_congr_ae (Eventually.of_forall fun y' => ?_)` and prove the remaining obligations. Conclude with `congrArg _ (kerL_swap A ψ x y' y)`. Rewrite using `[h3, hF f hf y, hN]`. Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem selfDual_scale [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (h : SelfDual μ (A.kerL ψ ((1 : A.Kˣ) : A.K))) :
    SelfDual (distribHaarChar A.K x • μ) (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (unitL A x) = distribHaarChar A.K x ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [unitL, A.star_K, pow_two]
  obtain ⟨hμ, hF⟩ := h
  have hc : distribHaarChar A.K x ≠ 0 := distribHaarChar_pos.ne'
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul _ hc, fun f hf y => ?_⟩
  set c := distribHaarChar A.K x with hcdef
  set B1 := A.kerL ψ ((1 : A.Kˣ) : A.K)
  have h1 : ∀ g z, fourB (c • μ) (A.kerL ψ x) g z = (c : ℂ) * fourB μ B1 g (unitL A x • z) := by
    intro g z
    rw [fourB_nnreal_smul]
    simp only [fourB, kerL_eq A ψ x, B1]
  have h2 : fourB (c • μ) (A.kerL ψ x) f = fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z) :=
    funext (h1 f)
  rw [h1, h2]
  have h3 : fourB μ B1 (fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)) (unitL A x • y) =
      (c : ℂ) * ((distribHaarChar A.L (unitL A x) : ℝ≥0) : ℂ)⁻¹ * fourB μ B1 (fourB μ B1 f) y := by
    rw [fourB_const_mul, mul_assoc]
    congr 1
    have e := integral_units_smul μ (unitL A x) (fun z => fourB μ B1 f z * B1 z y)
    refine Eq.trans ?_ e
    show ∫ y', fourB μ B1 f (unitL A x • y') * B1 y' (unitL A x • y) ∂μ = _
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    exact congrArg _ (kerL_swap A ψ x y' y)
  rw [h3, hF f hf y, hN]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp

/- English proof (translation)
Use `(inferInstance : Unram F E).charZero` as an intermediate fact. Establish `hu` using `‹Unram F E›.ultraF`. Use `‹Unram F E›.lcF` as an intermediate fact. Use `EtMeas.finite_L A` as an intermediate fact. Take `⟨_, _, _, _, hS⟩` from `EtMeas.top_facts F A.L`.

Rewrite using `[EtMeas.absK_unit, ENNReal.ofReal_coe_nnreal]`. Conclude with `selfDual_unique hS _ (selfDual_scale A ψ x (m.μL 1) (m.sdL 1)) (m.sdL x)`.
-/
theorem meas_scale [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (m : A.Meas ψ) (x : A.Kˣ) :
    m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  have := (inferInstance : Unram F E).charZero
  have hu := ‹Unram F E›.ultraF; have := ‹Unram F E›.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  rw [EtMeas.absK_unit, ENNReal.ofReal_coe_nnreal]
  exact selfDual_unique hS _ (selfDual_scale A ψ x (m.μL 1) (m.sdL 1)) (m.sdL x)

end GlobalTheory.JR.MeasScale

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ hψ`. Conclude with `⟨(EtMeas.nonempty_meas_and_reps F E A ψ hψ).1, GlobalTheory.JR.MeasScale.meas_scale A ψ⟩`.
-/
theorem GlobalTheory.JR.exists_meas_and_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  intro F E _ _ _ _ _ A ψ hψ
  exact ⟨(EtMeas.nonempty_meas_and_reps F E A ψ hψ).1, GlobalTheory.JR.MeasScale.meas_scale A ψ⟩
