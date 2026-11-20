import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilGaussNon

section Char

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hDm : MeasurableSet (valBall F m : Set F)` using `(isOpen_valBall m).measurableSet`. Rewrite using `[← integral_indicator hDm]`. Use `set g : F → ℂ := (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) with hg`. Establish `e1 : ∫ x, g (x + b) ∂μ = ∫ x, g x ∂μ` using `integral_add_right_eq_self g b`. Establish `e2 : ∀ x, g (x + b) = (χ b : ℂ) * g x`.

Introduce `x`. Distinguish the cases in `hx : x ∈ (valBall F m : Set F)`. Establish `hxb : x + b ∈ (valBall F m : Set F)` using `(valBall F m).add_mem hx hb`. Rewrite using `[hg, Set.indicator_of_mem hxb, Set.indicator_of_mem hx, AddChar.map_add_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hxb : x + b ∉ (valBall F m : Set F)` using `fun h => hx (by`. Use `sub_mem (show x + b ∈ valBall F m from h) hb` as an intermediate fact. Simplify using `using this)`. Rewrite using `[hg, Set.indicator_of_notMem hxb, Set.indicator_of_notMem hx, mul_zero]`.

Rewrite `e1` using `[e2]`. Rewrite `e1` using `[integral_const_mul]`. Establish `h1 : ((χ b : ℂ) - 1) ≠ 0`. Rewrite using `[sub_ne_zero]`. Introduce `h`.

Conclude with `hχb (Circle.ext (by simpa using h))`. Establish `h2 : ((χ b : ℂ) - 1) * ∫ x, g x ∂μ = 0` using `by linear_combination e1`. Conclude with `(mul_eq_zero.1 h2).resolve_left h1`.
-/
theorem integral_valBall_char_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure] {χ : AddChar F Circle}
    {m : ℤ} {b : F} (hb : b ∈ valBall F m) (hχb : χ b ≠ 1) :
    ∫ x in (valBall F m : Set F), (χ x : ℂ) ∂μ = 0 := by
  have hDm : MeasurableSet (valBall F m : Set F) := (isOpen_valBall m).measurableSet
  rw [← integral_indicator hDm]
  set g : F → ℂ := (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) with hg
  have e1 : ∫ x, g (x + b) ∂μ = ∫ x, g x ∂μ := integral_add_right_eq_self g b
  have e2 : ∀ x, g (x + b) = (χ b : ℂ) * g x := by
    intro x
    by_cases hx : x ∈ (valBall F m : Set F)
    · have hxb : x + b ∈ (valBall F m : Set F) := (valBall F m).add_mem hx hb
      rw [hg, Set.indicator_of_mem hxb, Set.indicator_of_mem hx, AddChar.map_add_eq_mul]
      push_cast
      ring
    · have hxb : x + b ∉ (valBall F m : Set F) := fun h => hx (by
        have := sub_mem (show x + b ∈ valBall F m from h) hb
        simpa using this)
      rw [hg, Set.indicator_of_notMem hxb, Set.indicator_of_notMem hx, mul_zero]
  simp_rw [e2] at e1
  rw [integral_const_mul] at e1
  have h1 : ((χ b : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hχb (Circle.ext (by simpa using h))
  have h2 : ((χ b : ℂ) - 1) * ∫ x, g x ∂μ = 0 := by linear_combination e1
  exact (mul_eq_zero.1 h2).resolve_left h1

end Char

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

variable (F E) in

def radius (c : F) (m : ℤ) : ℤ := -((ord c - m) / (residueDegree F E : ℤ))

/- English proof (translation)
Use extensionality with `u`. Distinguish the cases in `hu : u = 0`. Substitute `hu` using the available equality. Simplify using `[zero_mem]`. Establish `hN : Algebra.norm F u ≠ 0` using `(normUnits F E (Units.mk0 u hu)).ne_zero`.

Simplify using `only [Set.mem_preimage, SetLike.mem_coe]`. Rewrite using `[mem_valBall_iff_le_ord (mul_ne_zero hc hN), mem_valBall_iff_le_ord hu, ord_mul hc hN, ord_norm, radius]`. Establish `hf : (0 : ℤ) < residueDegree F E` using `by exact_mod_cast residueDegree_pos F E`. Rewrite using `[neg_le, Int.le_ediv_iff_mul_le hf]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`.
-/
theorem preimage_valBall {c : F} (hc : c ≠ 0) (m : ℤ) :
    (fun u : E => c * Algebra.norm F u) ⁻¹' (valBall F m : Set F) =
      (valBall E (radius F E c m) : Set E) := by
  ext u
  by_cases hu : u = 0
  · subst hu
    simp [zero_mem]
  · have hN : Algebra.norm F u ≠ 0 := (normUnits F E (Units.mk0 u hu)).ne_zero
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [mem_valBall_iff_le_ord (mul_ne_zero hc hN), mem_valBall_iff_le_ord hu, ord_mul hc hN,
      ord_norm, radius]
    have hf : (0 : ℤ) < residueDegree F E := by exact_mod_cast residueDegree_pos F E
    rw [neg_le, Int.le_ediv_iff_mul_le hf]
    constructor <;> intro h <;> linarith

/- English proof (translation)
Establish `hf : (0 : ℤ) < residueDegree F E` using `by exact_mod_cast residueDegree_pos F E`. Rewrite using `[radius, neg_le, Int.le_ediv_iff_mul_le hf]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem radius_le {c : F} {m N₀ : ℤ} (h : m ≤ ord c + residueDegree F E * N₀) :
    radius F E c m ≤ N₀ := by
  have hf : (0 : ℤ) < residueDegree F E := by exact_mod_cast residueDegree_pos F E
  rw [radius, neg_le, Int.le_ediv_iff_mul_le hf]
  linarith

/- English proof (translation)
Establish `hD : MeasurableSet (valBall F m : Set F)` using `(isOpen_valBall m).measurableSet`. Establish `hc : Continuous fun x => (χ x : ℂ)` using `continuous_induced_dom.comp hχ`. Establish `hg : Measurable ((valBall F m : Set F).indicator (fun x => (χ x : ℂ)))` using `hc.measurable.indicator hD`. Prove the components needed by the constructor for the conclusion. Rewrite using `[integrable_indicator_iff hD]`.

Use `Measure.integrableOn_of_bounded (M := 1) ?_ hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => le_of_eq (Circle.norm_coe _))` and prove the remaining obligations. Rewrite using `[Measure.map_apply hP.measurable hD, hpre]`. Conclude with `(isCompact_valBall n).measure_lt_top.ne`. Rewrite using `[integral_map hP.aemeasurable hg.aestronglyMeasurable, ← integral_indicator (isOpen_valBall n).measurableSet]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Distinguish the cases in `hu : u ∈ (valBall E n : Set E)`. Establish `hu' : P u ∈ (valBall F m : Set F)`. Establish `: u ∈ P ⁻¹' (valBall F m : Set F)` using `hpre ▸ hu`. Conclude with `this`. Simplify using `only [Set.indicator_of_mem hu, Set.indicator_of_mem hu']`.

Establish `hu' : P u ∉ (valBall F m : Set F)` using `fun h => hu (hpre ▸ (show u ∈ P ⁻¹' _ from h))`. Simplify using `only [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']`.
-/
theorem map_facts {χ : AddChar F Circle} (hχ : Continuous χ) {P : E → F} (hP : Continuous P)
    {m n : ℤ} (hpre : P ⁻¹' (valBall F m : Set F) = (valBall E n : Set E)) :
    Integrable ((valBall F m : Set F).indicator (fun x => (χ x : ℂ)))
        ((haarIntegers E).map P) ∧
      ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x ∂((haarIntegers E).map P) =
        ∫ u in (valBall E n : Set E), (χ (P u) : ℂ) ∂haarIntegers E := by
  have hD : MeasurableSet (valBall F m : Set F) := (isOpen_valBall m).measurableSet
  have hc : Continuous fun x => (χ x : ℂ) := continuous_induced_dom.comp hχ
  have hg : Measurable ((valBall F m : Set F).indicator (fun x => (χ x : ℂ))) :=
    hc.measurable.indicator hD
  constructor
  · rw [integrable_indicator_iff hD]
    refine Measure.integrableOn_of_bounded (M := 1) ?_ hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (Circle.norm_coe _))
    rw [Measure.map_apply hP.measurable hD, hpre]
    exact (isCompact_valBall n).measure_lt_top.ne
  · rw [integral_map hP.aemeasurable hg.aestronglyMeasurable,
      ← integral_indicator (isOpen_valBall n).measurableSet]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ (valBall E n : Set E)
    · have hu' : P u ∈ (valBall F m : Set F) := by
        have : u ∈ P ⁻¹' (valBall F m : Set F) := hpre ▸ hu
        exact this
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hu']
    · have hu' : P u ∉ (valBall F m : Set F) := fun h => hu (hpre ▸ (show u ∈ P ⁻¹' _ from h))
      simp only [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']

/- English proof (translation)
Establish `hN : Continuous (Algebra.norm F : E → F)` using `GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of hcont`. Establish `hNa : Continuous (fun u : E => a * Algebra.norm F u)` using `continuous_const.mul hN`. Establish `p1 : (Algebra.norm F : E → F) ⁻¹' (valBall F m : Set F) = (valBall E (radius F E 1 m) : Set E)`. Rewrite using `[← preimage_valBall one_ne_zero m]`. Simplify using `only [one_mul]`.

Take `⟨i1, e1⟩` from `map_facts hχ hN p1`. Take `⟨i2, e2⟩` from `map_facts hχ hNa (preimage_valBall ha m)`. Establish `hsum : (haarIntegers E).map (Algebra.norm F : E → F) + (c : ENNReal) • (haarIntegers E).map (fun u : E => a * Algebra.norm F u) = κ • haarIntegers F`. Use extensionality with `S hS`. Simplify using `only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]`.

Rewrite using `[Measure.map_apply hN.measurable hS, Measure.map_apply hNa.measurable hS]`. Conclude with `hm S hS`. Establish `key : ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x ∂((haarIntegers E).map (Algebra.norm F : E → F) + (c : ENNReal) • (haarIntegers E).map (fun u : E => a * Algebra.norm F u)) = ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x ∂(κ • haarIntegers F)`. Rewrite using `[hsum]`. Rewrite `key` using `[integral_add_measure i1 (i2.smul_measure ENNReal.coe_ne_top), integral_smul_measure, integral_smul_measure, e1, e2, integral_indicator (isOpen_valBall m).measurableSet, integral_valBall_char_eq_zero _ hb hχb, smul_zero]`.

Take `⟨t, ht⟩ : ∃ t : ENNReal, ν = t • haarIntegers E` from `⟨_, eq_smul_haarIntegers ν⟩`. Rewrite using `[ht, Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure, integral_smul_measure]`. Rewrite `key` using `[ENNReal.coe_toReal, Complex.real_smul]`. Rewrite using `[Complex.real_smul, Complex.real_smul]`. Take the linear combination `(t.toReal : ℂ) * key`.
-/
theorem ball_sum_eq_zero (hcont : Continuous (algebraMap F E)) {χ : AddChar F Circle}
    (hχ : Continuous χ) {a : F} (ha : a ≠ 0) (c : NNReal) (κ : ENNReal)
    (hm : ∀ S : Set F, MeasurableSet S →
      haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) +
        (c : ENNReal) * haarIntegers E ((fun u : E => a * Algebra.norm F u) ⁻¹' S) =
          κ * haarIntegers F S)
    {m : ℤ} {b : F} (hb : b ∈ valBall F m) (hχb : χ b ≠ 1) (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ u in (valBall E (radius F E 1 m) : Set E), (χ (Algebra.norm F u) : ℂ) ∂ν) +
      ((c : ℝ) : ℂ) * ∫ u in (valBall E (radius F E a m) : Set E),
        (χ (a * Algebra.norm F u) : ℂ) ∂ν = 0 := by
  have hN : Continuous (Algebra.norm F : E → F) := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of hcont
  have hNa : Continuous (fun u : E => a * Algebra.norm F u) := continuous_const.mul hN
  have p1 : (Algebra.norm F : E → F) ⁻¹' (valBall F m : Set F) =
      (valBall E (radius F E 1 m) : Set E) := by
    rw [← preimage_valBall one_ne_zero m]
    simp only [one_mul]
  obtain ⟨i1, e1⟩ := map_facts hχ hN p1
  obtain ⟨i2, e2⟩ := map_facts hχ hNa (preimage_valBall ha m)
  have hsum : (haarIntegers E).map (Algebra.norm F : E → F) +
      (c : ENNReal) • (haarIntegers E).map (fun u : E => a * Algebra.norm F u) =
        κ • haarIntegers F := by
    ext S hS
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hN.measurable hS, Measure.map_apply hNa.measurable hS]
    exact hm S hS
  have key : ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x
      ∂((haarIntegers E).map (Algebra.norm F : E → F) +
        (c : ENNReal) • (haarIntegers E).map (fun u : E => a * Algebra.norm F u)) =
      ∫ x, (valBall F m : Set F).indicator (fun x => (χ x : ℂ)) x ∂(κ • haarIntegers F) := by
    rw [hsum]
  rw [integral_add_measure i1 (i2.smul_measure ENNReal.coe_ne_top), integral_smul_measure,
    integral_smul_measure, e1, e2, integral_indicator (isOpen_valBall m).measurableSet,
    integral_valBall_char_eq_zero _ hb hχb, smul_zero] at key
  obtain ⟨t, ht⟩ : ∃ t : ENNReal, ν = t • haarIntegers E := ⟨_, eq_smul_haarIntegers ν⟩
  rw [ht, Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure,
    integral_smul_measure]
  rw [ENNReal.coe_toReal, Complex.real_smul] at key
  rw [Complex.real_smul, Complex.real_smul]
  linear_combination (t.toReal : ℂ) * key

end Main

/- English proof (translation)
Introduce `H F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a hna N₀`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont`. Use `haveI : Algebra.IsSeparable F E := inferInstance`.

Establish `hnr : a ∉ (normUnits F E).range` using `fun ⟨t, ht⟩ => hna ⟨t, by rw [← coe_normUnits, ht]⟩`. Take `⟨κ, -, hκ⟩` from `H F E hcont a hnr`. Take `⟨b, hχb⟩` from `AddChar.ne_one_iff.1 hχ1`. Take `⟨M, hM⟩` from `exists_mem_valBall_neg_nat b`. Take `⟨m, h0, h1, h2⟩ : ∃ m : ℤ, m ≤ -(M : ℤ) ∧ m ≤ ord (1 : F) + residueDegree F E * N₀ ∧ m ≤ ord (a : F) + residueDegree F E * N₀` from `⟨min (-(M : ℤ)) (min (ord (1 : F) + residueDegree F E * N₀) (ord (a : F) + residueDegree F E * N₀)), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩`.

Establish `hbm : b ∈ valBall F m` using `valBall_antitone h0 hM`. Conclude with `⟨radius F E 1 m, radius_le h1, radius F E (a : F) m, radius_le h2, ball_sum_eq_zero hcont hχ a.ne_zero _ κ hκ hbm hχb (muE E χ)⟩`.
-/
theorem ball_integrals_cancel : (∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
  haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S) → ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), (¬ ∃ t : Eˣ, Algebra.norm F (t : E) = a) → ∀ N₀ : ℤ,
  ∃ n₁ ≤ N₀, ∃ n₂ ≤ N₀,
    (∫ u in (valBall E n₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ) +
      ((modulus (a : F) : ℝ) : ℂ) * ∫ u in (valBall E n₂ : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = 0 := by
  intro H F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a hna N₀
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hnr : a ∉ (normUnits F E).range := fun ⟨t, ht⟩ => hna ⟨t, by rw [← coe_normUnits, ht]⟩
  obtain ⟨κ, -, hκ⟩ := H F E hcont a hnr
  obtain ⟨b, hχb⟩ := AddChar.ne_one_iff.1 hχ1
  obtain ⟨M, hM⟩ := exists_mem_valBall_neg_nat b
  obtain ⟨m, h0, h1, h2⟩ : ∃ m : ℤ, m ≤ -(M : ℤ) ∧ m ≤ ord (1 : F) + residueDegree F E * N₀ ∧
      m ≤ ord (a : F) + residueDegree F E * N₀ :=
    ⟨min (-(M : ℤ)) (min (ord (1 : F) + residueDegree F E * N₀)
      (ord (a : F) + residueDegree F E * N₀)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hbm : b ∈ valBall F m := valBall_antitone h0 hM
  exact ⟨radius F E 1 m, radius_le h1, radius F E (a : F) m, radius_le h2,
    ball_sum_eq_zero hcont hχ a.ne_zero _ κ hκ hbm hχb (muE E χ)⟩

end GlobalTheory.CompanionTheory.WeilGaussNon
