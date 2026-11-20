import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace GlobalTheory.LeviFactor
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace

namespace GlobalTheory.CommProdAvg

def mulHom {G : Type} [Group G] (A B C : Subgroup G) (hAC : A ≤ C) (hBC : B ≤ C)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A × B →* C where
  toFun p := ⟨(p.1 : G) * p.2, C.mul_mem (hAC p.1.2) (hBC p.2.2)⟩
  map_one' := by ext; simp
  map_mul' p q := by
    ext
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h := (hcomm _ q.1.2 _ p.2.2).eq
    calc (p.1 : G) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
      _ = p.1 * (p.2 * q.1) * q.2 := by rw [h]
      _ = p.1 * p.2 * (q.1 * q.2) := by group

/- English proof (translation)
Use `haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA`. Use `haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB`. Use `haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC`. Use `set μA : Measure A := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts A) with hμAdef`. Use `haveI : IsProbabilityMeasure μA := ⟨by simpa [μA] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts A))⟩`.

Use `set m := mulHom A B C hAC hBC hcomm with hm`. Establish `hmc : Continuous m`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `(continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)`. Establish `hms : Function.Surjective m`.

Introduce and unpack `⟨z, hz⟩`. Take `⟨x, hx, y, hy, rfl⟩` from `hsurj z hz`. Conclude with `⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩`. Use `haveI : (Measure.map m (μA.prod μB)).IsHaarMeasure := Measure.isHaarMeasure_map_of_isFiniteMeasure _ m hmc hms`. Use `haveI : IsProbabilityMeasure (Measure.map m (μA.prod μB)) := Measure.isProbabilityMeasure_map hmc.measurable.aemeasurable`.

Establish `heq : μC = Measure.map m (μA.prod μB)` using `Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _`. Establish `hf : Continuous (fun z : C => φ z)` using `continuousOn_iff_continuous_restrict.mp hφ`. Rewrite using `[heq, integral_map hmc.measurable.aemeasurable hf.aestronglyMeasurable]`. Establish `h1 : (fun p : A × B => φ ((m p : C) : G)) = fun p => (fun y : B => φ y) p.2`. Use function extensionality and compare the values at `p`.

Conclude with `hinv _ p.1.2 _ p.2.2`. Rewrite using `[h1]`. Establish `hg : Continuous (fun y : B => φ y)` using `hf.comp (continuous_inclusion hBC)`. Rewrite using `[← integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable, Measure.map_snd_prod]`. Simplify using the standard rewrite rules.
-/
theorem main (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (A B C : Subgroup G) (hA : IsCompact (A : Set G)) (hB : IsCompact (B : Set G))
    (hC : IsCompact (C : Set G)) (hAC : A ≤ C) (hBC : B ≤ C)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hsurj : ∀ z ∈ C, ∃ x ∈ A, ∃ y ∈ B, z = x * y)
    (μB : Measure B) (μC : Measure C) (hμB : μB.IsHaarMeasure) (hμBp : IsProbabilityMeasure μB)
    (hμC : μC.IsHaarMeasure) (hμCp : IsProbabilityMeasure μC)
    (φ : G → ℝ) (hφ : ContinuousOn φ C) (hinv : ∀ x ∈ A, ∀ y ∈ B, φ (x * y) = φ y) :
    ∫ z : C, φ z ∂μC = ∫ y : B, φ y ∂μB := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  set μA : Measure A := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts A) with hμAdef
  haveI : IsProbabilityMeasure μA :=
    ⟨by simpa [μA] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts A))⟩
  set m := mulHom A B C hAC hBC hcomm with hm
  have hmc : Continuous m := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hms : Function.Surjective m := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hsurj z hz
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  haveI : (Measure.map m (μA.prod μB)).IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure _ m hmc hms
  haveI : IsProbabilityMeasure (Measure.map m (μA.prod μB)) :=
    Measure.isProbabilityMeasure_map hmc.measurable.aemeasurable
  have heq : μC = Measure.map m (μA.prod μB) :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hf : Continuous (fun z : C => φ z) := continuousOn_iff_continuous_restrict.mp hφ
  rw [heq, integral_map hmc.measurable.aemeasurable hf.aestronglyMeasurable]
  have h1 : (fun p : A × B => φ ((m p : C) : G)) = fun p => (fun y : B => φ y) p.2 := by
    funext p
    exact hinv _ p.1.2 _ p.2.2
  rw [h1]
  have hg : Continuous (fun y : B => φ y) := hf.comp (continuous_inclusion hBC)
  rw [← integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable, Measure.map_snd_prod]
  simp

end GlobalTheory.CommProdAvg
