import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.QuadraticFormRationalPoints
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.BddE
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ZDom
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import GroundTheory.AutomorphicForms.CompactFormulaCountable

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom : Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E))` using `continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap`. Conclude with `Continuous.units_map _ hM`.
-/
private theorem continuous_em : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

/- English proof (translation)
Use `haveI : SecondCountableTopology (A E) := GroundTheory.Automorphic.secondCountableTopology_adeleRing E`. Use `haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (A E)) := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A E))`. Use `haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (A E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
private theorem secondCountable_gl : SecondCountableTopology (GL (Fin 2) (A E)) := by
  haveI : SecondCountableTopology (A E) := GroundTheory.Automorphic.secondCountableTopology_adeleRing E
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (A E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (A E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/- English proof (translation)
Use `haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩`. Use `haveI := secondCountable_gl (E := E)`. Establish `hin : ∀ k, Continuous fun g : G1 ℚ => f (em E (gl g) * k)` using `fun k => hf.comp ((continuous_em.comp Matrix.SpecialLinearGroup.continuous_toGL).mul continuous_const)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `k₀`.

Take `⟨C, hC, hk⟩` from `exists_compact_mem_nhds k₀`. Take `⟨B, hB⟩` from `hb C hC`. Use `continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_` and prove the remaining obligations. Conclude with `Eventually.of_forall fun k => (hin k).aestronglyMeasurable`. Use `filter_upwards [hk] with k hkC`.

Conclude with `ae_of_all _ fun g => hB g k hkC`. Conclude with `ae_of_all _ fun g => (hf.comp (continuous_const.mul continuous_id)).continuousAt`.
-/
private theorem continuous_inner (M : Meas ℚ) {f : GL (Fin 2) (A E) → ℂ} (hf : Continuous f)
    (hb : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ g : G1 ℚ, ∀ k ∈ C, ‖f (em E (gl g) * k)‖ ≤ B) :
    Continuous fun k : GL (Fin 2) (A E) => ∫ g in M.D, f (em E (gl g) * k) ∂M.μ := by
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI := secondCountable_gl (E := E)
  have hin : ∀ k, Continuous fun g : G1 ℚ => f (em E (gl g) * k) := fun k =>
    hf.comp ((continuous_em.comp Matrix.SpecialLinearGroup.continuous_toGL).mul continuous_const)
  rw [continuous_iff_continuousAt]
  intro k₀
  obtain ⟨C, hC, hk⟩ := exists_compact_mem_nhds k₀
  obtain ⟨B, hB⟩ := hb C hC
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact Eventually.of_forall fun k => (hin k).aestronglyMeasurable
  · filter_upwards [hk] with k hkC
    exact ae_of_all _ fun g => hB g k hkC
  · exact ae_of_all _ fun g => (hf.comp (continuous_const.mul continuous_id)).continuousAt

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

/- English proof (translation)
Introduce `E _ _ _ D W M N P φ hφ`. Establish `hc : Continuous φ.1` using `ContAut.continuous_of_isOpen_stab E 2 φ (P.cusp φ hφ).1.level`. Take `⟨j, r, hj, -⟩` from `reps E D`. Establish `hbd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ g : G1 ℚ, ∀ k ∈ C, ‖φ.1 (em E (gl g) * k)‖ ≤ B`. Introduce `C hC`.

Take `⟨B, hB⟩` from `bddE E P φ hφ C hC`. Conclude with `⟨B, fun g k hk => by rw [← hj g]; exact hB (j g) k hk⟩`. Establish `hΦ` using `continuous_inner M hc hbd`. Use `set Φ : GL (Fin 2) (A E) → ℂ := fun k => ∫ g in M.D, φ.1 (em E (gl g) * k) ∂M.μ with hΦdef`. Take `⟨hfin, hmeas, CZ, hCZ, hmem⟩` from `zDom E`.

Use `haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by simpa using hfin⟩`. Use `haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩`. Establish `hs : Continuous (sZ D)` using `(szLaws E D).2.1`. Establish `hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E)` using `hs.comp continuous_subtype_val`. Establish `key : ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) = ∫ z in normOneFundamentalDomain E, Φ (sZ D (z : IdeleGroup E) * gl h) ∂normOneMeasure E`.

Introduce `h`. Simplify using `only [UPer, UI, SLP, hΦdef, mul_assoc]`. Simplify using `only [key]`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `h₀`.

Take `⟨K, hK, hh⟩` from `exists_compact_mem_nhds h₀`. Establish `hglc : Continuous (gl : G1 E → GL (Fin 2) (A E))` using `Matrix.SpecialLinearGroup.continuous_toGL`. Establish `hCc : IsCompact ((fun p : (A E)ˣ × G1 E => sZ D p.1 * gl p.2) '' (CZ ×ˢ K))` using `(hCZ.prod hK).image ((hs.comp continuous_fst).mul (hglc.comp continuous_snd))`. Take `⟨B, hB⟩` from `hbd _ hCc`. Use `continuousAt_of_dominated (bound := fun _ => B * (M.μ.restrict M.D).real Set.univ) ?_ ?_ (integrable_const _) ?_` and prove the remaining obligations.

Conclude with `Eventually.of_forall fun h => (hΦ.comp (hsz.mul continuous_const)).aestronglyMeasurable`. Use `filter_upwards [hh] with h hhK`. Use `ae_restrict_of_forall_mem hmeas fun z hz => ?_` and prove the remaining obligations. Conclude with `norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB g _ ⟨(((z : IdeleGroup E) : (A E)ˣ), h), ⟨hmem z hz, hhK⟩, rfl⟩)`. Conclude with `ae_of_all _ fun z => (hΦ.comp (continuous_const.mul hglc)).continuousAt`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.perCont :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.PerCont := by
  intro E _ _ _ D W M N P φ hφ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E 2 φ (P.cusp φ hφ).1.level
  obtain ⟨j, r, hj, -⟩ := reps E D
  have hbd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C →
      ∃ B : ℝ, ∀ g : G1 ℚ, ∀ k ∈ C, ‖φ.1 (em E (gl g) * k)‖ ≤ B := by
    intro C hC
    obtain ⟨B, hB⟩ := bddE E P φ hφ C hC
    exact ⟨B, fun g k hk => by rw [← hj g]; exact hB (j g) k hk⟩
  have hΦ := continuous_inner M hc hbd
  set Φ : GL (Fin 2) (A E) → ℂ := fun k => ∫ g in M.D, φ.1 (em E (gl g) * k) ∂M.μ with hΦdef
  obtain ⟨hfin, hmeas, CZ, hCZ, hmem⟩ := zDom E
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using hfin⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  have hs : Continuous (sZ D) := (szLaws E D).2.1
  have hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E) :=
    hs.comp continuous_subtype_val
  have key : ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) =
      ∫ z in normOneFundamentalDomain E, Φ (sZ D (z : IdeleGroup E) * gl h) ∂normOneMeasure E := by
    intro h
    simp only [UPer, UI, SLP, hΦdef, mul_assoc]
  simp only [key]
  rw [continuous_iff_continuousAt]
  intro h₀
  obtain ⟨K, hK, hh⟩ := exists_compact_mem_nhds h₀
  have hglc : Continuous (gl : G1 E → GL (Fin 2) (A E)) := Matrix.SpecialLinearGroup.continuous_toGL
  have hCc : IsCompact ((fun p : (A E)ˣ × G1 E => sZ D p.1 * gl p.2) '' (CZ ×ˢ K)) :=
    (hCZ.prod hK).image ((hs.comp continuous_fst).mul (hglc.comp continuous_snd))
  obtain ⟨B, hB⟩ := hbd _ hCc
  refine continuousAt_of_dominated (bound := fun _ => B * (M.μ.restrict M.D).real Set.univ) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun h =>
      (hΦ.comp (hsz.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [hh] with h hhK
    refine ae_restrict_of_forall_mem hmeas fun z hz => ?_
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun g =>
      hB g _ ⟨(((z : IdeleGroup E) : (A E)ˣ), h), ⟨hmem z hz, hhK⟩, rfl⟩)
  · exact ae_of_all _ fun z =>
      (hΦ.comp (continuous_const.mul hglc)).continuousAt
