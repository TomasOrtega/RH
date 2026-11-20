import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, k = g * h⁻¹` from `⟨_, rfl⟩`. Establish `hdet : h.1 0 0 * h.1 1 1 - h.1 0 1 * h.1 1 0 = 1`. Establish `hd` using `h.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `hg0 : g.1 1 0 = t * h.1 1 0` using `by simpa using congrFun hrow 0`.

Establish `hg1 : g.1 1 1 = t * h.1 1 1` using `by simpa using congrFun hrow 1`. Establish `e0 : k.1 1 0 = 0`. Rewrite using `[hk]`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[hg0, hg1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1 : k.1 1 1 = t`. Rewrite using `[hk]`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[hg0, hg1]`.

Take the linear combination `(t : E) * hdet`. Establish `e2 : k.1 0 0 = ((t⁻¹ : Eˣ) : E)`. Establish `hd` using `k.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two, e0, e1]`. Establish `ht : (t : E) ≠ 0` using `t.ne_zero`.

Simplify using `only [Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hd`. Establish `d2 : (((IdeleGroup.diagonal E t⁻¹)⁻¹ : (A E)ˣ) : A E) = UpperTheory.ConvolutionTheory.R2.rt (t : E)`. Rewrite using `[← map_inv, inv_inv]`.

Both sides reduce to the same expression. Establish `d3 : (((IdeleGroup.diagonal E t)⁻¹ : (A E)ˣ) : A E) = algebraMap E (A E) (t : E)⁻¹`. Rewrite using `[← map_inv]`. Conclude with `congrArg (algebraMap E (A E)) (Units.val_inv_eq_inv_val t)`. Use `⟨UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E)), ?_⟩` and prove the remaining obligations.

Establish `hkm : ratS E k = nU (UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E))) * mD (IdeleGroup.diagonal E t⁻¹)`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[M.val_mul, M.val_ratS]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Simplify using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d3, e2]`. Simplify using `only [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2]`. Simplify using `[← map_mul]`. Simplify using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two, e0]`. Simplify using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2, e1]`.

Establish `hgk : g = k * h` using `by rw [hk, inv_mul_cancel_right]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem tri {E : Type} [Field E] [NumberField E] (g h : Matrix.SpecialLinearGroup (Fin 2) E) (t : Eˣ)
    (hrow : g.1 1 = (t : E) • h.1 1) :
    ∃ β : A E, ratS E g = nU β * mD (IdeleGroup.diagonal E t⁻¹) * ratS E h := by
  obtain ⟨k, hk⟩ : ∃ k, k = g * h⁻¹ := ⟨_, rfl⟩
  have hdet : h.1 0 0 * h.1 1 1 - h.1 0 1 * h.1 1 0 = 1 := by
    have hd := h.det_coe
    rwa [Matrix.det_fin_two] at hd
  have hg0 : g.1 1 0 = t * h.1 1 0 := by simpa using congrFun hrow 0
  have hg1 : g.1 1 1 = t * h.1 1 1 := by simpa using congrFun hrow 1
  have e0 : k.1 1 0 = 0 := by
    rw [hk]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg0, hg1]
    ring
  have e1 : k.1 1 1 = t := by
    rw [hk]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg0, hg1]
    linear_combination (t : E) * hdet
  have e2 : k.1 0 0 = ((t⁻¹ : Eˣ) : E) := by
    have hd := k.det_coe
    rw [Matrix.det_fin_two, e0, e1] at hd
    have ht : (t : E) ≠ 0 := t.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hd
  have d2 : (((IdeleGroup.diagonal E t⁻¹)⁻¹ : (A E)ˣ) : A E) = UpperTheory.ConvolutionTheory.R2.rt (t : E) := by
    rw [← map_inv, inv_inv]
    rfl
  have d3 : (((IdeleGroup.diagonal E t)⁻¹ : (A E)ˣ) : A E) = algebraMap E (A E) (t : E)⁻¹ := by
    rw [← map_inv]
    exact congrArg (algebraMap E (A E)) (Units.val_inv_eq_inv_val t)
  refine ⟨UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E)), ?_⟩
  have hkm : ratS E k = nU (UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E))) * mD (IdeleGroup.diagonal E t⁻¹) := by
    refine Subtype.ext ?_
    rw [M.val_mul, M.val_ratS]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d3, e2]
    · simp only [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2]
      simp [← map_mul]
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, e0]
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2, e1]
  have hgk : g = k * h := by rw [hk, inv_mul_cancel_right]
  calc ratS E g = ratS E (k * h) := by rw [← hgk]
    _ = _ := by rw [map_mul, hkm]

/- English proof (translation)
Introduce `hT E _ _`. Take `⟨α, hm, hu, hd⟩` from `hT E`. Take `⟨Tq, hTq⟩ : ∃ Tq : Subgroup (IdeleGroup E), Tq = (IdeleGroup.diagonal E).range` from `⟨_, rfl⟩`. Establish `hmem : ∀ g : Tq, mD g.1 ∈ Gam E`. Introduce and unpack `⟨g, hg⟩`.

Rewrite `hg` using `[hTq]`. Take `⟨t, rfl⟩` from `hg`. Conclude with `M.mD_diag_mem t`. Use `haveI : DiscreteTopology Tq := by`. Use `DiscreteTopology.of_continuous_injective (f := fun g : Tq => (⟨mD g.1, hmem g⟩ : Gam E)) ?_ ?_` and prove the remaining obligations.

Conclude with `(M.continuous_mD.comp continuous_subtype_val).subtype_mk _`. Introduce `a b hab`. Establish `h1 : mD a.1 = mD b.1` using `congrArg (·.1) hab`. Establish `h2` using `congrArg (fun g : G1 E => g.1 0 0) h1`. Conclude with `Subtype.ext (Units.ext (by simpa [mD] using h2))`.

Take `⟨F, hF, huniq, -⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup Tq`. Establish `hdiag : Function.Injective (IdeleGroup.diagonal E)`. Introduce `a b hab`. Establish `h1 : ((IdeleGroup.diagonal E a : (A E)ˣ) : A E) = ((IdeleGroup.diagonal E b : (A E)ˣ) : A E)` using `by rw [hab]`. Conclude with `Units.ext (AdeleRing.algebraMap_injective (𝓞 E) E h1)`.

Use `⟨α ⁻¹' F, hm hF, fun b x => by simp [hu], ?_⟩` and prove the remaining obligations. Introduce `σ hσ x r`. Establish `key : ∀ (t : Eˣ) (r' : {r : Fin 2 → E // r ≠ 0}), r'.1 = (t : E) • r.1 → α (ratS E (σ r') * x) = IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x)`. Introduce `t r' hr`. Take `⟨β, hβ⟩` from `tri (σ r') (σ r) t (by rw [hσ r', hσ r, hr])`.

Rewrite using `[hβ, mul_assoc, mul_assoc, hu, hd]`. Take `⟨⟨g, hg⟩, hgF, hgU⟩` from `huniq (α (ratS E (σ r) * x))`. Establish `hg'` using `hg`. Rewrite `hg'` using `[hTq]`. Take `⟨s, rfl⟩` from `hg'`.

Establish `hne : ((s⁻¹ : Eˣ) : E) • r.1 ≠ 0`. Introduce `h0`. Conclude with `r.2 ((smul_eq_zero.mp h0).resolve_left (Units.ne_zero _))`. Use `⟨s⁻¹, ⟨⟨_, hne⟩, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show α (ratS E (σ _) * x) ∈ F`.

Rewrite using `[key s⁻¹ _ rfl, inv_inv]`. Conclude with `hgF`. Introduce and unpack `t ⟨r', hr'T, hr'⟩`. Establish `hin : IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) ∈ F`. Rewrite using `[← key t r' hr']`.

Conclude with `hr'T`. Establish `hmemt : IdeleGroup.diagonal E t⁻¹ ∈ Tq`. Rewrite using `[hTq]`. Conclude with `⟨_, rfl⟩`. Use `hgU ⟨_, hmemt⟩ hin` as an intermediate fact.

Establish `h2 : IdeleGroup.diagonal E t⁻¹ = IdeleGroup.diagonal E s` using `congrArg Subtype.val this`. Rewrite using `[← inv_inv t, hdiag h2]`.
-/
theorem UpperTheory.exists_unipotentInvariant_set_unique_row_scaling :
    TorCo → ∀ (E : Type) [Field E] [NumberField E], ∃ T : Set (G1 E), MeasurableSet T ∧ (∀ b x, nU b * x ∈ T ↔ x ∈ T) ∧ ∀ σ : {r : Fin 2 → E // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) E, M.RowSec σ → ∀ (x : G1 E) (r : {r : Fin 2 → E // r ≠ 0}), ∃! t : Eˣ, ∃ r' ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, r'.1 = (t : E) • r.1 := by
  intro hT E _ _
  obtain ⟨α, hm, hu, hd⟩ := hT E
  obtain ⟨Tq, hTq⟩ : ∃ Tq : Subgroup (IdeleGroup E), Tq = (IdeleGroup.diagonal E).range := ⟨_, rfl⟩
  have hmem : ∀ g : Tq, mD g.1 ∈ Gam E := by
    rintro ⟨g, hg⟩
    rw [hTq] at hg
    obtain ⟨t, rfl⟩ := hg
    exact M.mD_diag_mem t
  haveI : DiscreteTopology Tq := by
    refine DiscreteTopology.of_continuous_injective (f := fun g : Tq => (⟨mD g.1, hmem g⟩ : Gam E)) ?_ ?_
    · exact (M.continuous_mD.comp continuous_subtype_val).subtype_mk _
    · intro a b hab
      have h1 : mD a.1 = mD b.1 := congrArg (·.1) hab
      have h2 := congrArg (fun g : G1 E => g.1 0 0) h1
      exact Subtype.ext (Units.ext (by simpa [mD] using h2))
  obtain ⟨F, hF, huniq, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Tq
  have hdiag : Function.Injective (IdeleGroup.diagonal E) := by
    intro a b hab
    have h1 : ((IdeleGroup.diagonal E a : (A E)ˣ) : A E) = ((IdeleGroup.diagonal E b : (A E)ˣ) : A E) := by rw [hab]
    exact Units.ext (AdeleRing.algebraMap_injective (𝓞 E) E h1)
  refine ⟨α ⁻¹' F, hm hF, fun b x => by simp [hu], ?_⟩
  intro σ hσ x r
  have key : ∀ (t : Eˣ) (r' : {r : Fin 2 → E // r ≠ 0}), r'.1 = (t : E) • r.1 →
      α (ratS E (σ r') * x) = IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) := by
    intro t r' hr
    obtain ⟨β, hβ⟩ := tri (σ r') (σ r) t (by rw [hσ r', hσ r, hr])
    rw [hβ, mul_assoc, mul_assoc, hu, hd]
  obtain ⟨⟨g, hg⟩, hgF, hgU⟩ := huniq (α (ratS E (σ r) * x))
  have hg' := hg
  rw [hTq] at hg'
  obtain ⟨s, rfl⟩ := hg'
  have hne : ((s⁻¹ : Eˣ) : E) • r.1 ≠ 0 := by
    intro h0
    exact r.2 ((smul_eq_zero.mp h0).resolve_left (Units.ne_zero _))
  refine ⟨s⁻¹, ⟨⟨_, hne⟩, ?_, rfl⟩, ?_⟩
  · show α (ratS E (σ _) * x) ∈ F
    rw [key s⁻¹ _ rfl, inv_inv]
    exact hgF
  · rintro t ⟨r', hr'T, hr'⟩
    have hin : IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) ∈ F := by
      rw [← key t r' hr']
      exact hr'T
    have hmemt : IdeleGroup.diagonal E t⁻¹ ∈ Tq := by
      rw [hTq]
      exact ⟨_, rfl⟩
    have := hgU ⟨_, hmemt⟩ hin
    have h2 : IdeleGroup.diagonal E t⁻¹ = IdeleGroup.diagonal E s := congrArg Subtype.val this
    rw [← inv_inv t, hdiag h2]
