import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.LatSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ZDom
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [finPartPi]`. Conclude with `continuous_snd.comp (continuous_apply i)`.
-/
private theorem cont_finPart : Continuous (fun v : V4 ℚ => finPartPi v) := by
  refine continuous_pi fun i => ?_
  simp only [finPartPi]
  exact continuous_snd.comp (continuous_apply i)

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [infPartPi]`. Use `fun_prop`.
-/
private theorem cont_infPart : Continuous (fun v : V4 ℚ => infPartPi v) := by
  refine continuous_pi fun i => ?_
  simp only [infPartPi]
  fun_prop

/- English proof (translation)
Unfold `wt`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
private theorem wt_nonneg' (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (n : ℕ) (v : V4 ℚ) : 0 ≤ wt K n v := by
  unfold wt
  split_ifs <;> positivity

/- English proof (translation)
Establish `hs : MeasurableSet {v : V4 ℚ | finPartPi v ∈ K}` using `(hK.isClosed.preimage cont_finPart).measurableSet`. Unfold `wt`. Conclude with `Measurable.ite hs (((continuous_const.add cont_infPart.norm).pow n).measurable.inv) measurable_const`.
-/
private theorem wt_meas (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hK : IsCompact K) (n : ℕ) :
    Measurable (fun v : V4 ℚ => wt K n v) := by
  have hs : MeasurableSet {v : V4 ℚ | finPartPi v ∈ K} := (hK.isClosed.preimage cont_finPart).measurableSet
  unfold wt
  exact Measurable.ite hs (((continuous_const.add cont_infPart.norm).pow n).measurable.inv) measurable_const

/- English proof (translation)
Take `⟨c0, C0, hc0, hC0, hred⟩` from `redE E`. Take `⟨-, -, Cz, hCz, hz⟩` from `zDom E`. Take `⟨-, hsc, hnu, -⟩` from `szLaws E D`. Establish `hgl : Continuous (gl : G1 E → GL (Fin 2) (A E))` using `by fun_prop`. Set `C : Set (GL (Fin 2) (A E))` to `(fun p : G1 E × (A E)ˣ => gl p.1 * sZ D p.2) '' (C0 ×ˢ Cz)`.

Establish `hC : IsCompact C` using `(hC0.prod hCz).image ((hgl.comp continuous_fst).mul (hsc.comp continuous_snd))`. Establish `hCn : ∀ k ∈ C, nu ℚ k = 1`. Introduce and unpack `_ ⟨⟨h, z⟩, -, rfl⟩`. Simplify using `only [nu_mul, nu_gl, hnu, mul_one]`. Establish `hc : 0 < min c0 1` using `lt_min hc0 one_pos`.

Take `⟨n, r, B1, hL⟩` from `latSum E D K C (min c0 1) 0 hK hC hCn hc`. Take `⟨hLf, -, hdec⟩` from `decE E P φ hφ`. Take `⟨B2, hB2⟩` from `hdec C hC (min c0 1) hc r`. Use `⟨n, B1 * B2, fun z hzD h => ?_⟩` and prove the remaining obligations. Take `⟨γ, u, b, k, hk, he, hb⟩` from `hred h`.

Take `⟨ρ, hρ⟩` from `(orb1 E D).1 γ`. Establish `hk' : gl k * sZ D (z : IdeleGroup E) ∈ C` using `⟨(k, (z : IdeleGroup E)), ⟨hk, hz z hzD⟩, rfl⟩`. Establish `hY : gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)) = gl (ratS E γ) * (gl h * sZ D (z : IdeleGroup E))`. Rewrite using `[← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, he]`. Establish `hg : gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ)`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hφX : φ.1 (gl h * sZ D (z : IdeleGroup E)) = φ.1 (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))`. Rewrite using `[hY, hg, hLf.2]`.

Establish `hwt : ∀ ξ, D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ) = D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp (ρ ξ))`. Introduce `ξ`. Establish `e : ∀ g X : GL (Fin 2) (A E), (g * X)⁻¹ * g = X⁻¹` using `fun g X => by group`. Rewrite using `[hY, ← hρ, ← D.act_mul, e]`. Establish `h1 : min c0 1 ≤ ab (1 : (A ℚ)ˣ)`.

Establish `: ab (1 : (A ℚ)ˣ) = 1` using `by simp [ab]`. Rewrite using `[this]`. Conclude with `min_le_right _ _`. Establish `hcb : min c0 1 ≤ ab b` using `(min_le_left _ _).trans hb`. Take `⟨hs, hsum, -⟩` from `hL 1 u b _ hk' h1 hcb`.

Simplify using `only [Units.val_one, one_mul] at hs hsum`. Establish `hf : (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) = (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ))) ∘ ρ.toEquiv`. Use function extensionality and compare the values at `ξ`. Conclude with `congrArg (wt K n) (hwt ξ)`. Establish `ht : ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ)) = ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ))`.

Rewrite using `[hf]`. Conclude with `Equiv.tsum_eq ρ.toEquiv (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)))`. Use `⟨by rw [hf]; exact ρ.toEquiv.summable_iff.2 hs, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, hφX]`. Establish `hs0 : 0 ≤ ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ))` using `tsum_nonneg fun _ => wt_nonneg' _ _ _`.

Establish `hab : ab b ≠ 0` using `(lt_of_lt_of_le hc0 hb).ne'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem bound (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2)
    (φ : ↥(Sm E 2)) (hφ : φ ∈ P.V) (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ (n : ℕ) (B : ℝ), ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E,
      (Summable fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) ∧
      (∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) *
        ‖φ.1 (gl h * sZ D (z : IdeleGroup E))‖ ≤ B := by
  obtain ⟨c0, C0, hc0, hC0, hred⟩ := redE E
  obtain ⟨-, -, Cz, hCz, hz⟩ := zDom E
  obtain ⟨-, hsc, hnu, -⟩ := szLaws E D
  have hgl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
  let C : Set (GL (Fin 2) (A E)) := (fun p : G1 E × (A E)ˣ => gl p.1 * sZ D p.2) '' (C0 ×ˢ Cz)
  have hC : IsCompact C :=
    (hC0.prod hCz).image ((hgl.comp continuous_fst).mul (hsc.comp continuous_snd))
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro _ ⟨⟨h, z⟩, -, rfl⟩
    simp only [nu_mul, nu_gl, hnu, mul_one]
  have hc : 0 < min c0 1 := lt_min hc0 one_pos
  obtain ⟨n, r, B1, hL⟩ := latSum E D K C (min c0 1) 0 hK hC hCn hc
  obtain ⟨hLf, -, hdec⟩ := decE E P φ hφ
  obtain ⟨B2, hB2⟩ := hdec C hC (min c0 1) hc r
  refine ⟨n, B1 * B2, fun z hzD h => ?_⟩
  obtain ⟨γ, u, b, k, hk, he, hb⟩ := hred h
  obtain ⟨ρ, hρ⟩ := (orb1 E D).1 γ
  have hk' : gl k * sZ D (z : IdeleGroup E) ∈ C := ⟨(k, (z : IdeleGroup E)), ⟨hk, hz z hzD⟩, rfl⟩
  have hY : gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)) =
      gl (ratS E γ) * (gl h * sZ D (z : IdeleGroup E)) := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, he]
  have hg : gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
    apply Units.ext
    ext i j
    rfl
  have hφX : φ.1 (gl h * sZ D (z : IdeleGroup E)) =
      φ.1 (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E))) := by
    rw [hY, hg, hLf.2]
  have hwt : ∀ ξ, D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ) =
      D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp (ρ ξ)) := by
    intro ξ
    have e : ∀ g X : GL (Fin 2) (A E), (g * X)⁻¹ * g = X⁻¹ := fun g X => by group
    rw [hY, ← hρ, ← D.act_mul, e]
  have h1 : min c0 1 ≤ ab (1 : (A ℚ)ˣ) := by
    have : ab (1 : (A ℚ)ˣ) = 1 := by simp [ab]
    rw [this]
    exact min_le_right _ _
  have hcb : min c0 1 ≤ ab b := (min_le_left _ _).trans hb
  obtain ⟨hs, hsum, -⟩ := hL 1 u b _ hk' h1 hcb
  simp only [Units.val_one, one_mul] at hs hsum
  have hf : (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) =
      (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ))) ∘
        ρ.toEquiv := by
    funext ξ
    exact congrArg (wt K n) (hwt ξ)
  have ht : ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ)) =
      ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)) := by
    rw [hf]
    exact Equiv.tsum_eq ρ.toEquiv (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)))
  refine ⟨by rw [hf]; exact ρ.toEquiv.summable_iff.2 hs, ?_⟩
  rw [ht, hφX]
  have hs0 : 0 ≤ ∑' ξ : Fin 4 → ℚ,
      wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)) :=
    tsum_nonneg fun _ => wt_nonneg' _ _ _
  have hab : ab b ≠ 0 := (lt_of_lt_of_le hc0 hb).ne'
  calc _ ≤ (B1 * ab b ^ r) * (B2 * (ab b)⁻¹ ^ r) :=
        mul_le_mul hsum (hB2 u b _ hk' hcb) (norm_nonneg _) (hs0.trans hsum)
    _ = B1 * B2 := by
        rw [inv_pow]
        field_simp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `hgl : Continuous (gl : G1 E → GL (Fin 2) (A E))` using `by fun_prop`. Take `⟨-, hsc, -⟩` from `szLaws E D`. Conclude with `(hgl.comp continuous_snd).mul (hsc.comp (continuous_subtype_val.comp continuous_fst))`.
-/
private theorem cont_el (D : Dat ℚ E) : Continuous fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E =>
    gl p.2 * sZ D (p.1 : IdeleGroup E) := by
  have hgl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
  obtain ⟨-, hsc, -⟩ := szLaws E D
  exact (hgl.comp continuous_snd).mul (hsc.comp (continuous_subtype_val.comp continuous_fst))

/- English proof (translation)
The claim follows from `measurable_fst.prodMk (measurable_fst.comp measurable_snd)`.
-/
private theorem meas_proj (δ : ℚ) : Measurable fun y : Y E δ => ((y.1, y.2.1) : ↥(IdeleGroup.normOneSubgroup E) × G1 E) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

/- English proof (translation)
Take `⟨ρ', hρc, hρ, -⟩` from `actCont ℚ E D`. Establish `hcact : ∀ v, Continuous fun x : GL (Fin 2) (A E) => D.act x v` using `fun v => by`. Simplify using `only [hρ]`. Conclude with `(Units.continuous_val.comp hρc).matrix_mulVec continuous_const`. Use `haveI : MeasurableSingletonClass (Orb D.δ) := ⟨fun _ => trivial⟩`.

Establish `hc : ∀ ξ : Orb D.δ, Continuous fun x : ↥(IdeleGroup.normOneSubgroup E) × G1 E => D.act (gl x.2 * sZ D (x.1 : IdeleGroup E))⁻¹ (rp ξ.1)` using `fun ξ => (hcact (rp ξ.1)).comp (cont_el D).inv`. Establish `hf : Measurable fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ => D.act (gl p.1.2 * sZ D (p.1.1 : IdeleGroup E))⁻¹ (rp p.2.1)` using `measurable_from_prod_countable_left fun ξ => (hc ξ).measurable`. Establish `h2 : Measurable fun y : Y E D.δ => (((y.1, y.2.1), y.2.2) : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ)` using `(meas_proj D.δ).prodMk (measurable_snd.comp measurable_snd)`. Establish `e : pY D = (fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ => D.act (gl p.1.2 * sZ D (p.1.1 : IdeleGroup E))⁻¹ (rp p.2.1)) ∘ fun y : Y E D.δ => (((y.1, y.2.1), y.2.2) : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ)`. Use function extensionality and compare the values at `y`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hf.comp h2`.
-/
private theorem meas_pY (D : Dat ℚ E) : Measurable (pY D) := by
  obtain ⟨ρ', hρc, hρ, -⟩ := actCont ℚ E D
  have hcact : ∀ v, Continuous fun x : GL (Fin 2) (A E) => D.act x v := fun v => by
    simp only [hρ]
    exact (Units.continuous_val.comp hρc).matrix_mulVec continuous_const
  haveI : MeasurableSingletonClass (Orb D.δ) := ⟨fun _ => trivial⟩
  have hc : ∀ ξ : Orb D.δ, Continuous fun x : ↥(IdeleGroup.normOneSubgroup E) × G1 E =>
      D.act (gl x.2 * sZ D (x.1 : IdeleGroup E))⁻¹ (rp ξ.1) := fun ξ => (hcact (rp ξ.1)).comp (cont_el D).inv
  have hf : Measurable fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ =>
      D.act (gl p.1.2 * sZ D (p.1.1 : IdeleGroup E))⁻¹ (rp p.2.1) :=
    measurable_from_prod_countable_left fun ξ => (hc ξ).measurable
  have h2 : Measurable fun y : Y E D.δ =>
      (((y.1, y.2.1), y.2.2) : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ) :=
    (meas_proj D.δ).prodMk (measurable_snd.comp measurable_snd)
  have e : pY D = (fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ =>
      D.act (gl p.1.2 * sZ D (p.1.1 : IdeleGroup E))⁻¹ (rp p.2.1)) ∘ fun y : Y E D.δ =>
      (((y.1, y.2.1), y.2.2) : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ) := by
    funext y
    rfl
  rw [e]
  exact hf.comp h2

/- English proof (translation)
Establish `h1 : Measurable fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E => f (gl p.2 * sZ D (p.1 : IdeleGroup E))` using `(hf.comp (cont_el D)).measurable`. Establish `e : (fun y : Y E D.δ => f (el D y)) = (fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E => f (gl p.2 * sZ D (p.1 : IdeleGroup E))) ∘ fun y : Y E D.δ => ((y.1, y.2.1) : ↥(IdeleGroup.normOneSubgroup E) × G1 E)`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `h1.comp (meas_proj D.δ)`.
-/
private theorem meas_el (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ) (hf : Continuous f) :
    Measurable fun y : Y E D.δ => f (el D y) := by
  have h1 : Measurable fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E => f (gl p.2 * sZ D (p.1 : IdeleGroup E)) :=
    (hf.comp (cont_el D)).measurable
  have e : (fun y : Y E D.δ => f (el D y)) = (fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E =>
      f (gl p.2 * sZ D (p.1 : IdeleGroup E))) ∘ fun y : Y E D.δ =>
      ((y.1, y.2.1) : ↥(IdeleGroup.normOneSubgroup E) × G1 E) := by
    funext y
    rfl
  rw [e]
  exact h1.comp (meas_proj D.δ)

/- English proof (translation)
Use `haveI : MeasurableSingletonClass (Orb D.δ) := ⟨fun _ => trivial⟩`. Establish `hwm : Measurable fun y : Y E D.δ => wt K n (pY D y)` using `(wt_meas K hK n).comp (meas_pY D)`. Establish `hwc : Measurable fun y : Y E D.δ => ((wt K n (pY D y) : ℝ) : ℂ)` using `Complex.measurable_ofReal.comp hwm`. Establish `hm : Measurable fun y : Y E D.δ => ((wt K n (pY D y) : ℝ) : ℂ) * f (el D y)` using `hwc.mul (meas_el D f hf)`. Use `⟨hm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Take `⟨hZ, hDz, -⟩` from `zDom E`. Use `haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by rw [Measure.restrict_apply_univ]; exact hZ⟩`. Use `haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by rw [Measure.restrict_apply_univ]; exact volE E N⟩`. Set `g : Y E D.δ → ℝ≥0∞` to `fun y => ‖((wt K n (pY D y) : ℝ) : ℂ) * f (el D y)‖ₑ`. Establish `hg : Measurable g` using `hm.enorm`.

Establish `key : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E, ∫⁻ ξ : Orb D.δ, g (z, (h, ξ)) ∂Measure.count ≤ ENNReal.ofReal B`. Introduce `z hz h`. Take `⟨hs, hb⟩` from `hB z hz h`. Rewrite using `[lintegral_count]`. Set `wq : (Fin 4 → ℚ) → ℝ` to `fun ξ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ)) * ‖f (gl h * sZ D (z : IdeleGroup E))‖`.

Establish `e : ∀ ξ : Orb D.δ, g (z, (h, ξ)) = ENNReal.ofReal (wq ξ.1)`. Introduce `ξ`. Establish `e1 : pY D (z, (h, ξ)) = D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ.1)` using `rfl`. Establish `e2 : el D (z, (h, ξ)) = gl h * sZ D (z : IdeleGroup E)` using `rfl`. Simplify using `only [g, wq]`.

Rewrite using `[e1, e2, ← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg' _ _ _)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmY : mY D.δ N = ((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod ((N.μ.restrict N.D).prod Measure.count)` using `rfl`. Establish `hfin : ∫⁻ y, g y ∂mY D.δ N < ⊤`. Rewrite using `[hmY, lintegral_prod _ hg.aemeasurable]`.

Establish `hle : ∫⁻ z, ∫⁻ p, g (z, p) ∂((N.μ.restrict N.D).prod Measure.count) ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)) ≤ ∫⁻ _, ENNReal.ofReal B * (N.μ.restrict N.D) Set.univ ∂((normOneMeasure E).restrict (normOneFundamentalDomain E))`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem hDz] with z hz`. Establish `hgz : Measurable fun p : G1 E × Orb D.δ => g (z, p)` using `hg.comp measurable_prodMk_left`. Rewrite using `[lintegral_prod (fun p : G1 E × Orb D.δ => g (z, p)) hgz.aemeasurable]`.

Combine the equalities or inequalities in the displayed calculation. Use `hle.trans_lt ?_` and prove the remaining obligations. Rewrite using `[lintegral_const]`. Conclude with `ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)) (measure_lt_top _ _)`. Conclude with `hfin`.
-/
private theorem fin_int (D : Dat ℚ E) (N : MeasE E) (f : GL (Fin 2) (A E) → ℂ) (hf : Continuous f)
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hK : IsCompact K) (n : ℕ) (B : ℝ)
    (hB : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E,
      (Summable fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) ∧
      (∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) *
        ‖f (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) :
    Integrable (fun y => (wt K n (pY D y) : ℂ) * f (el D y)) (mY D.δ N) := by
  haveI : MeasurableSingletonClass (Orb D.δ) := ⟨fun _ => trivial⟩
  have hwm : Measurable fun y : Y E D.δ => wt K n (pY D y) := (wt_meas K hK n).comp (meas_pY D)
  have hwc : Measurable fun y : Y E D.δ => ((wt K n (pY D y) : ℝ) : ℂ) := Complex.measurable_ofReal.comp hwm
  have hm : Measurable fun y : Y E D.δ => ((wt K n (pY D y) : ℝ) : ℂ) * f (el D y) := hwc.mul (meas_el D f hf)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  obtain ⟨hZ, hDz, -⟩ := zDom E
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hZ⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volE E N⟩
  let g : Y E D.δ → ℝ≥0∞ := fun y => ‖((wt K n (pY D y) : ℝ) : ℂ) * f (el D y)‖ₑ
  have hg : Measurable g := hm.enorm
  have key : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E,
      ∫⁻ ξ : Orb D.δ, g (z, (h, ξ)) ∂Measure.count ≤ ENNReal.ofReal B := by
    intro z hz h
    obtain ⟨hs, hb⟩ := hB z hz h
    rw [lintegral_count]
    let wq : (Fin 4 → ℚ) → ℝ := fun ξ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ)) *
      ‖f (gl h * sZ D (z : IdeleGroup E))‖
    have e : ∀ ξ : Orb D.δ, g (z, (h, ξ)) = ENNReal.ofReal (wq ξ.1) := by
      intro ξ
      have e1 : pY D (z, (h, ξ)) = D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ.1) := rfl
      have e2 : el D (z, (h, ξ)) = gl h * sZ D (z : IdeleGroup E) := rfl
      simp only [g, wq]
      rw [e1, e2, ← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg' _ _ _)]
    calc _ = ∑' ξ : Orb D.δ, ENNReal.ofReal (wq ξ.1) := tsum_congr e
      _ ≤ ∑' ξ : Fin 4 → ℚ, ENNReal.ofReal (wq ξ) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun ξ => ENNReal.ofReal (wq ξ)
      _ = ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, wq ξ) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (wt_nonneg' _ _ _) (norm_nonneg _))
            (hs.mul_right _)).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by simp only [wq]; rw [tsum_mul_right]; exact hb)
  have hmY : mY D.δ N = ((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod
      ((N.μ.restrict N.D).prod Measure.count) := rfl
  have hfin : ∫⁻ y, g y ∂mY D.δ N < ⊤ := by
    rw [hmY, lintegral_prod _ hg.aemeasurable]
    have hle : ∫⁻ z, ∫⁻ p, g (z, p)
          ∂((N.μ.restrict N.D).prod Measure.count) ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)) ≤
        ∫⁻ _, ENNReal.ofReal B * (N.μ.restrict N.D) Set.univ
          ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hDz] with z hz
      have hgz : Measurable fun p : G1 E × Orb D.δ => g (z, p) := hg.comp measurable_prodMk_left
      rw [lintegral_prod (fun p : G1 E × Orb D.δ => g (z, p)) hgz.aemeasurable]
      calc _ ≤ ∫⁻ _, ENNReal.ofReal B ∂(N.μ.restrict N.D) := lintegral_mono fun h => key z hz h
        _ = _ := lintegral_const _
    refine hle.trans_lt ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)) (measure_lt_top _ _)
  exact hfin

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

/- English proof (translation)
Introduce `E _ _ _ D W M N P φ hφ`. Establish `hφc : Continuous φ.1` using `(decE E P φ hφ).1.1`. Use `⟨meas_pY D, meas_el D φ.1 hφc, fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨n, B, hB⟩` from `bound E D P φ hφ K hK`. Conclude with `⟨n, fin_int D N φ.1 hφc K hK n B hB⟩`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.yInt :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.YInt := by
  intro E _ _ _ D W M N P φ hφ
  have hφc : Continuous φ.1 := (decE E P φ hφ).1.1
  refine ⟨meas_pY D, meas_el D φ.1 hφc, fun K hK => ?_⟩
  obtain ⟨n, B, hB⟩ := bound E D P φ hφ K hK
  exact ⟨n, fin_int D N φ.1 hφc K hK n B hB⟩
