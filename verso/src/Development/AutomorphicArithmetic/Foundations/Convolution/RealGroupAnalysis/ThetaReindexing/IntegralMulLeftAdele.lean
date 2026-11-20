import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

/- English proof (translation)
Establish `hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹` using `inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le`. Establish `hmap` using `map_smul_adeleMeasure (K := F) a`. Establish `he : MeasurableEmbedding (fun x : A F => a • x)` using `(Homeomorph.smul a).measurableEmbedding`. Establish `h1 : ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) = ∫ s, g s ∂((adeleMeasure F).map (fun x : A F => a • x))` using `(he.integral_map g).symm`. Rewrite using `[h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]`.

Rewrite using `[Complex.real_smul]`. Both sides reduce to the same expression.
-/
private theorem integral_mul_left_adele {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (g : A F → ℂ) :
    ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, g s ∂(adeleMeasure F) := by
  have hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹ := inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le
  have hmap := map_smul_adeleMeasure (K := F) a
  have he : MeasurableEmbedding (fun x : A F => a • x) :=
    (Homeomorph.smul a).measurableEmbedding
  have h1 : ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) =
      ∫ s, g s ∂((adeleMeasure F).map (fun x : A F => a • x)) :=
    (he.integral_map g).symm
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]
  rw [Complex.real_smul]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W a φ v`. Establish `hab : ((ab a : ℝ) : ℂ) ≠ 0`. Conclude with `ne_of_gt (IdeleGroup.ideleModule F a).2` after adjusting the coercions. Use `set w : V4 F := ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] with hw`. Establish `hpt : ∀ s : A F, (fun i => (a : A F) * Function.update v 1 s i) = Function.update w 1 ((a : A F) * s)`.

Introduce `s`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [hw, Function.update]`. Establish `hch : ∀ s : A F, (a : A F) * s * w 1 = s * v 1`. Introduce `s`.

Establish `: w 1 = ((a⁻¹ : (A F)ˣ) : A F) * v 1` using `by simp [hw]`. Rewrite using `[this, mul_mul_mul_comm, Units.mul_inv, one_mul]`. Take `⟨G, hG⟩ : ∃ G : A F → ℂ, G = fun r => φ.1 (Function.update w 1 r) * ψ (-(r * w 1))` from `⟨_, rfl⟩`. Establish `hL : hat (W.Om (mD a) φ).1 v = ∫ s, ((W.η.1 a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * G ((a : A F) * s) ∂(adeleMeasure F)`. Unfold `hat`.

Use `integral_congr_ae (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [W.Om_m, hpt s, hG, hch s]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : hat φ.1 w = ∫ s, G s ∂(adeleMeasure F)`. Rewrite using `[hG]`.

Both sides reduce to the same expression. Rewrite using `[hL, integral_const_mul, integral_mul_left_adele, hR]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.ConvolutionTheory.R2.D.hatM :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (a : (A F)ˣ) φ v, hat (W.Om (mD a) φ).1 v = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
      hat φ.1 ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] := by
  intro F E _ _ _ _ _ _ _ D W a φ v
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (IdeleGroup.ideleModule F a).2
  set w : V4 F := ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] with hw
  have hpt : ∀ s : A F, (fun i => (a : A F) * Function.update v 1 s i) =
      Function.update w 1 ((a : A F) * s) := by
    intro s
    funext i
    fin_cases i <;> simp [hw, Function.update]
  have hch : ∀ s : A F, (a : A F) * s * w 1 = s * v 1 := by
    intro s
    have : w 1 = ((a⁻¹ : (A F)ˣ) : A F) * v 1 := by simp [hw]
    rw [this, mul_mul_mul_comm, Units.mul_inv, one_mul]
  obtain ⟨G, hG⟩ : ∃ G : A F → ℂ, G = fun r => φ.1 (Function.update w 1 r) * ψ (-(r * w 1)) := ⟨_, rfl⟩
  have hL : hat (W.Om (mD a) φ).1 v =
      ∫ s, ((W.η.1 a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * G ((a : A F) * s) ∂(adeleMeasure F) := by
    unfold hat
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [W.Om_m, hpt s, hG, hch s]
    ring
  have hR : hat φ.1 w = ∫ s, G s ∂(adeleMeasure F) := by
    rw [hG]
    rfl
  rw [hL, integral_const_mul, integral_mul_left_adele, hR]
  push_cast
  field_simp
