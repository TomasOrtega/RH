import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie

open MeasureTheory BoundedContinuousFunction
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.CharFourierInj

variable {G A : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A]

/- English proof (translation)
Use `letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G`. Use `haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup`. Use `haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace`. Use `haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated`. Use `haveI : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance`.

Use `infer_instance`.
-/
theorem polish : PolishSpace G := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance
  infer_instance

def bchar (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a)) (hn : ∀ a x, ‖χ a x‖ = 1) (a : A) : G →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨χ a, hc a⟩ 2 fun x y => by
    calc dist (χ a x) (χ a y) ≤ ‖χ a x‖ + ‖χ a y‖ := dist_le_norm_add_norm _ _
      _ = 2 := by rw [hn, hn]; norm_num

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bchar_apply (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a)) (hn : ∀ a x, ‖χ a x‖ = 1) (a : A) (x : G) :
    bchar χ hc hn a x = χ a x := rfl

/- English proof (translation)
The claim follows from `hφ.mul_bdd g.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)`.
-/
theorem integrable_mul_bcf (μ : Measure G) (g : G →ᵇ ℂ) {φ : G → ℂ} (hφ : Integrable φ μ) :
    Integrable (fun x => φ x * g x) μ := hφ.mul_bdd g.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)

/- English proof (translation)
Establish `h1 : χ a x * χ (-a) x = 1` using `by rw [← ha, add_neg_cancel, h0]`. Establish `h2 : χ a x * (starRingEnd ℂ) (χ a x) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]`. Evaluate the numerical expressions. Establish `hne : χ a x ≠ 0` using `fun h => by simpa [h] using hn a x`.

Conclude with `mul_left_cancel₀ hne (h2.trans h1.symm)`.
-/
private theorem exists_integer_complexConj (χ : A → G → ℂ) (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1)
    (hn : ∀ a x, ‖χ a x‖ = 1) (a : A) (x : G) : (starRingEnd ℂ) (χ a x) = χ (-a) x := by
  have h1 : χ a x * χ (-a) x = 1 := by rw [← ha, add_neg_cancel, h0]
  have h2 : χ a x * (starRingEnd ℂ) (χ a x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  have hne : χ a x ≠ 0 := fun h => by simpa [h] using hn a x
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

/- English proof (translation)
Use `haveI : PolishSpace G := polish`. Use `set B : A → (G →ᵇ ℂ) := bchar χ hc hn with hB`. Establish `hBx : ∀ a x, B a x = χ a x` using `fun a x => bchar_apply χ hc hn a x`. Establish `hBmul : ∀ a b, B a * B b = B (a + b)`. Introduce `a b`.

Use extensionality with `x`. Rewrite using `[BoundedContinuousFunction.coe_mul, Pi.mul_apply, hBx, hBx, hBx, ha]`. Establish `hBone : B 0 = 1`. Use extensionality with `x`. Rewrite using `[hBx, h0, BoundedContinuousFunction.coe_one, Pi.one_apply]`.

Establish `hBstar : ∀ a, star (B a) = B (-a)`. Introduce `a`. Use extensionality with `x`. Rewrite using `[BoundedContinuousFunction.star_apply, hBx, hBx]`. Conclude with `exists_integer_complexConj χ ha h0 hn a x`.

Establish `hmem : ∀ a, B a ∈ Submodule.span ℂ (Set.range B)` using `fun a => Submodule.subset_span ⟨a, rfl⟩`. Establish `hmul : ∀ p ∈ Submodule.span ℂ (Set.range B), ∀ q ∈ Submodule.span ℂ (Set.range B), p * q ∈ Submodule.span ℂ (Set.range B)`. Introduce `p hp q hq`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem p hp`.

Take `⟨a, rfl⟩` from `hp`. Proceed by induction on `hq using Submodule.span_induction with`. Consider the case `mem q hq => obtain ⟨b, rfl⟩ := hq`. Rewrite using `[hBmul]`. Conclude with `hmem _`.

Consider the case `zero => rw [mul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add q q' _ _ h h' => rw [mul_add]`. Conclude with `Submodule.add_mem _ h h'`. Consider the case `smul c q _ h => rw [mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ c h`. Consider the case `zero => rw [zero_mul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add p p' _ _ h h' => rw [add_mul]`. Conclude with `Submodule.add_mem _ h h'`.

Consider the case `smul c p _ h => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c h`. Establish `hstar : ∀ p ∈ Submodule.span ℂ (Set.range B), star p ∈ Submodule.span ℂ (Set.range B)`. Introduce `p hp`. Proceed by induction on `hp using Submodule.span_induction with`.

Consider the case `mem p hp => obtain ⟨a, rfl⟩ := hp`. Rewrite using `[hBstar]`. Conclude with `hmem _`. Consider the case `zero => rw [star_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add p p' _ _ h h' => rw [star_add]`. Conclude with `Submodule.add_mem _ h h'`. Consider the case `smul c p _ h => rw [star_smul]`. Conclude with `Submodule.smul_mem _ _ h`. Set `Al : StarSubalgebra ℂ (G →ᵇ ℂ)` to `{ carrier := (Submodule.span ℂ (Set.range B) : Set (G →ᵇ ℂ)) mul_mem' := fun {p q} hp hq => hmul p hp q hq one_mem' := by rw [← hBone]; exact hmem 0 add_mem' := fun {p q} hp hq => Submodule.add_mem _ hp hq zero_mem' := Submodule.zero_mem _ algebraMap_mem' := fun c => by`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, ← hBone]`. Conclude with `Submodule.smul_mem _ c (hmem 0)`. Use the proof step `star_mem' := fun {p} hp => hstar p hp }`. Establish `hsepA : (Al.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints`. Introduce `x y hxy`.

Choose the witnesses or unpack the hypotheses as in `⟨a, hax⟩ : ∃ a, χ a (x - y) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hxy (sub_eq_zero.mp (hsep _ hcon))`. Use `⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℂ (B a), StarSubalgebra.mem_map.mpr ⟨B a, hmem a, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations.

Introduce `hxy'`. Apply `hax` to reduce the goal to its premises. Establish `hy0 : χ a y ≠ 0` using `fun h => by simpa [h] using hn a y`. Establish `e1 : χ a x = χ a (x - y) * χ a y` using `by rw [← hx, sub_add_cancel]`. Establish `e2 : χ a x = χ a y` using `by rw [← hBx, ← hBx]; exact hxy'`.

Conclude with `mul_right_cancel₀ hy0 (by rw [← e1, e2, one_mul])`. Establish `hpos : ∀ u : G → ℝ, Integrable u μ → ∀ g : G →ᵇ ℂ, ∫ x, g x ∂(μ.withDensity fun x => ((u x).toNNReal : ℝ≥0∞)) = ∫ x, ((max (u x) 0 : ℝ) : ℂ) * g x ∂μ`. Introduce `u hu g`. Rewrite using `[integral_withDensity_eq_integral_smul₀ hu.1.aemeasurable.real_toNNReal]`. Use `congr 1`.

Establish `hintp : ∀ u : G → ℝ, Integrable u μ → ∀ g : G →ᵇ ℂ, Integrable (fun x => ((max (u x) 0 : ℝ) : ℂ) * g x) μ` using `fun u hu g => integrable_mul_bcf μ g (φ := fun x => ((max (u x) 0 : ℝ) : ℂ)) hu.real_toNNReal.ofReal`. Establish `hI : ∀ g : G →ᵇ ℂ, ∫ x, g x ∂(μ.withDensity fun x => ((f x).toNNReal : ℝ≥0∞)) - ∫ x, g x ∂(μ.withDensity fun x => ((-f x).toNNReal : ℝ≥0∞)) = ∫ x, (f x : ℂ) * g x ∂μ`. Introduce `g`. Rewrite using `[hpos f hi g, hpos (fun x => -f x) hi.neg g, ← integral_sub (hintp f hi g) (hintp (fun x => -f x) hi.neg g)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Establish `e : max (f x) 0 - max (-f x) 0 = f x`. Break down `le_total 0 (f x) with h | h` into its components or cases. Rewrite using `[max_eq_left h, max_eq_right (by linarith)]; ring`. Rewrite using `[max_eq_right h, max_eq_left (by linarith)]; ring`.

Rewrite using `[← sub_mul, ← Complex.ofReal_sub, e]`. Establish `hZ : ∀ g ∈ Submodule.span ℂ (Set.range B), ∫ x, (f x : ℂ) * g x ∂μ = 0`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`.

Take `⟨a, rfl⟩` from `hg`. Rewrite using `[show (fun x => (f x : ℂ) * B a x) = fun x => χ a x * (f x : ℂ) from`. Use function extensionality and compare the values at `fun x => by rw [hBx, mul_comm]]`. Conclude with `h a`. Consider the case `zero => show ∫ x, (f x : ℂ) * 0 ∂μ = 0`.

Simplify using the standard rewrite rules. Consider the case `add g g' _ _ h1 h2 => show ∫ x, (f x : ℂ) * (g x + g' x) ∂μ = 0`. Repeatedly rewrite using `[mul_add]`. Rewrite using `[integral_add (integrable_mul_bcf μ g (φ := fun x => (f x : ℂ)) hi.ofReal) (integrable_mul_bcf μ g' (φ := fun x => (f x : ℂ)) hi.ofReal), h1, h2, add_zero]`. Consider the case `smul c g _ h1 => show ∫ x, (f x : ℂ) * (c * g x) ∂μ = 0`.

Rewrite using `[show (fun x => (f x : ℂ) * (c * g x)) = fun x => c * ((f x : ℂ) * g x) from`. Use function extensionality and compare the values at `fun x => by ring, integral_const_mul, h1, mul_zero]`. Use `haveI : IsFiniteMeasure (μ.withDensity fun x => ((f x).toNNReal : ℝ≥0∞)) := isFiniteMeasure_withDensity_ofReal hi.2`. Use `haveI : IsFiniteMeasure (μ.withDensity fun x => ((-f x).toNNReal : ℝ≥0∞)) := isFiniteMeasure_withDensity_ofReal hi.neg.2`. Establish `hPP` using `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish hsepA (fun g hg => sub_eq_zero.mp ((hI g).trans (hZ g hg)))`.

Establish `hae` using `(withDensity_eq_iff_of_sigmaFinite hf.measurable.real_toNNReal.coe_nnreal_ennreal.aemeasurable hf.measurable.neg.real_toNNReal.coe_nnreal_ennreal.aemeasurable).mp hPP`. Establish `h0ae : f =ᵐ[μ] 0` using `by filter_upwards [hae] with x hx`. Establish `h' : max (f x) 0 = max (-f x) 0`. Use `congrArg NNReal.toReal (ENNReal.coe_inj.mp hx)` as an intermediate fact. Rewrite `this` using `[Real.coe_toNNReal', Real.coe_toNNReal']`. Then use the resulting hypothesis.

Rewrite using `[Pi.zero_apply]`. Break down `lt_trichotomy (f x) 0 with hl | hl | hl` into its components or cases. Rewrite using `[max_eq_right hl.le, max_eq_left (by linarith)] at h'; linarith`. Conclude with `hl`. Rewrite using `[max_eq_left hl.le, max_eq_right (by linarith)] at h'; linarith`.

Conclude with `(Continuous.ae_eq_iff_eq (μ := μ) hf continuous_zero).mp h0ae`.
-/
theorem real_eq_zero (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a)) (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y)
    (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1) (hn : ∀ a x, ‖χ a x‖ = 1)
    (hsep : ∀ x, (∀ a, χ a x = 1) → x = 0) (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ) (hf : Continuous f)
    (hi : Integrable f μ) (h : ∀ a, ∫ x, χ a x * (f x : ℂ) ∂μ = 0) : f = 0 := by
  haveI : PolishSpace G := polish
  set B : A → (G →ᵇ ℂ) := bchar χ hc hn with hB
  have hBx : ∀ a x, B a x = χ a x := fun a x => bchar_apply χ hc hn a x
  have hBmul : ∀ a b, B a * B b = B (a + b) := by
    intro a b; ext x; rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hBx, hBx, hBx, ha]
  have hBone : B 0 = 1 := by
    ext x; rw [hBx, h0, BoundedContinuousFunction.coe_one, Pi.one_apply]
  have hBstar : ∀ a, star (B a) = B (-a) := by
    intro a; ext x; rw [BoundedContinuousFunction.star_apply, hBx, hBx]; exact exists_integer_complexConj χ ha h0 hn a x
  have hmem : ∀ a, B a ∈ Submodule.span ℂ (Set.range B) := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hmul : ∀ p ∈ Submodule.span ℂ (Set.range B), ∀ q ∈ Submodule.span ℂ (Set.range B), p * q ∈ Submodule.span ℂ (Set.range B) := by
    intro p hp q hq
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨a, rfl⟩ := hp
      induction hq using Submodule.span_induction with
      | mem q hq => obtain ⟨b, rfl⟩ := hq; rw [hBmul]; exact hmem _
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add q q' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
      | smul c q _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add p p' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
    | smul c p _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  have hstar : ∀ p ∈ Submodule.span ℂ (Set.range B), star p ∈ Submodule.span ℂ (Set.range B) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp => obtain ⟨a, rfl⟩ := hp; rw [hBstar]; exact hmem _
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add p p' _ _ h h' => rw [star_add]; exact Submodule.add_mem _ h h'
    | smul c p _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h
  let Al : StarSubalgebra ℂ (G →ᵇ ℂ) :=
    { carrier := (Submodule.span ℂ (Set.range B) : Set (G →ᵇ ℂ))
      mul_mem' := fun {p q} hp hq => hmul p hp q hq
      one_mem' := by rw [← hBone]; exact hmem 0
      add_mem' := fun {p q} hp hq => Submodule.add_mem _ hp hq
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, ← hBone]; exact Submodule.smul_mem _ c (hmem 0)
      star_mem' := fun {p} hp => hstar p hp }
  have hsepA : (Al.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, hax⟩ : ∃ a, χ a (x - y) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hxy (sub_eq_zero.mp (hsep _ hcon))
    refine ⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℂ (B a),
      StarSubalgebra.mem_map.mpr ⟨B a, hmem a, rfl⟩, rfl⟩, ?_⟩
    intro hxy'
    apply hax
    have hy0 : χ a y ≠ 0 := fun h => by simpa [h] using hn a y
    have e1 : χ a x = χ a (x - y) * χ a y := by rw [← hx, sub_add_cancel]
    have e2 : χ a x = χ a y := by rw [← hBx, ← hBx]; exact hxy'
    exact mul_right_cancel₀ hy0 (by rw [← e1, e2, one_mul])
  have hpos : ∀ u : G → ℝ, Integrable u μ → ∀ g : G →ᵇ ℂ,
      ∫ x, g x ∂(μ.withDensity fun x => ((u x).toNNReal : ℝ≥0∞)) = ∫ x, ((max (u x) 0 : ℝ) : ℂ) * g x ∂μ := by
    intro u hu g
    rw [integral_withDensity_eq_integral_smul₀ hu.1.aemeasurable.real_toNNReal]
    congr 1
  have hintp : ∀ u : G → ℝ, Integrable u μ → ∀ g : G →ᵇ ℂ,
      Integrable (fun x => ((max (u x) 0 : ℝ) : ℂ) * g x) μ := fun u hu g =>
    integrable_mul_bcf μ g (φ := fun x => ((max (u x) 0 : ℝ) : ℂ)) hu.real_toNNReal.ofReal
  have hI : ∀ g : G →ᵇ ℂ, ∫ x, g x ∂(μ.withDensity fun x => ((f x).toNNReal : ℝ≥0∞)) -
      ∫ x, g x ∂(μ.withDensity fun x => ((-f x).toNNReal : ℝ≥0∞)) = ∫ x, (f x : ℂ) * g x ∂μ := by
    intro g
    rw [hpos f hi g, hpos (fun x => -f x) hi.neg g, ← integral_sub (hintp f hi g) (hintp (fun x => -f x) hi.neg g)]
    congr 1; funext x
    have e : max (f x) 0 - max (-f x) 0 = f x := by
      rcases le_total 0 (f x) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [← sub_mul, ← Complex.ofReal_sub, e]
  have hZ : ∀ g ∈ Submodule.span ℂ (Set.range B), ∫ x, (f x : ℂ) * g x ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, rfl⟩ := hg
      rw [show (fun x => (f x : ℂ) * B a x) = fun x => χ a x * (f x : ℂ) from
        funext fun x => by rw [hBx, mul_comm]]
      exact h a
    | zero =>
      show ∫ x, (f x : ℂ) * 0 ∂μ = 0
      simp
    | add g g' _ _ h1 h2 =>
      show ∫ x, (f x : ℂ) * (g x + g' x) ∂μ = 0
      simp_rw [mul_add]
      rw [integral_add (integrable_mul_bcf μ g (φ := fun x => (f x : ℂ)) hi.ofReal)
        (integrable_mul_bcf μ g' (φ := fun x => (f x : ℂ)) hi.ofReal), h1, h2, add_zero]
    | smul c g _ h1 =>
      show ∫ x, (f x : ℂ) * (c * g x) ∂μ = 0
      rw [show (fun x => (f x : ℂ) * (c * g x)) = fun x => c * ((f x : ℂ) * g x) from
        funext fun x => by ring, integral_const_mul, h1, mul_zero]
  haveI : IsFiniteMeasure (μ.withDensity fun x => ((f x).toNNReal : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  haveI : IsFiniteMeasure (μ.withDensity fun x => ((-f x).toNNReal : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.neg.2
  have hPP := MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish hsepA
    (fun g hg => sub_eq_zero.mp ((hI g).trans (hZ g hg)))
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.real_toNNReal.coe_nnreal_ennreal.aemeasurable
    hf.measurable.neg.real_toNNReal.coe_nnreal_ennreal.aemeasurable).mp hPP
  have h0ae : f =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    have h' : max (f x) 0 = max (-f x) 0 := by
      have := congrArg NNReal.toReal (ENNReal.coe_inj.mp hx)
      rwa [Real.coe_toNNReal', Real.coe_toNNReal'] at this
    rw [Pi.zero_apply]
    rcases lt_trichotomy (f x) 0 with hl | hl | hl
    · rw [max_eq_right hl.le, max_eq_left (by linarith)] at h'; linarith
    · exact hl
    · rw [max_eq_left hl.le, max_eq_right (by linarith)] at h'; linarith
  exact (Continuous.ae_eq_iff_eq (μ := μ) hf continuous_zero).mp h0ae

end GlobalTheory.CharFourierInj

namespace GlobalTheory.CharFourierInj

variable {G A : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A]

/- English proof (translation)
Establish `h1 : ∀ a, Integrable (fun x => χ a x * N x) μ` using `fun a => hi.norm.mono' ((hc a).mul hN).aestronglyMeasurable (Filter.Eventually.of_forall fun x => le_of_eq (by rw [norm_mul, hn, one_mul]))`. Establish `h2 : ∀ a, Integrable (fun x => χ a x * (starRingEnd ℂ) (N x)) μ` using `fun a => hi.norm.mono' ((hc a).mul (Complex.continuous_conj.comp hN)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => le_of_eq (by rw [norm_mul, hn, one_mul, Complex.norm_conj]))`. Establish `hcj : ∀ a, ∫ x, χ a x * (starRingEnd ℂ) (N x) ∂μ = 0`. Introduce `a`. Establish `e : (fun x => χ a x * (starRingEnd ℂ) (N x)) = fun x => (starRingEnd ℂ) (χ (-a) x * N x)`.

Use function extensionality and compare the values at `x`. Rewrite using `[map_mul, exists_integer_complexConj χ ha h0 hn, neg_neg]`. Rewrite using `[e, integral_conj, h (-a), map_zero]`. Establish `hre : ∀ a, ∫ x, χ a x * ((N x).re : ℂ) ∂μ = 0`. Introduce `a`.

Establish `e : (fun x => χ a x * ((N x).re : ℂ)) = fun x => (χ a x * N x + χ a x * (starRingEnd ℂ) (N x)) * (1 / 2)`. Use function extensionality and compare the values at `x`. Rewrite using `[← mul_add, Complex.add_conj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, integral_mul_const, integral_add (h1 a) (h2 a), h a, hcj a]`. Simplify using the standard rewrite rules. Establish `him : ∀ a, ∫ x, χ a x * ((N x).im : ℂ) ∂μ = 0`. Introduce `a`. Establish `e : (fun x => χ a x * ((N x).im : ℂ)) = fun x => (χ a x * N x - χ a x * (starRingEnd ℂ) (N x)) * (-Complex.I / 2)`.

Use function extensionality and compare the values at `x`. Rewrite using `[← mul_sub, Complex.sub_conj]`. Use `push_cast`. Take the linear combination `(χ a x * ((N x).im : ℂ)) * Complex.I_sq`. Rewrite using `[e, integral_mul_const, integral_sub (h1 a) (h2 a), h a, hcj a]`.

Simplify using the standard rewrite rules. Establish `hr` using `real_eq_zero χ hc hx ha h0 hn hsep μ (fun x => (N x).re) (Complex.continuous_re.comp hN) hi.re hre`. Establish `hm` using `real_eq_zero χ hc hx ha h0 hn hsep μ (fun x => (N x).im) (Complex.continuous_im.comp hN) hi.im him`. Use function extensionality and compare the values at `x`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `using congrFun hr x`. Simplify using `using congrFun hm x`.
-/
theorem eq_zero (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a)) (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y)
    (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1) (hn : ∀ a x, ‖χ a x‖ = 1)
    (hsep : ∀ x, (∀ a, χ a x = 1) → x = 0) (μ : Measure G) [μ.IsAddHaarMeasure] (N : G → ℂ) (hN : Continuous N)
    (hi : Integrable N μ) (h : ∀ a, ∫ x, χ a x * N x ∂μ = 0) : N = 0 := by
  have h1 : ∀ a, Integrable (fun x => χ a x * N x) μ := fun a =>
    hi.norm.mono' ((hc a).mul hN).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (by rw [norm_mul, hn, one_mul]))
  have h2 : ∀ a, Integrable (fun x => χ a x * (starRingEnd ℂ) (N x)) μ := fun a =>
    hi.norm.mono' ((hc a).mul (Complex.continuous_conj.comp hN)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (by rw [norm_mul, hn, one_mul, Complex.norm_conj]))
  have hcj : ∀ a, ∫ x, χ a x * (starRingEnd ℂ) (N x) ∂μ = 0 := by
    intro a
    have e : (fun x => χ a x * (starRingEnd ℂ) (N x)) = fun x => (starRingEnd ℂ) (χ (-a) x * N x) := by
      funext x; rw [map_mul, exists_integer_complexConj χ ha h0 hn, neg_neg]
    rw [e, integral_conj, h (-a), map_zero]
  have hre : ∀ a, ∫ x, χ a x * ((N x).re : ℂ) ∂μ = 0 := by
    intro a
    have e : (fun x => χ a x * ((N x).re : ℂ)) =
        fun x => (χ a x * N x + χ a x * (starRingEnd ℂ) (N x)) * (1 / 2) := by
      funext x; rw [← mul_add, Complex.add_conj]; push_cast; ring
    rw [e, integral_mul_const, integral_add (h1 a) (h2 a), h a, hcj a]; simp
  have him : ∀ a, ∫ x, χ a x * ((N x).im : ℂ) ∂μ = 0 := by
    intro a
    have e : (fun x => χ a x * ((N x).im : ℂ)) =
        fun x => (χ a x * N x - χ a x * (starRingEnd ℂ) (N x)) * (-Complex.I / 2) := by
      funext x; rw [← mul_sub, Complex.sub_conj]; push_cast
      linear_combination (χ a x * ((N x).im : ℂ)) * Complex.I_sq
    rw [e, integral_mul_const, integral_sub (h1 a) (h2 a), h a, hcj a]; simp
  have hr := real_eq_zero χ hc hx ha h0 hn hsep μ (fun x => (N x).re) (Complex.continuous_re.comp hN) hi.re hre
  have hm := real_eq_zero χ hc hx ha h0 hn hsep μ (fun x => (N x).im) (Complex.continuous_im.comp hN) hi.im him
  funext x
  apply Complex.ext
  · simpa using congrFun hr x
  · simpa using congrFun hm x

end GlobalTheory.CharFourierInj

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicMatFourier

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Establish `hS0 : 0 < (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.spaceThree D).rank`. Use `(GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isIsoSplit_three D).rank` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨S, hS⟩ : ∃ S : HSp D, 0 < S.rank` from `⟨_, hS0⟩`. Establish `hx` using `(GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S S (Matrix.of fun _ _ => z)).mp (by`.

Introduce `γ _`. Use `h (incA D D.host.xi0 * ∑ a, ∑ b, ∑ c, ∑ d, incA D ((HSpace.gram S)⁻¹ a b) * cA D (γ c b) * incA D (HSpace.gram S c d)) using 2` and compare the differences between its conclusion and the goal. Unfold `symplO hO`. Use `congr 1`. Simplify using `only [Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc])`.

Take `⟨γ, hγ⟩` from `hx`. Establish `hz : incA D (γ ⟨0, hS⟩ ⟨0, hS⟩) = z`. Use `congrArg (fun M : Matrix (Fin S.rank) (Fin S.rank) (AE D) => M ⟨0, hS⟩ ⟨0, hS⟩) hγ` as an intermediate fact. Simplify using `using this`. Assume the negation of the conclusion as `hz0`.

Establish `he : γ ⟨0, hS⟩ ⟨0, hS⟩ ≠ 0`. Introduce `he`. Apply `hz0` to reduce the goal to its premises. Rewrite using `[← hz, he, map_zero]`. Take `⟨x0, hx0⟩` from `hψ.1.2.2.2`.

Use `haveI : Nontrivial (AF D.host.F) := nontrivial_of_ne x0 0 (fun h0 => hx0 (by rw [h0, AddChar.map_zero_eq_one]))`. Establish `hn0 : Module.finrank (AF D.host.F) (AE D) ≠ 0`. Rewrite using `[Module.finrank_baseChange]`. Conclude with `Module.finrank_pos.ne'`. Establish `hn : (Module.finrank (AF D.host.F) (AE D) : D.host.F) ≠ 0` using `Nat.cast_ne_zero.mpr hn0`.

Establish `key` using `h (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (Module.finrank (AF D.host.F) (AE D) : D.host.F)⁻¹ * x0) * incA D (γ ⟨0, hS⟩ ⟨0, hS⟩)⁻¹)`. Rewrite `key` using `[← hz, mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, mul_one, Algebra.trace_algebraMap, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap D.host.F (AF D.host.F)), ← map_mul, mul_inv_cancel₀ hn, map_one, one_mul]`. Conclude with `hx0 key`.
-/
theorem eq_zero_of_psi_trace (hψ : IsStdChar D ψ (-1)) (z : AE D)
    (h : ∀ w : AE D, ψ (Algebra.trace (AF D.host.F) (AE D) (w * z)) = 1) : z = 0 := by
  have hS0 : 0 < (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.spaceThree D).rank := by
    have := (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isIsoSplit_three D).rank; omega
  obtain ⟨S, hS⟩ : ∃ S : HSp D, 0 < S.rank := ⟨_, hS0⟩
  have hx := (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S S (Matrix.of fun _ _ => z)).mp (by
    intro γ _
    convert h (incA D D.host.xi0 * ∑ a, ∑ b, ∑ c, ∑ d, incA D ((HSpace.gram S)⁻¹ a b) * cA D (γ c b) *
      incA D (HSpace.gram S c d)) using 2
    unfold symplO hO
    congr 1
    simp only [Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc])
  obtain ⟨γ, hγ⟩ := hx
  have hz : incA D (γ ⟨0, hS⟩ ⟨0, hS⟩) = z := by
    have := congrArg (fun M : Matrix (Fin S.rank) (Fin S.rank) (AE D) => M ⟨0, hS⟩ ⟨0, hS⟩) hγ
    simpa using this
  by_contra hz0
  have he : γ ⟨0, hS⟩ ⟨0, hS⟩ ≠ 0 := by
    intro he; apply hz0; rw [← hz, he, map_zero]
  obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
  haveI : Nontrivial (AF D.host.F) := nontrivial_of_ne x0 0 (fun h0 => hx0 (by rw [h0, AddChar.map_zero_eq_one]))
  have hn0 : Module.finrank (AF D.host.F) (AE D) ≠ 0 := by
    rw [Module.finrank_baseChange]; exact Module.finrank_pos.ne'
  have hn : (Module.finrank (AF D.host.F) (AE D) : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have key := h (algebraMap (AF D.host.F) (AE D)
    (algebraMap D.host.F (AF D.host.F) (Module.finrank (AF D.host.F) (AE D) : D.host.F)⁻¹ * x0) *
      incA D (γ ⟨0, hS⟩ ⟨0, hS⟩)⁻¹)
  rw [← hz, mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, mul_one, Algebra.trace_algebraMap,
    nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap D.host.F (AF D.host.F)), ← map_mul,
    mul_inv_cancel₀ hn, map_one, one_mul] at key
  exact hx0 key

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.zero_apply]`. Use `eq_zero_of_psi_trace hψ (u i j) fun w => ?_` and prove the remaining obligations. Use `h (Matrix.single j i w)` as an intermediate fact. Rewrite `this` using `[Matrix.trace_single_mul, smul_eq_mul]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_psi_trace_mat (hψ : IsStdChar D ψ (-1)) {m n : ℕ} (u : Mx D m n)
    (h : ∀ y : Mx D n m, ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (y * u))) = 1) : u = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  refine eq_zero_of_psi_trace hψ (u i j) fun w => ?_
  have := h (Matrix.single j i w)
  rwa [Matrix.trace_single_mul, smul_eq_mul] at this

end GlobalTheory.AdelicMatFourier

namespace GlobalTheory.AdelicMatFourier

/- English proof (translation)
Introduce `D ψ hψ m n μ hμ N hN hi h`. Take `⟨h1, h2, h3, h4, -, -⟩` from `GlobalTheory.TowerRestrict.lattice_Mx D m n`. Use `haveI := h1`. Use `haveI := h2`. Use `haveI := h3`.

Use `haveI := h4`. Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D m n) := ⟨rfl⟩`. Establish `htr : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap _`. Use `GlobalTheory.CharFourierInj.eq_zero (A := Mx D n m) (fun y u => ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (y * u)))) ?_ ?_ ?_ ?_ ?_ ?_ μ N hN hi h` and prove the remaining obligations.

Introduce `y`. Conclude with `hψ.1.1.comp (htr.comp (continuous_const.matrix_mul continuous_id).matrix_trace)`. Introduce `y u u'`. Simplify using `only [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]`. Introduce `y y' u`.

Simplify using `only [Matrix.add_mul, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]`. Introduce `u`. Simplify using `only [Matrix.zero_mul, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one]`. Introduce `y u`. Conclude with `hψ.1.2.1 _`.

Introduce `u hu`. Conclude with `eq_zero_of_psi_trace_mat hψ u hu`.
-/
theorem eq_zero_of_fourier_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ N : Mx D m n → ℂ, Continuous N → Integrable N μ → (∀ y : Mx D n m, ∫ u : Mx D m n, ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin n) (Fin m) (AE D)) (u : Matrix (Fin m) (Fin n) (AE D))))) * N u ∂μ = 0) → N = 0 := by
  intro D ψ hψ m n μ hμ N hN hi h
  obtain ⟨h1, h2, h3, h4, -, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  refine GlobalTheory.CharFourierInj.eq_zero (A := Mx D n m)
    (fun y u => ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (y * u)))) ?_ ?_ ?_ ?_ ?_ ?_ μ N hN hi h
  · intro y
    exact hψ.1.1.comp (htr.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · intro y u u'
    simp only [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
  · intro y y' u
    simp only [Matrix.add_mul, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
  · intro u
    simp only [Matrix.zero_mul, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one]
  · intro y u
    exact hψ.1.2.1 _
  · intro u hu
    exact eq_zero_of_psi_trace_mat hψ u hu

end GlobalTheory.AdelicMatFourier

end
