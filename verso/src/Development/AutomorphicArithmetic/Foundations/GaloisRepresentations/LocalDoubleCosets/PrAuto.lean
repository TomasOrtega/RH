import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `G _ _ _ _ _ _ B hB _ _ μ _ χ s p hp hs hper hsB hχ`. Establish `hit : ∀ n (b : G), b ∈ B → s^[n] b ∈ B`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro b hb`.

Simplify using `using hb`. Consider the case `succ n ih`. Introduce `b hb`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hsB _ (ih b hb)`.

Establish `hleft : ∀ g, s^[p - 1] (s g) = g`. Introduce `g`. Rewrite using `[← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]`. Conclude with `hper g`. Establish `hright : ∀ g, s (s^[p - 1] g) = g`.

Introduce `g`. Rewrite using `[← Function.iterate_succ_apply' s, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]`. Conclude with `hper g`. Set `σ : B ≃ₜ* B` to `{ toFun := fun b => ⟨s b, hsB _ b.2⟩ invFun := fun b => ⟨s^[p - 1] b, hit _ _ b.2⟩ left_inv := fun b => Subtype.ext (hleft b) right_inv := fun b => Subtype.ext (hright b) map_mul' := fun a b => Subtype.ext (map_mul s (a : G) (b : G)) continuous_toFun := (hs.comp continuous_subtyp …`. Use `haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : SecondCountableTopology B := inferInstanceAs (SecondCountableTopology {x // x ∈ (B : Set G)})`. Use `haveI hν : (Measure.map σ μ).IsHaarMeasure := σ.isHaarMeasure_map μ`. Establish `heq` using `Measure.isMulLeftInvariant_eq_smul (Measure.map σ μ) μ`. Use `⟨Measure.haarScalarFactor (Measure.map σ μ) μ, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, fun f g => ?_⟩` and prove the remaining obligations. Establish `hint : ∀ b : B, (χ b : ℂ) * (f ∘ s) ((b : G)⁻¹ * g) = (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g)`.

Introduce `b`. Rewrite using `[hχ b (σ b) rfl]`. Simplify using `[σ, map_mul, map_inv]`. Establish `hm : ∫ c, (χ c : ℂ) * f ((c : G)⁻¹ * s g) ∂(Measure.map σ μ) = ∫ b, (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) ∂μ` using `integral_map_equiv σ.toHomeomorph.toMeasurableEquiv (fun c : B => (χ c : ℂ) * f ((c : G)⁻¹ * s g))`. Unfold `pr`.

Repeatedly rewrite using `[hint]`. Rewrite using `[← hm]`. Use `conv_lhs => rw [heq]`. Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.
-/
theorem UpperTheory.Gal.LocD.prAuto :
    PrAuto := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ s p hp hs hper hsB hχ
  have hit : ∀ n (b : G), b ∈ B → s^[n] b ∈ B := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      rw [Function.iterate_succ_apply']
      exact hsB _ (ih b hb)
  have hleft : ∀ g, s^[p - 1] (s g) = g := by
    intro g
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  have hright : ∀ g, s (s^[p - 1] g) = g := by
    intro g
    rw [← Function.iterate_succ_apply' s, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  let σ : B ≃ₜ* B :=
    { toFun := fun b => ⟨s b, hsB _ b.2⟩
      invFun := fun b => ⟨s^[p - 1] b, hit _ _ b.2⟩
      left_inv := fun b => Subtype.ext (hleft b)
      right_inv := fun b => Subtype.ext (hright b)
      map_mul' := fun a b => Subtype.ext (map_mul s (a : G) (b : G))
      continuous_toFun := (hs.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((hs.iterate _).comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B :=
    inferInstanceAs (SecondCountableTopology {x // x ∈ (B : Set G)})
  haveI hν : (Measure.map σ μ).IsHaarMeasure := σ.isHaarMeasure_map μ
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map σ μ) μ
  refine ⟨Measure.haarScalarFactor (Measure.map σ μ) μ,
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, fun f g => ?_⟩
  have hint : ∀ b : B, (χ b : ℂ) * (f ∘ s) ((b : G)⁻¹ * g) =
      (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) := by
    intro b
    rw [hχ b (σ b) rfl]
    simp [σ, map_mul, map_inv]
  have hm : ∫ c, (χ c : ℂ) * f ((c : G)⁻¹ * s g) ∂(Measure.map σ μ) =
      ∫ b, (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) ∂μ :=
    integral_map_equiv σ.toHomeomorph.toMeasurableEquiv (fun c : B => (χ c : ℂ) * f ((c : G)⁻¹ * s g))
  unfold pr
  simp_rw [hint]
  rw [← hm]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
