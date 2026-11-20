import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrame
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SkewScaleInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `fun h0 => by simp [h0] at hs`. Establish `hu : (1 : Fv F v) ⊗ₜ[F] s⁻¹ ∈ intLoc F E v`. Rewrite using `[InertChart.mem_intLoc_iff hw h, toCompl_tmul, map_one, one_mul]`. Express the relevant statement in the definitionally equal form `Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) ≤ 1`. Rewrite using `[show Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) = w.valuation E s⁻¹ from HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _, map_inv₀, hs, inv_one]`.

Introduce `y hy`. Use `latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hy` and prove the remaining obligations. Use `(latLoc F L' v).smul_mem ⟨_, hu⟩ (tmul_mem_latLoc ha (hL x hx)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `_ = ((1 : Fv F v) ⊗ₜ[F] s⁻¹) * (a ⊗ₜ[F] (s • x) i)`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel_left₀ hs0]`.
-/
theorem latLoc_le_of_unit {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n : ℕ}
    {L L' : Submodule (𝓞 E) (Fin n → E)} {s : E} (hs : w.valuation E s = 1) (hL : ∀ y ∈ L, s • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hu : (1 : Fv F v) ⊗ₜ[F] s⁻¹ ∈ intLoc F E v := by
    rw [InertChart.mem_intLoc_iff hw h, toCompl_tmul, map_one, one_mul]
    change Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) ≤ 1
    rw [show Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) = w.valuation E s⁻¹ from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _, map_inv₀, hs, inv_one]
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, hu⟩ (tmul_mem_latLoc ha (hL x hx)) using 1
  funext i
  change _ = ((1 : Fv F v) ⊗ₜ[F] s⁻¹) * (a ⊗ₜ[F] (s • x) i)
  rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel_left₀ hs0]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d W r s hX v w hw t ht s₁ s₂ hs₁ hs₂ h₁ h₂`. Establish `h : w.under (𝓞 F) = v` using `GlobalTheory.LFun.under_eq_of_isInertAt hw`. Establish `ht0 : algebraMap F E t ≠ 0` using `(map_ne_zero _).2 ht`. Establish `hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0`. Rewrite using `[Matrix.det_smul, Matrix.det_transpose]`.

Conclude with `mul_ne_zero (pow_ne_zero _ ht0) (GlobalTheory.SkewFrameInert.det_ne_zero hX)`. Establish `hform : ∀ (c : E) (y x : Fin d → E), form σ W.J (c • y) x = c * form σ W.J y x`. Introduce `c y x`. Simplify using `[form, smul_dotProduct]`. Unfold `IsSelfDualAt`.

Rewrite using `[← SelfDual.latLoc_dualGlob hdet hX.lat]`. Use `le_antisymm (latLoc_le_of_unit hw h hs₁ fun y hy x hx => ?_) (latLoc_le_of_unit hw h hs₂ fun y hy => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.SkewFrameInert.hE_smul_transpose, hform, show algebraMap F E t * (s₁ * form σ W.J y x) = s₁ * algebraMap F E t * form σ W.J y x by ring]`. Conclude with `h₁ _ ((hX.dual y).1 hy x hx)`. Use `(hX.dual (s₂ • y)).2 fun x hx o => ?_` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hy x hx`. Rewrite `hc` using `[GlobalTheory.SkewFrameInert.hE_smul_transpose]`. Establish `e : (o : E) * form σ W.J (s₂ • y) x = ((o * c : 𝓞 E) : E) * (s₂ * (algebraMap F E t)⁻¹)`. Establish `hoc : ((o * c : 𝓞 E) : E) = (o : E) * (c : E)` using `map_mul (algebraMap (𝓞 E) E) o c`. Establish `hc' : (c : E) = algebraMap F E t * form σ W.J y x` using `hc`.

Rewrite using `[hform, hoc, hc']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `h₂ (o * c)`.
-/
theorem isSelfDualAt_smul_transpose : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
    ∀ {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
    ∀ (t : F), t ≠ 0 → ∀ (s₁ s₂ : E), w.valuation E s₁ = 1 → w.valuation E s₂ = 1 →
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) →
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) →
    GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hX v w hw t ht s₁ s₂ hs₁ hs₂ h₁ h₂
  have h : w.under (𝓞 F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have ht0 : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ht0) (GlobalTheory.SkewFrameInert.det_ne_zero hX)
  have hform : ∀ (c : E) (y x : Fin d → E), form σ W.J (c • y) x = c * form σ W.J y x := by
    intro c y x
    simp [form, smul_dotProduct]
  unfold IsSelfDualAt
  rw [← SelfDual.latLoc_dualGlob hdet hX.lat]
  refine le_antisymm (latLoc_le_of_unit hw h hs₁ fun y hy x hx => ?_) (latLoc_le_of_unit hw h hs₂ fun y hy => ?_)
  · rw [GlobalTheory.SkewFrameInert.hE_smul_transpose, hform,
      show algebraMap F E t * (s₁ * form σ W.J y x) = s₁ * algebraMap F E t * form σ W.J y x by ring]
    exact h₁ _ ((hX.dual y).1 hy x hx)
  · refine (hX.dual (s₂ • y)).2 fun x hx o => ?_
    obtain ⟨c, hc⟩ := hy x hx
    rw [GlobalTheory.SkewFrameInert.hE_smul_transpose] at hc
    have e : (o : E) * form σ W.J (s₂ • y) x = ((o * c : 𝓞 E) : E) * (s₂ * (algebraMap F E t)⁻¹) := by
      have hoc : ((o * c : 𝓞 E) : E) = (o : E) * (c : E) := map_mul (algebraMap (𝓞 E) E) o c
      have hc' : (c : E) = algebraMap F E t * form σ W.J y x := hc
      rw [hform, hoc, hc']
      field_simp
    rw [e]
    exact h₂ (o * c)

end GlobalTheory.SkewScaleInert
