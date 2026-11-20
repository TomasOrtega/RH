import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

/- English proof (translation)
Simplify using `[liftM, h]`.
-/
theorem liftM_val_ext {M : IntermediateField ℚ ℂ} {x : ℂ} (h : x ∈ M) : ((liftM M x : M) : ℂ) = x := by
  simp [liftM, h]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[liftM_val_ext (hσ (a * b)), IntermediateField.coe_mul, liftM_val_ext (hσ a), liftM_val_ext (hσ b), map_mul]`.
-/
theorem liftM_mul_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a * b)) = liftM M (σ a) * liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a * b)), IntermediateField.coe_mul, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_mul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[liftM_val_ext (hσ (a + b)), IntermediateField.coe_add, liftM_val_ext (hσ a), liftM_val_ext (hσ b), map_add]`.
-/
theorem liftM_add_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a + b)) = liftM M (σ a) + liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a + b)), IntermediateField.coe_add, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_add]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[map_one, liftM_val_ext (one_mem M), IntermediateField.coe_one]`.
-/
theorem liftM_one_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) :
    liftM M (σ 1) = 1 := by
  apply Subtype.ext
  rw [map_one, liftM_val_ext (one_mem M), IntermediateField.coe_one]

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (σ (algebraMap (𝓞 E) E e))` using `(RingOfIntegers.isIntegral_coe e).map σ.toIntAlgHom`. Establish `hx : IsIntegral ℤ (liftM M (σ (algebraMap (𝓞 E) E e)))`. Rewrite using `[← isIntegral_algHom_iff (algebraMap M ℂ).toIntAlgHom (algebraMap M ℂ).injective]`. Express the relevant statement in the definitionally equal form `IsIntegral ℤ ((liftM M (σ (algebraMap (𝓞 E) E e)) : M) : ℂ)`. Rewrite using `[liftM_val_ext (hσ _)]` and apply the resulting hypothesis.

Conclude with `⟨⟨_, hx⟩, rfl⟩`.
-/
theorem liftM_int_ext {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (e : 𝓞 E) :
    liftM M (σ (algebraMap (𝓞 E) E e)) ∈ (algebraMap (𝓞 M) M).range := by
  have h1 : IsIntegral ℤ (σ (algebraMap (𝓞 E) E e)) :=
    (RingOfIntegers.isIntegral_coe e).map σ.toIntAlgHom
  have hx : IsIntegral ℤ (liftM M (σ (algebraMap (𝓞 E) E e))) := by
    rw [← isIntegral_algHom_iff (algebraMap M ℂ).toIntAlgHom (algebraMap M ℂ).injective]
    change IsIntegral ℤ ((liftM M (σ (algebraMap (𝓞 E) E e)) : M) : ℂ)
    rwa [liftM_val_ext (hσ _)]
  exact ⟨⟨_, hx⟩, rfl⟩

/- English proof (translation)
Establish `hJJ : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E)`. Rewrite using `[← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Establish `hint : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), liftM M (σ z) ∈ (algebraMap (𝓞 M) M).range`. Introduce `z hz`.

Rewrite `hz` using `[← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]`. Take `⟨y, rfl⟩` from `Submodule.mem_one.1 hz`. Conclude with `liftM_int_ext M σ hσ y`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Introduce `b hb`. Rewrite using `[← liftM_mul_ext M σ hσ]`.

Conclude with `hint _ (Submodule.mul_mem_mul ha hb)`. Consider the case `zero`. Introduce `b _`. Rewrite using `[zero_mul]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz`. Introduce `b hb`. Rewrite using `[add_mul]`. Conclude with `add_mem (hy b hb) (hz b hb)`. Consider the case `smul r y _ hy`.

Introduce `b hb`. Rewrite using `[smul_mul_assoc, Algebra.smul_def]`. Conclude with `mul_mem (RingHom.mem_range_self _ r) (hy b hb)`. Introduce `hx`. Establish `key : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), x * liftM M (σ z) ∈ imI M σ J`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.mul_induction_on' with`. Consider the case `mem_mul_mem a ha b hb`. Take `⟨r, hr⟩` from `hx b hb`. Rewrite using `[liftM_mul_ext M σ hσ, mul_comm (liftM M (σ a)), ← mul_assoc, ← hr, ← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨a, ha, rfl⟩)`. Consider the case `add y _ z _ hy hz`. Rewrite using `[liftM_add_ext M σ hσ, mul_add]`. Conclude with `add_mem hy hz`. Use `key 1 hJJ` as an intermediate fact.

Rewrite `this` using `[liftM_one_ext, mul_one]`. Then use the resulting hypothesis.
-/
theorem mem_imI_iff {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (x : M) :
    x ∈ imI M σ J ↔
      ∀ b ∈ ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), x * liftM M (σ b) ∈ (algebraMap (𝓞 M) M).range := by
  have hJJ : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have hint : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E), liftM M (σ z) ∈ (algebraMap (𝓞 M) M).range := by
    intro z hz
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one] at hz
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hz
    exact liftM_int_ext M σ hσ y
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro b hb
      rw [← liftM_mul_ext M σ hσ]
      exact hint _ (Submodule.mul_mem_mul ha hb)
    | zero =>
      intro b _
      rw [zero_mul]
      exact zero_mem _
    | add y z _ _ hy hz =>
      intro b hb
      rw [add_mul]
      exact add_mem (hy b hb) (hz b hb)
    | smul r y _ hy =>
      intro b hb
      rw [smul_mul_assoc, Algebra.smul_def]
      exact mul_mem (RingHom.mem_range_self _ r) (hy b hb)
  · intro hx
    have key : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
        Submodule (𝓞 E) E), x * liftM M (σ z) ∈ imI M σ J := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
        obtain ⟨r, hr⟩ := hx b hb
        rw [liftM_mul_ext M σ hσ, mul_comm (liftM M (σ a)), ← mul_assoc, ← hr, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a, ha, rfl⟩)
      | add y _ z _ hy hz =>
        rw [liftM_add_ext M σ hσ, mul_add]
        exact add_mem hy hz
    have := key 1 hJJ
    rwa [liftM_one_ext, mul_one] at this

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
