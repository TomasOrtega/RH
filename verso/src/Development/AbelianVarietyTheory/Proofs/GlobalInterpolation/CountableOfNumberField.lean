import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.SWQ

/- English proof (translation)
The claim follows from `Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm`.
-/
theorem countable_of_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

/- English proof (translation)
Use extensionality with `S hS`. Rewrite using `[Measure.map_apply (measurable_const_smul w) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul, distribHaarChar_mul]`.
-/
theorem map_unit_mul_eq (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)) [ν.IsAddHaarMeasure]
    (w : (AF F)ˣ) : ν.map (fun x => w • x) = (distribHaarChar (AF F) w⁻¹ : ℝ≥0∞) • ν := by
  ext S hS
  rw [Measure.map_apply (measurable_const_smul w) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
    distribHaarChar_mul]

/- English proof (translation)
Introduce `F _ _ _ ν hν t ht`. Take `⟨hH, D, _, hD, hD1⟩` from `hν`. Use `haveI := hH`. Use `haveI := countable_of_numberField F`. Use `set K := (algebraMap F (AF F)).range.toAddSubgroup with hK`.

Use `haveI : Countable K := by`. Use `Function.Surjective.countable (f := fun r : F => (⟨algebraMap F (AF F) r, ⟨r, rfl⟩⟩ : K)) ?_` and prove the remaining obligations. Introduce and unpack `⟨x, ⟨r, rfl⟩⟩`. Conclude with `⟨r, rfl⟩`. Establish `htu : IsUnit (algebraMap F (AF F) t)` using `(isUnit_iff_ne_zero.mpr ht).map _`.

Use `set u : (AF F)ˣ := htu.unit with hu`. Establish `hmul : (fun x : AF F => (algebraMap F (AF F) t) * x) = fun x => u • x`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[hmul]`.

Set `e : K ≃ K` to `{ toFun := fun g => ⟨algebraMap F (AF F) t⁻¹ * g, by`. Take `⟨r, hr⟩` from `g.2; exact ⟨t⁻¹ * r, by rw [map_mul, hr]⟩⟩`. Use `invFun := fun g => ⟨algebraMap F (AF F) t * g, by`. Take `⟨r, hr⟩` from `g.2; exact ⟨t * r, by rw [map_mul, hr]⟩⟩`. Use `left_inv := fun g => by ext; simp only; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]`.

Use `right_inv := fun g => by ext; simp only; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] }`. Establish `hqmp : Measure.QuasiMeasurePreserving (MulAction.toPerm u).symm ν ν`. Use `⟨measurable_const_smul u⁻¹, ?_⟩` and prove the remaining obligations. Establish `: ⇑(MulAction.toPerm u).symm = fun x : AF F => u⁻¹ • x` using `rfl`. Rewrite using `[this, map_unit_mul_eq F ν u⁻¹]`.

Conclude with `Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _`. Establish `hD' : IsAddFundamentalDomain K (MulAction.toPerm u '' D) ν`. Use `hD.image_of_equiv (MulAction.toPerm u) hqmp e ?_` and prove the remaining obligations. Introduce `g x`. Express the relevant statement in the definitionally equal form `u • ((e g : AF F) + x) = (g : AF F) + u • x`.

Express the relevant statement in the definitionally equal form `algebraMap F (AF F) t * (algebraMap F (AF F) t⁻¹ * (g : AF F) + x) = (g : AF F) + algebraMap F (AF F) t * x`. Rewrite using `[mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]`. Establish `himg : (MulAction.toPerm u '' D) = u • D` using `rfl`. Establish `h1 : ν (u • D) = 1` using `by rw [← himg, hD'.measure_eq hD, hD1]`. Establish `hchar : distribHaarChar (AF F) u = 1`.

Use `distribHaarChar_mul ν u D` as an intermediate fact. Rewrite `this` using `[h1, hD1, mul_one]`. Conclude with `this` after adjusting the coercions. Rewrite using `[map_unit_mul_eq F ν u, map_inv, hchar, inv_one, ENNReal.coe_one, one_smul]`.
-/
theorem modrat_main : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν →
    ∀ t : F, t ≠ 0 → ν.map (fun x => (algebraMap F (AF F) t) * x) = ν := by
  intro F _ _ _ ν hν t ht
  obtain ⟨hH, D, _, hD, hD1⟩ := hν
  haveI := hH
  haveI := countable_of_numberField F
  set K := (algebraMap F (AF F)).range.toAddSubgroup with hK
  haveI : Countable K := by
    refine Function.Surjective.countable (f := fun r : F => (⟨algebraMap F (AF F) r, ⟨r, rfl⟩⟩ : K)) ?_
    rintro ⟨x, ⟨r, rfl⟩⟩
    exact ⟨r, rfl⟩
  have htu : IsUnit (algebraMap F (AF F) t) := (isUnit_iff_ne_zero.mpr ht).map _
  set u : (AF F)ˣ := htu.unit with hu
  have hmul : (fun x : AF F => (algebraMap F (AF F) t) * x) = fun x => u • x := by
    funext x; rfl
  rw [hmul]

  let e : K ≃ K :=
    { toFun := fun g => ⟨algebraMap F (AF F) t⁻¹ * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t⁻¹ * r, by rw [map_mul, hr]⟩⟩
      invFun := fun g => ⟨algebraMap F (AF F) t * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t * r, by rw [map_mul, hr]⟩⟩
      left_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      right_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] }
  have hqmp : Measure.QuasiMeasurePreserving (MulAction.toPerm u).symm ν ν := by
    refine ⟨measurable_const_smul u⁻¹, ?_⟩
    have : ⇑(MulAction.toPerm u).symm = fun x : AF F => u⁻¹ • x := rfl
    rw [this, map_unit_mul_eq F ν u⁻¹]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
  have hD' : IsAddFundamentalDomain K (MulAction.toPerm u '' D) ν := by
    refine hD.image_of_equiv (MulAction.toPerm u) hqmp e ?_
    intro g x
    change u • ((e g : AF F) + x) = (g : AF F) + u • x
    change algebraMap F (AF F) t * (algebraMap F (AF F) t⁻¹ * (g : AF F) + x) = (g : AF F) + algebraMap F (AF F) t * x
    rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  have himg : (MulAction.toPerm u '' D) = u • D := rfl
  have h1 : ν (u • D) = 1 := by rw [← himg, hD'.measure_eq hD, hD1]
  have hchar : distribHaarChar (AF F) u = 1 := by
    have := distribHaarChar_mul ν u D
    rw [h1, hD1, mul_one] at this
    exact_mod_cast this
  rw [map_unit_mul_eq F ν u, map_inv, hchar, inv_one, ENNReal.coe_one, one_smul]

end GlobalTheory.SWQ
