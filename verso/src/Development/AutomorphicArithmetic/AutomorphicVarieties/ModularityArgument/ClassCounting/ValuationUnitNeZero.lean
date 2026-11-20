import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.V.ZK

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_actP_asIdeal_iff_mapRingEquiv_symm_mem (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F) :
    y ∈ (actP σ P).asIdeal ↔ (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y ∈ P.asIdeal :=
  Iff.rfl

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun y => ?_)` and prove the remaining obligations. Rewrite using `[mem_actP_asIdeal_iff_mapRingEquiv_symm_mem]`. Conclude with `Iff.of_eq (congrArg (· ∈ P.asIdeal) (Subtype.ext rfl))`.
-/
theorem polyAction_one₂ (P : HeightOneSpectrum (𝓞 F)) : actP (1 : F ≃ₐ[L] F) P = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  rw [mem_actP_asIdeal_iff_mapRingEquiv_symm_mem]
  exact Iff.of_eq (congrArg (· ∈ P.asIdeal) (Subtype.ext rfl))

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun y => ?_)` and prove the remaining obligations. Rewrite using `[mem_actP_asIdeal_iff_mapRingEquiv_symm_mem, mem_actP_asIdeal_iff_mapRingEquiv_symm_mem, mem_actP_asIdeal_iff_mapRingEquiv_symm_mem]`. Conclude with `Iff.of_eq (congrArg (· ∈ P.asIdeal) (Subtype.ext rfl))`.
-/
theorem polyAction_mul (σ τ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) : actP (σ * τ) P = actP σ (actP τ P) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  rw [mem_actP_asIdeal_iff_mapRingEquiv_symm_mem, mem_actP_asIdeal_iff_mapRingEquiv_symm_mem, mem_actP_asIdeal_iff_mapRingEquiv_symm_mem]
  exact Iff.of_eq (congrArg (· ∈ P.asIdeal) (Subtype.ext rfl))

/- English proof (translation)
Rewrite using `[← polyAction_mul, inv_mul_cancel, polyAction_one₂]`.
-/
theorem actP_inv_actP (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) : actP σ⁻¹ (actP σ P) = P := by
  rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]

/- English proof (translation)
Rewrite using `[← polyAction_mul, mul_inv_cancel, polyAction_one₂]`.
-/
theorem actP_actP_inv (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) : actP σ (actP σ⁻¹ P) = P := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

def actPerm : (F ≃ₐ[L] F) →* Equiv.Perm (HeightOneSpectrum (𝓞 F)) where
  toFun σ := ⟨actP σ, actP σ⁻¹, actP_inv_actP σ, actP_actP_inv σ⟩
  map_one' := Equiv.ext polyAction_one₂
  map_mul' σ τ := Equiv.ext (polyAction_mul σ τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem actPerm_apply (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) : actPerm σ P = actP σ P := rfl

/- English proof (translation)
The claim follows from `(Valuation.ne_zero_iff _).2 α.ne_zero`.
-/
theorem valuation_unit_ne_zero (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) : P.valuation F (α : F) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 α.ne_zero

/- English proof (translation)
Simplify using `only [ordP, neg_neg]`. Conclude with `(WithZero.exp_log (valuation_unit_ne_zero P α)).symm`.
-/
theorem valuation_eq_exp_ordP (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    P.valuation F (α : F) = WithZero.exp (-ordP P α) := by
  simp only [ordP, neg_neg]
  exact (WithZero.exp_log (valuation_unit_ne_zero P α)).symm

/- English proof (translation)
Simplify using `[ordP]`.
-/
theorem ordP_one (P : HeightOneSpectrum (𝓞 F)) : ordP P (1 : Fˣ) = 0 := by
  simp [ordP]

/- English proof (translation)
Simplify using `only [ordP, Units.val_mul, map_mul]`. Rewrite using `[WithZero.log_mul (valuation_unit_ne_zero P α) (valuation_unit_ne_zero P β), neg_add]`.
-/
theorem ordP_mul (P : HeightOneSpectrum (𝓞 F)) (α β : Fˣ) : ordP P (α * β) = ordP P α + ordP P β := by
  simp only [ordP, Units.val_mul, map_mul]
  rw [WithZero.log_mul (valuation_unit_ne_zero P α) (valuation_unit_ne_zero P β), neg_add]

def ordHom (P : HeightOneSpectrum (𝓞 F)) : Additive Fˣ →+ ℤ where
  toFun x := ordP P x.toMul
  map_zero' := ordP_one P
  map_add' x y := ordP_mul P x.toMul y.toMul

/- English proof (translation)
Use `((HeightOneSpectrum.Support.finite (𝓞 F) (α : F)).union (HeightOneSpectrum.Support.finite (𝓞 F) ((α⁻¹ : Fˣ) : F))).subset ?_` and prove the remaining obligations. Introduce `P hP`. Establish `hinv : ordP P α⁻¹ = -ordP P α`. Establish `h` using `ordP_mul P α α⁻¹`. Rewrite `h` using `[mul_inv_cancel, ordP_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hP' : ordP P α ≠ 0` using `hP`. Simplify using `only [Set.mem_union, HeightOneSpectrum.Support, Set.mem_setOf_eq]`. Rewrite using `[valuation_eq_exp_ordP, valuation_eq_exp_ordP, hinv, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordP_finite (α : Fˣ) : {P : HeightOneSpectrum (𝓞 F) | ordP P α ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (α : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((α⁻¹ : Fˣ) : F))).subset ?_
  intro P hP
  have hinv : ordP P α⁻¹ = -ordP P α := by
    have h := ordP_mul P α α⁻¹
    rw [mul_inv_cancel, ordP_one] at h
    omega
  have hP' : ordP P α ≠ 0 := hP
  simp only [Set.mem_union, HeightOneSpectrum.Support, Set.mem_setOf_eq]
  rw [valuation_eq_exp_ordP, valuation_eq_exp_ordP, hinv, ← WithZero.exp_zero,
    WithZero.exp_lt_exp, WithZero.exp_lt_exp]
  omega

/- English proof (translation)
The claim follows from `ordP_finite α`.
-/
theorem ordP_finite_support (α : Fˣ) :
    (Function.support fun P : HeightOneSpectrum (𝓞 F) => ordP P α).Finite := ordP_finite α

def divHom (F : Type) [Field F] [NumberField F] : Additive Fˣ →+ (HeightOneSpectrum (𝓞 F) →₀ ℤ) where
  toFun x := Finsupp.ofSupportFinite (fun P => ordP P x.toMul) (ordP_finite_support _)
  map_zero' := Finsupp.ext fun P => ordP_one P
  map_add' x y := Finsupp.ext fun P => ordP_mul P x.toMul y.toMul

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem divHom_apply (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)) :
    divHom F (Additive.ofMul α) P = ordP P α := rfl

end UpperTheory.V.ZK

end
