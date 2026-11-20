import Mathlib
import GroundTheory.PAdicHodge.GaloisOnCp
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module IntermediateField

noncomputable section

section General

variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

def normTraceF (y : Ω) : F := -(minpoly F y).nextCoeff / ((minpoly F y).natDegree : F)

def normTrace (y : Ω) : Ω := algebraMap F Ω (normTraceF F y)

@[simp]
/- English proof (translation)
Rewrite using `[normTraceF, minpoly.eq_X_sub_C, nextCoeff_X_sub_C, natDegree_X_sub_C]`. Simplify using the standard rewrite rules. Use the proof step `@[simp]`.
-/
theorem normTraceF_algebraMap (a : F) : normTraceF F (algebraMap F Ω a) = a := by
  rw [normTraceF, minpoly.eq_X_sub_C, nextCoeff_X_sub_C, natDegree_X_sub_C]
  simp

@[simp]
/- English proof (translation)
Rewrite using `[normTrace, normTraceF_algebraMap]`.
-/
theorem normTrace_algebraMap (a : F) : normTrace F (algebraMap F Ω a) = algebraMap F Ω a := by
  rw [normTrace, normTraceF_algebraMap]

/- English proof (translation)
Establish `hy : IsIntegral F y` using `IsIntegral.of_finite F y`. Use `haveI : FiniteDimensional F⟮y⟯ L := FiniteDimensional.right F F⟮y⟯ L`. Rewrite using `[normTraceF, minpoly.algebraMap_eq (algebraMap L Ω).injective, trace_eq_finrank_mul_minpoly_nextCoeff, ← Module.finrank_mul_finrank F F⟮y⟯ L, IntermediateField.adjoin.finrank hy]`. Establish `h1 : ((minpoly F y).natDegree : F) ≠ 0` using `Nat.cast_ne_zero.2 (minpoly.natDegree_pos hy).ne'`. Establish `h2 : (finrank F⟮y⟯ L : F) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem normTraceF_eq_trace_div [CharZero F] (L : Type*) [Field L] [Algebra F L] [Algebra L Ω]
    [IsScalarTower F L Ω] [FiniteDimensional F L] (y : L) :
    normTraceF F (algebraMap L Ω y) = Algebra.trace F L y / (finrank F L : F) := by
  have hy : IsIntegral F y := IsIntegral.of_finite F y
  haveI : FiniteDimensional F⟮y⟯ L := FiniteDimensional.right F F⟮y⟯ L
  rw [normTraceF, minpoly.algebraMap_eq (algebraMap L Ω).injective,
    trace_eq_finrank_mul_minpoly_nextCoeff, ← Module.finrank_mul_finrank F F⟮y⟯ L,
    IntermediateField.adjoin.finrank hy]
  have h1 : ((minpoly F y).natDegree : F) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos hy).ne'
  have h2 : (finrank F⟮y⟯ L : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast
  field_simp

variable [CharZero F] [Algebra.IsIntegral F Ω]

/- English proof (translation)
Use `haveI := IntermediateField.finiteDimensional_adjoin_pair (Algebra.IsIntegral.isIntegral (R := F) y) (Algebra.IsIntegral.isIntegral (R := F) z)`. Establish `hy : y ∈ F⟮y, z⟯` using `subset_adjoin F _ (by simp)`. Establish `hz : z ∈ F⟮y, z⟯` using `subset_adjoin F _ (by simp)`. Establish `e` using `normTraceF_eq_trace_div F (Ω := Ω) F⟮y, z⟯`. Establish `h1` using `e ⟨y, hy⟩`.

Establish `h2` using `e ⟨z, hz⟩`. Establish `h3` using `e (⟨y, hy⟩ + ⟨z, hz⟩)`. Rewrite `h3` using `[LinearMap.map_add, add_div, ← h1, ← h2]`. Conclude with `h3`.
-/
theorem normTraceF_add (y z : Ω) : normTraceF F (y + z) = normTraceF F y + normTraceF F z := by
  haveI := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral (R := F) y) (Algebra.IsIntegral.isIntegral (R := F) z)
  have hy : y ∈ F⟮y, z⟯ := subset_adjoin F _ (by simp)
  have hz : z ∈ F⟮y, z⟯ := subset_adjoin F _ (by simp)
  have e := normTraceF_eq_trace_div F (Ω := Ω) F⟮y, z⟯
  have h1 := e ⟨y, hy⟩
  have h2 := e ⟨z, hz⟩
  have h3 := e (⟨y, hy⟩ + ⟨z, hz⟩)
  rw [LinearMap.map_add, add_div, ← h1, ← h2] at h3
  exact h3

/- English proof (translation)
Use `haveI := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) y)`. Establish `e` using `normTraceF_eq_trace_div F (Ω := Ω) F⟮y⟯`. Establish `h1` using `e (AdjoinSimple.gen F y)`. Establish `h2` using `e (a • AdjoinSimple.gen F y)`. Rewrite `h2` using `[LinearMap.map_smul, smul_eq_mul, mul_div_assoc, ← h1]`.

Conclude with `h2`.
-/
theorem normTraceF_smul (a : F) (y : Ω) : normTraceF F (a • y) = a * normTraceF F y := by
  haveI := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) y)
  have e := normTraceF_eq_trace_div F (Ω := Ω) F⟮y⟯
  have h1 := e (AdjoinSimple.gen F y)
  have h2 := e (a • AdjoinSimple.gen F y)
  rw [LinearMap.map_smul, smul_eq_mul, mul_div_assoc, ← h1] at h2
  exact h2

def normTraceFₗ : Ω →ₗ[F] F where
  toFun := normTraceF F
  map_add' := normTraceF_add F
  map_smul' := normTraceF_smul F

def normTraceₗ : Ω →ₗ[F] Ω := (Algebra.linearMap F Ω).comp (normTraceFₗ F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem normTraceFₗ_apply (y : Ω) : normTraceFₗ F y = normTraceF F y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem normTraceₗ_apply (y : Ω) : normTraceₗ F y = normTrace F y := rfl

/- English proof (translation)
The claim follows from `map_add (normTraceₗ F) y z`.
-/
theorem normTrace_add (y z : Ω) : normTrace F (y + z) = normTrace F y + normTrace F z :=
  map_add (normTraceₗ F) y z

/- English proof (translation)
The claim follows from `map_sub (normTraceₗ F) y z`.
-/
theorem normTrace_sub (y z : Ω) : normTrace F (y - z) = normTrace F y - normTrace F z :=
  map_sub (normTraceₗ F) y z

/- English proof (translation)
The claim follows from `map_zero (normTraceₗ F)`.
-/
@[simp] theorem normTrace_zero : normTrace F (0 : Ω) = 0 := map_zero (normTraceₗ F)

/- English proof (translation)
The claim follows from `map_smul (normTraceₗ F) a y`.
-/
theorem normTrace_smul (a : F) (y : Ω) : normTrace F (a • y) = a • normTrace F y :=
  map_smul (normTraceₗ F) a y

/- English proof (translation)
The claim follows from `map_sum (normTraceₗ F) f s`.
-/
theorem normTrace_sum {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    normTrace F (∑ i ∈ s, f i) = ∑ i ∈ s, normTrace F (f i) :=
  map_sum (normTraceₗ F) f s

/- English proof (translation)
Rewrite using `[← Algebra.smul_def, normTrace_smul, Algebra.smul_def]`.
-/
theorem normTrace_algebraMap_mul (a : F) (y : Ω) :
    normTrace F (algebraMap F Ω a * y) = algebraMap F Ω a * normTrace F y := by
  rw [← Algebra.smul_def, normTrace_smul, Algebra.smul_def]

/- English proof (translation)
Use `haveI : Algebra.IsIntegral E Ω := Algebra.IsIntegral.tower_top F`. Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective`. Establish `hyE : IsIntegral E y` using `Algebra.IsIntegral.isIntegral y`. Use `haveI : FiniteDimensional E E⟮y⟯ := IntermediateField.adjoin.finiteDimensional hyE`. Use `haveI : FiniteDimensional F E⟮y⟯ := FiniteDimensional.trans F E E⟮y⟯`.

Use `haveI : IsScalarTower F E⟮y⟯ Ω := IsScalarTower.of_algebraMap_eq fun a => by`. Rewrite using `[IsScalarTower.algebraMap_apply F E Ω, IsScalarTower.algebraMap_apply F E E⟮y⟯]`. Both sides reduce to the same expression. Use `set g : E⟮y⟯ := AdjoinSimple.gen E y`. Establish `hE : normTraceF E y = Algebra.trace E E⟮y⟯ g / (finrank E E⟮y⟯ : E)` using `normTraceF_eq_trace_div E (Ω := Ω) E⟮y⟯ g`.

Establish `hFy : normTraceF F y = Algebra.trace F E⟮y⟯ g / (finrank F E⟮y⟯ : F)` using `normTraceF_eq_trace_div F (Ω := Ω) E⟮y⟯ g`. Establish `hF : (finrank E E⟮y⟯ : F) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `hFE : (finrank F E : F) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `key : normTrace E y = ((finrank E E⟮y⟯ : F)⁻¹) • algebraMap E Ω (Algebra.trace E E⟮y⟯ g)`. Rewrite using `[normTrace, hE, div_eq_inv_mul, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply F E Ω]`.

Use `congr 2`. Simplify using the standard rewrite rules. Establish `hT : normTraceF F (algebraMap E Ω (Algebra.trace E E⟮y⟯ g)) = Algebra.trace F E (Algebra.trace E E⟮y⟯ g) / (finrank F E : F)` using `normTraceF_eq_trace_div F (Ω := Ω) E _`. Rewrite using `[key, normTraceF_smul, hT, hFy, Algebra.trace_trace, ← Module.finrank_mul_finrank F E E⟮y⟯]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem normTraceF_normTrace (E : Type*) [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] [FiniteDimensional F E] (y : Ω) :
    normTraceF F (normTrace E y) = normTraceF F y := by
  haveI : Algebra.IsIntegral E Ω := Algebra.IsIntegral.tower_top F
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hyE : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional E E⟮y⟯ := IntermediateField.adjoin.finiteDimensional hyE
  haveI : FiniteDimensional F E⟮y⟯ := FiniteDimensional.trans F E E⟮y⟯
  haveI : IsScalarTower F E⟮y⟯ Ω := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply F E Ω, IsScalarTower.algebraMap_apply F E E⟮y⟯]; rfl
  set g : E⟮y⟯ := AdjoinSimple.gen E y
  have hE : normTraceF E y = Algebra.trace E E⟮y⟯ g / (finrank E E⟮y⟯ : E) :=
    normTraceF_eq_trace_div E (Ω := Ω) E⟮y⟯ g
  have hFy : normTraceF F y = Algebra.trace F E⟮y⟯ g / (finrank F E⟮y⟯ : F) :=
    normTraceF_eq_trace_div F (Ω := Ω) E⟮y⟯ g
  have hF : (finrank E E⟮y⟯ : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hFE : (finrank F E : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have key : normTrace E y =
      ((finrank E E⟮y⟯ : F)⁻¹) • algebraMap E Ω (Algebra.trace E E⟮y⟯ g) := by
    rw [normTrace, hE, div_eq_inv_mul, map_mul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply F E Ω]
    congr 2
    simp
  have hT : normTraceF F (algebraMap E Ω (Algebra.trace E E⟮y⟯ g)) =
      Algebra.trace F E (Algebra.trace E E⟮y⟯ g) / (finrank F E : F) :=
    normTraceF_eq_trace_div F (Ω := Ω) E _
  rw [key, normTraceF_smul, hT, hFy, Algebra.trace_trace, ← Module.finrank_mul_finrank F E E⟮y⟯]
  push_cast
  field_simp

/- English proof (translation)
Rewrite using `[normTrace, normTraceF_normTrace, normTrace]`.
-/
theorem normTrace_normTrace (E : Type*) [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] [FiniteDimensional F E] (y : Ω) :
    normTrace F (normTrace E y) = normTrace F y := by
  rw [normTrace, normTraceF_normTrace, normTrace]

end General

section Transport

variable {Ω : Type*} [Field Ω]

/- English proof (translation)
Use `symm`. Apply `minpoly.eq_of_irreducible_of_monic` to reduce the goal to its premises. Use `(MulEquiv.irreducible_iff (Polynomial.mapEquiv τ)).2 (minpoly.irreducible hy)` as an intermediate fact. Simplify using `using this`. Establish `hc : (algebraMap F₂ Ω).comp (τ : F₁ →+* F₂) = (σ : Ω →+* Ω).comp (algebraMap F₁ Ω)` using `RingHom.ext h`.

Rewrite using `[aeval_def, eval₂_map, hc, ← RingEquiv.coe_toRingHom, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]`. Conclude with `(minpoly.monic hy).map _`.
-/
theorem minpoly_map_ringEquiv {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (τ : F₁ ≃+* F₂) (σ : Ω ≃+* Ω) (h : ∀ a, algebraMap F₂ Ω (τ a) = σ (algebraMap F₁ Ω a))
    {y : Ω} (hy : IsIntegral F₁ y) :
    minpoly F₂ (σ y) = (minpoly F₁ y).map (τ : F₁ →+* F₂) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · have := (MulEquiv.irreducible_iff (Polynomial.mapEquiv τ)).2 (minpoly.irreducible hy)
    simpa using this
  · have hc : (algebraMap F₂ Ω).comp (τ : F₁ →+* F₂) = (σ : Ω →+* Ω).comp (algebraMap F₁ Ω) :=
      RingHom.ext h
    rw [aeval_def, eval₂_map, hc, ← RingEquiv.coe_toRingHom, ← hom_eval₂, ← aeval_def,
      minpoly.aeval, map_zero]
  · exact (minpoly.monic hy).map _

/- English proof (translation)
Rewrite using `[normTrace, normTraceF, minpoly_map_ringEquiv τ σ h hy, nextCoeff_map τ.injective, natDegree_map_eq_of_injective τ.injective, normTrace, normTraceF, ← h]`. Simplify using `[map_div₀, map_neg, map_natCast]`.
-/
theorem normTrace_map_ringEquiv {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω]
    [Algebra F₂ Ω] (τ : F₁ ≃+* F₂) (σ : Ω ≃+* Ω)
    (h : ∀ a, algebraMap F₂ Ω (τ a) = σ (algebraMap F₁ Ω a)) {y : Ω} (hy : IsIntegral F₁ y) :
    normTrace F₂ (σ y) = σ (normTrace F₁ y) := by
  rw [normTrace, normTraceF, minpoly_map_ringEquiv τ σ h hy, nextCoeff_map τ.injective,
    natDegree_map_eq_of_injective τ.injective, normTrace, normTraceF, ← h]
  simp [map_div₀, map_neg, map_natCast]

/- English proof (translation)
Establish `hy : IsIntegral k y` using `(Algebra.IsIntegral.isIntegral (R := B₀) y).tower_top`. Set `τ : k ≃+* k` to `((k.equivMap (σ : Ω →ₐ[B₀] Ω)).trans (IntermediateField.equivOfEq hk)).toRingEquiv`. Conclude with `normTrace_map_ringEquiv τ σ.toRingEquiv (fun a => rfl) hy`.
-/
theorem normTrace_map_of_map_eq {B₀ : Type*} [Field B₀] [Algebra B₀ Ω] [Algebra.IsIntegral B₀ Ω]
    (k : IntermediateField B₀ Ω) (σ : Ω ≃ₐ[B₀] Ω) (hk : k.map (σ : Ω →ₐ[B₀] Ω) = k) (y : Ω) :
    normTrace k (σ y) = σ (normTrace k y) := by
  have hy : IsIntegral k y := (Algebra.IsIntegral.isIntegral (R := B₀) y).tower_top
  let τ : k ≃+* k := ((k.equivMap (σ : Ω →ₐ[B₀] Ω)).trans (IntermediateField.equivOfEq hk)).toRingEquiv
  exact normTrace_map_ringEquiv τ σ.toRingEquiv (fun a => rfl) hy

end Transport

section Degree

variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]

/- English proof (translation)
Rewrite using `[← relfinrank_eq_finrank_of_le h, ← relfinrank_bot_left, ← relfinrank_bot_left, relfinrank_mul_relfinrank bot_le h]`.
-/
theorem finrank_eq_mul_finrank_extendScalars {k E : IntermediateField B₀ Ω} (h : k ≤ E) :
    finrank B₀ E = finrank B₀ k * finrank k (extendScalars h) := by
  rw [← relfinrank_eq_finrank_of_le h, ← relfinrank_bot_left, ← relfinrank_bot_left,
    relfinrank_mul_relfinrank bot_le h]

/- English proof (translation)
Rewrite using `[finrank_eq_mul_finrank_extendScalars hX, finrank_eq_mul_finrank_extendScalars hY, finrank_eq_mul_finrank_extendScalars (le_sup_of_le_left hX : k ≤ X ⊔ Y), ← extendScalars_sup hX hY]`. Use `IntermediateField.finrank_sup_le (extendScalars hX) (extendScalars hY)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_sup_mul_le {k X Y : IntermediateField B₀ Ω} (hX : k ≤ X) (hY : k ≤ Y) :
    finrank B₀ ↥(X ⊔ Y) * finrank B₀ k ≤ finrank B₀ X * finrank B₀ Y := by
  rw [finrank_eq_mul_finrank_extendScalars hX, finrank_eq_mul_finrank_extendScalars hY,
    finrank_eq_mul_finrank_extendScalars (le_sup_of_le_left hX : k ≤ X ⊔ Y),
    ← extendScalars_sup hX hY]
  have := IntermediateField.finrank_sup_le (extendScalars hX) (extendScalars hY)
  calc finrank B₀ k * finrank k ↥(extendScalars hX ⊔ extendScalars hY) * finrank B₀ k
      = finrank B₀ k * finrank B₀ k * finrank k ↥(extendScalars hX ⊔ extendScalars hY) := by ring
    _ ≤ finrank B₀ k * finrank B₀ k *
        (finrank k (extendScalars hX) * finrank k (extendScalars hY)) := Nat.mul_le_mul_left _ this
    _ = _ := by ring

/- English proof (translation)
Rewrite using `[finrank_eq_mul_finrank_extendScalars (le_sup_left : F ≤ F ⊔ adjoin B₀ {z})]`. Establish `: extendScalars (le_sup_left : F ≤ F ⊔ adjoin B₀ {z}) = adjoin F {z}` using `restrictScalars_injective B₀ (by rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup])`. Rewrite using `[this, IntermediateField.adjoin.finrank hz]`.
-/
theorem finrank_sup_adjoin_simple (F : IntermediateField B₀ Ω) {z : Ω} (hz : IsIntegral F z) :
    finrank B₀ ↥(F ⊔ adjoin B₀ {z}) = finrank B₀ F * (minpoly F z).natDegree := by
  rw [finrank_eq_mul_finrank_extendScalars (le_sup_left : F ≤ F ⊔ adjoin B₀ {z})]
  have : extendScalars (le_sup_left : F ≤ F ⊔ adjoin B₀ {z}) = adjoin F {z} :=
    restrictScalars_injective B₀ (by rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup])
  rw [this, IntermediateField.adjoin.finrank hz]

/- English proof (translation)
The claim follows from `FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion_injective h)`.
-/
theorem finiteDimensional_of_le {k E : IntermediateField B₀ Ω} (h : k ≤ E) [FiniteDimensional B₀ E] :
    FiniteDimensional B₀ k :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

/- English proof (translation)
Use `haveI := finiteDimensional_of_le hA`. Establish `hz0 : IsIntegral B₀ z`. Use `IsIntegral.of_finite B₀ (⟨z, hz⟩ : A)` as an intermediate fact. Conclude with `this.map (IsScalarTower.toAlgHom B₀ A Ω)`. Establish `hzk : IsIntegral k z` using `hz0.tower_top`.

Establish `hzB : IsIntegral B z` using `hz0.tower_top`. Establish `hz' : adjoin B₀ {z} ≤ A`. Rewrite using `[adjoin_le_iff]`. Simplify using `using hz`. Establish `ek` using `finrank_sup_adjoin_simple k hzk`.

Establish `eB` using `finrank_sup_adjoin_simple B hzB`. Establish `c1` using `finrank_sup_mul_le (k := k ⊔ adjoin B₀ {z}) (X := A) (Y := B ⊔ adjoin B₀ {z}) (sup_le hA hz') (sup_le_sup_right hB _)`. Establish `s1 : A ⊔ (B ⊔ adjoin B₀ {z}) = A ⊔ B` using `le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hz'.trans le_sup_left))) (sup_le_sup_left le_sup_left _)`. Rewrite `c1` using `[s1, ek, eB]`. Establish `c2` using `finrank_sup_mul_le (k := k) (X := B) (Y := k ⊔ adjoin B₀ {z}) hB le_sup_left`.

Establish `s2 : B ⊔ (k ⊔ adjoin B₀ {z}) = B ⊔ adjoin B₀ {z}`. Rewrite using `[← sup_assoc, sup_eq_left.2 hB]`. Rewrite `c2` using `[s2, ek, eB]`. Establish `pA : 0 < finrank B₀ A` using `Module.finrank_pos`. Establish `pB : 0 < finrank B₀ B` using `Module.finrank_pos`.

Establish `pk : 0 < finrank B₀ k` using `Module.finrank_pos`. Establish `pAB : 0 < finrank B₀ A * finrank B₀ B` using `Nat.mul_pos pA pB`. Establish `pBk : 0 < finrank B₀ B * finrank B₀ k` using `Nat.mul_pos pB pk`. Apply `le_antisymm` to reduce the goal to its premises. Establish `: finrank B₀ B * finrank B₀ k * (minpoly B z).natDegree ≤ finrank B₀ B * finrank B₀ k * (minpoly k z).natDegree`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.le_of_mul_le_mul_left this pBk`. Establish `: finrank B₀ A * finrank B₀ B * (minpoly k z).natDegree ≤ finrank B₀ A * finrank B₀ B * (minpoly B z).natDegree`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.le_of_mul_le_mul_left this pAB`.
-/
theorem natDegree_minpoly_eq_of_finrank_sup {k A B : IntermediateField B₀ Ω} (hA : k ≤ A)
    (hB : k ≤ B) [FiniteDimensional B₀ A] [FiniteDimensional B₀ B]
    (h : finrank B₀ ↥(A ⊔ B) * finrank B₀ k = finrank B₀ A * finrank B₀ B) {z : Ω} (hz : z ∈ A) :
    (minpoly B z).natDegree = (minpoly k z).natDegree := by
  haveI := finiteDimensional_of_le hA
  have hz0 : IsIntegral B₀ z := by
    have := IsIntegral.of_finite B₀ (⟨z, hz⟩ : A)
    exact this.map (IsScalarTower.toAlgHom B₀ A Ω)
  have hzk : IsIntegral k z := hz0.tower_top
  have hzB : IsIntegral B z := hz0.tower_top
  have hz' : adjoin B₀ {z} ≤ A := by
    rw [adjoin_le_iff]; simpa using hz
  have ek := finrank_sup_adjoin_simple k hzk
  have eB := finrank_sup_adjoin_simple B hzB
  have c1 := finrank_sup_mul_le (k := k ⊔ adjoin B₀ {z}) (X := A) (Y := B ⊔ adjoin B₀ {z})
    (sup_le hA hz') (sup_le_sup_right hB _)
  have s1 : A ⊔ (B ⊔ adjoin B₀ {z}) = A ⊔ B :=
    le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hz'.trans le_sup_left)))
      (sup_le_sup_left le_sup_left _)
  rw [s1, ek, eB] at c1
  have c2 := finrank_sup_mul_le (k := k) (X := B) (Y := k ⊔ adjoin B₀ {z}) hB le_sup_left
  have s2 : B ⊔ (k ⊔ adjoin B₀ {z}) = B ⊔ adjoin B₀ {z} := by
    rw [← sup_assoc, sup_eq_left.2 hB]
  rw [s2, ek, eB] at c2
  have pA : 0 < finrank B₀ A := Module.finrank_pos
  have pB : 0 < finrank B₀ B := Module.finrank_pos
  have pk : 0 < finrank B₀ k := Module.finrank_pos
  have pAB : 0 < finrank B₀ A * finrank B₀ B := Nat.mul_pos pA pB
  have pBk : 0 < finrank B₀ B * finrank B₀ k := Nat.mul_pos pB pk
  apply le_antisymm
  · have : finrank B₀ B * finrank B₀ k * (minpoly B z).natDegree ≤
        finrank B₀ B * finrank B₀ k * (minpoly k z).natDegree := by
      calc _ = finrank B₀ B * (minpoly B z).natDegree * finrank B₀ k := by ring
        _ ≤ finrank B₀ B * (finrank B₀ k * (minpoly k z).natDegree) := c2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this pBk
  · have : finrank B₀ A * finrank B₀ B * (minpoly k z).natDegree ≤
        finrank B₀ A * finrank B₀ B * (minpoly B z).natDegree := by
      calc _ = finrank B₀ ↥(A ⊔ B) * finrank B₀ k * (minpoly k z).natDegree := by rw [h]
        _ = finrank B₀ ↥(A ⊔ B) * (finrank B₀ k * (minpoly k z).natDegree) := by ring
        _ ≤ finrank B₀ A * (finrank B₀ B * (minpoly B z).natDegree) := c1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this pAB

/- English proof (translation)
Use `haveI := finiteDimensional_of_le hA`. Establish `hz0 : IsIntegral B₀ z`. Use `IsIntegral.of_finite B₀ (⟨z, hz⟩ : A)` as an intermediate fact. Conclude with `this.map (IsScalarTower.toAlgHom B₀ A Ω)`. Establish `hzk : IsIntegral k z` using `hz0.tower_top`.

Establish `hzB : IsIntegral B z` using `hz0.tower_top`. Use `letI : Algebra k B := (IntermediateField.inclusion hB).toAlgebra`. Use `haveI : IsScalarTower k B Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hdvd` using `minpoly.dvd_map_of_isScalarTower k B z`. Establish `heq : (minpoly k z).map (algebraMap k B) = minpoly B z` using `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzB) ((minpoly.monic hzk).map _) hdvd (by rw [natDegree_map, natDegree_minpoly_eq_of_finrank_sup hA hB h hz])`.

Rewrite using `[normTrace, normTraceF, ← heq, nextCoeff_map (algebraMap k B).injective, natDegree_map, normTrace, normTraceF]`. Rewrite using `[← map_natCast (algebraMap k B), ← map_neg, ← map_div₀, ← IsScalarTower.algebraMap_apply]`.
-/
theorem normTrace_eq_of_finrank_sup {k A B : IntermediateField B₀ Ω} (hA : k ≤ A)
    (hB : k ≤ B) [FiniteDimensional B₀ A] [FiniteDimensional B₀ B]
    (h : finrank B₀ ↥(A ⊔ B) * finrank B₀ k = finrank B₀ A * finrank B₀ B) {z : Ω} (hz : z ∈ A) :
    normTrace B z = normTrace k z := by
  haveI := finiteDimensional_of_le hA
  have hz0 : IsIntegral B₀ z := by
    have := IsIntegral.of_finite B₀ (⟨z, hz⟩ : A)
    exact this.map (IsScalarTower.toAlgHom B₀ A Ω)
  have hzk : IsIntegral k z := hz0.tower_top
  have hzB : IsIntegral B z := hz0.tower_top
  letI : Algebra k B := (IntermediateField.inclusion hB).toAlgebra
  haveI : IsScalarTower k B Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdvd := minpoly.dvd_map_of_isScalarTower k B z
  have heq : (minpoly k z).map (algebraMap k B) = minpoly B z :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzB) ((minpoly.monic hzk).map _) hdvd
      (by rw [natDegree_map, natDegree_minpoly_eq_of_finrank_sup hA hB h hz])
  rw [normTrace, normTraceF, ← heq, nextCoeff_map (algebraMap k B).injective, natDegree_map,
    normTrace, normTraceF]
  rw [← map_natCast (algebraMap k B), ← map_neg, ← map_div₀, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Use `haveI : CharZero k := (algebraMap k Ω).charZero`. Use `haveI : Algebra.IsIntegral k Ω := Algebra.IsIntegral.tower_top B₀`. Use `letI : Algebra k E := (IntermediateField.inclusion h).toAlgebra`. Use `haveI : IsScalarTower k E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower B₀ k E := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite B₀ k E`. Conclude with `normTrace_normTrace k E y`.
-/
theorem normTrace_normTrace_of_le [CharZero Ω] [Algebra.IsIntegral B₀ Ω]
    {k E : IntermediateField B₀ Ω} (h : k ≤ E) [FiniteDimensional B₀ E] (y : Ω) :
    normTrace k (normTrace E y) = normTrace k y := by
  haveI : CharZero k := (algebraMap k Ω).charZero
  haveI : Algebra.IsIntegral k Ω := Algebra.IsIntegral.tower_top B₀
  letI : Algebra k E := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B₀ k E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite B₀ k E
  exact normTrace_normTrace k E y

/- English proof (translation)
The claim follows from `(normTraceF k y).2`.
-/
theorem normTrace_mem (k : IntermediateField B₀ Ω) (y : Ω) : normTrace k y ∈ k :=
  (normTraceF k y).2

/- English proof (translation)
The claim follows from `normTrace_algebraMap k ⟨a, ha⟩`.
-/
theorem normTrace_of_mem (k : IntermediateField B₀ Ω) {a : Ω} (ha : a ∈ k) : normTrace k a = a :=
  normTrace_algebraMap k ⟨a, ha⟩

/- English proof (translation)
Use `haveI : CharZero k := (algebraMap k Ω).charZero`. Use `haveI : Algebra.IsIntegral k Ω := Algebra.IsIntegral.tower_top B₀`. Conclude with `normTrace_algebraMap_mul k ⟨a, ha⟩ y`.
-/
theorem normTrace_mul_of_mem [CharZero Ω] [Algebra.IsIntegral B₀ Ω] (k : IntermediateField B₀ Ω)
    {a : Ω} (ha : a ∈ k) (y : Ω) : normTrace k (a * y) = a * normTrace k y := by
  haveI : CharZero k := (algebraMap k Ω).charZero
  haveI : Algebra.IsIntegral k Ω := Algebra.IsIntegral.tower_top B₀
  exact normTrace_algebraMap_mul k ⟨a, ha⟩ y

end Degree

section Norm

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic y) h]`.
-/
theorem norm_eq_of_aeval_minpoly_eq_zero {y r : PadicAlgCl p}
    (h : aeval r (minpoly ℚ_[p] y) = 0) : ‖r‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic y) h]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simpa using hC`. Consider the case `cons a s ih`. Rewrite using `[Multiset.sum_cons]`. Conclude with `(IsUltrametricDist.norm_add_le_max a s.sum).trans (max_le (h a (Multiset.mem_cons_self a s)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))`.
-/
theorem norm_multiset_sum_le_of_forall_le_of_nonneg (s : Multiset (PadicAlgCl p)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ‖x‖ ≤ C) : ‖s.sum‖ ≤ C := by
  induction s using Multiset.induction_on with
  | empty => simpa using hC
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max a s.sum).trans
      (max_le (h a (Multiset.mem_cons_self a s)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))

/- English proof (translation)
Establish `hy : IsIntegral F y` using `(Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top`. Establish `hm : ((minpoly F y).map (algebraMap F (PadicAlgCl p))).Monic` using `(minpoly.monic hy).map _`. Rewrite using `[← nextCoeff_map (algebraMap F (PadicAlgCl p)).injective, (IsAlgClosed.splits _).nextCoeff_eq_neg_sum_roots_of_monic hm, norm_neg]`. Use `norm_multiset_sum_le_of_forall_le_of_nonneg _ (norm_nonneg y) fun r hr => le_of_eq ?_` and prove the remaining obligations. Apply `norm_eq_of_aeval_minpoly_eq_zero` to reduce the goal to its premises.

Establish `h1 : aeval r (minpoly F y) = 0`. Rewrite `hr` using `[mem_roots hm.ne_zero, IsRoot, eval_map, ← aeval_def]`. Conclude with `hr`. Establish `h2` using `minpoly.dvd_map_of_isScalarTower ℚ_[p] F y`. Use `Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h2 h1` as an intermediate fact.

Rewrite `this` using `[aeval_map_algebraMap]`. Then use the resulting hypothesis.
-/
theorem norm_nextCoeff_minpoly_le (F : Type*) [Field F] [Algebra ℚ_[p] F] [Algebra F (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] F (PadicAlgCl p)] (y : PadicAlgCl p) :
    ‖algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff‖ ≤ ‖y‖ := by
  have hy : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  have hm : ((minpoly F y).map (algebraMap F (PadicAlgCl p))).Monic := (minpoly.monic hy).map _
  rw [← nextCoeff_map (algebraMap F (PadicAlgCl p)).injective,
    (IsAlgClosed.splits _).nextCoeff_eq_neg_sum_roots_of_monic hm, norm_neg]
  refine norm_multiset_sum_le_of_forall_le_of_nonneg _ (norm_nonneg y) fun r hr => le_of_eq ?_
  apply norm_eq_of_aeval_minpoly_eq_zero
  have h1 : aeval r (minpoly F y) = 0 := by
    rw [mem_roots hm.ne_zero, IsRoot, eval_map, ← aeval_def] at hr
    exact hr
  have h2 := minpoly.dvd_map_of_isScalarTower ℚ_[p] F y
  have := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h2 h1
  rwa [aeval_map_algebraMap] at this

/- English proof (translation)
Establish `hy : IsIntegral F y` using `(Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top`. Take `⟨m, rfl⟩` from `hN`. Establish `hd : ((minpoly F y).natDegree : PadicAlgCl p) ≠ 0` using `Nat.cast_ne_zero.2 (minpoly.natDegree_pos hy).ne'`. Establish `e : (((minpoly F y).natDegree * m : ℕ) : PadicAlgCl p) * normTrace F y = (m : PadicAlgCl p) * -algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff`. Rewrite using `[normTrace, normTraceF, map_div₀, map_neg, map_natCast]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, norm_mul, norm_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_natCast_mul_normTrace_le (F : Type*) [Field F] [Algebra ℚ_[p] F]
    [Algebra F (PadicAlgCl p)] [IsScalarTower ℚ_[p] F (PadicAlgCl p)] (y : PadicAlgCl p) {N : ℕ}
    (hN : (minpoly F y).natDegree ∣ N) : ‖(N : PadicAlgCl p) * normTrace F y‖ ≤ ‖y‖ := by
  have hy : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  obtain ⟨m, rfl⟩ := hN
  have hd : ((minpoly F y).natDegree : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos hy).ne'
  have e : (((minpoly F y).natDegree * m : ℕ) : PadicAlgCl p) * normTrace F y =
      (m : PadicAlgCl p) * -algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff := by
    rw [normTrace, normTraceF, map_div₀, map_neg, map_natCast]
    push_cast
    field_simp
  rw [e, norm_mul, norm_neg]
  calc ‖(m : PadicAlgCl p)‖ * ‖algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff‖
      ≤ 1 * ‖y‖ := mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ m)
        (norm_nextCoeff_minpoly_le F y) (norm_nonneg _) zero_le_one
    _ = ‖y‖ := one_mul _

end Norm

end

end GroundTheory.PAdicHodge
