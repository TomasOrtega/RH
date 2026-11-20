import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes

open scoped TensorProduct

namespace GlobalTheory.BaseChangeComponents

variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

noncomputable def incl (R : Subalgebra K Ω) : F ⊗[K] R →+* F ⊗[K] Ω :=
  (Algebra.TensorProduct.map (AlgHom.id K F) R.val).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem incl_tmul (R : Subalgebra K Ω) (a : F) (r : R) :
    incl F R (a ⊗ₜ r) = a ⊗ₜ (r : Ω) := rfl

/- English proof (translation)
Introduce `x y hxy`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (R := K) (M := F) R.val.toLinearMap Subtype.val_injective hxy`.
-/
theorem incl_injective (R : Subalgebra K Ω) : Function.Injective (incl F R) :=
  by
    intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap (R := K) (M := F)
      R.val.toLinearMap Subtype.val_injective hxy

noncomputable def denoms (R : Subalgebra K Ω) : Submonoid (F ⊗[K] R) :=
  (nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := R))

/- English proof (translation)
Use `letI := (incl F R).toAlgebra`. Rewrite using `[isLocalization_iff]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Take `⟨r, hr, rfl⟩` from `Submonoid.mem_map.1 hy`.

Establish `hr0 : (r : Ω) ≠ 0`. Use `nonZeroDivisors.ne_zero hr` as an intermediate fact. Simplify using `using this`. Establish `hval : algebraMap (F ⊗[K] R) (F ⊗[K] Ω) (Algebra.TensorProduct.includeRight (R` using `K) (A := F) (B := R) r) = Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω) (r : Ω) := by show incl F R ((1 : F) ⊗ₜ r) = (1 : F) ⊗ₜ (r : Ω)`. Conclude with `incl_tmul F R 1 r`.

Rewrite using `[hval]`. Conclude with `(IsUnit.mk0 _ hr0).map _`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨(0, 1), by simp⟩`.

Consider the case `tmul a w`. Take `⟨c, hc, b, hb, hb0, hw⟩` from `hR w`. Establish `hbR : (⟨b, hb⟩ : R) ∈ nonZeroDivisors R` using `mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))`. Use `⟨(a ⊗ₜ ⟨c, hc⟩, ⟨(1 : F) ⊗ₜ ⟨b, hb⟩, Submonoid.mem_map_of_mem _ hbR⟩), ?_⟩` and prove the remaining obligations. Use `show (a ⊗ₜ w) * incl F R ((1 : F) ⊗ₜ ⟨b, hb⟩) = incl F R (a ⊗ₜ ⟨c, hc⟩)`.

Rewrite using `[incl_tmul, incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Conclude with `congrArg _ hw`. Consider the case `add x y hx hy`. Take `⟨⟨x₁, s₁⟩, h₁⟩` from `hx`. Take `⟨⟨x₂, s₂⟩, h₂⟩` from `hy`.

Use `⟨(x₁ * s₂ + x₂ * s₁, s₁ * s₂), ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.coe_mul, map_mul, map_add] at h₁ h₂ ⊢`. Take the linear combination `(algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₂) * h₁ + (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₁) * h₂`. Introduce `x y h`. Conclude with `⟨1, congrArg _ (incl_injective F R h)⟩`.
-/
theorem isLocalization_incl (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    @IsLocalization _ _ (denoms F R) (F ⊗[K] Ω) _ (incl F R).toAlgebra :=
  by
    letI := (incl F R).toAlgebra
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hy
      have hr0 : (r : Ω) ≠ 0 := by
        have := nonZeroDivisors.ne_zero hr
        simpa using this
      have hval : algebraMap (F ⊗[K] R) (F ⊗[K] Ω)
          (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := R) r) =
            Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω) (r : Ω) := by
        show incl F R ((1 : F) ⊗ₜ r) = (1 : F) ⊗ₜ (r : Ω)
        exact incl_tmul F R 1 r
      rw [hval]
      exact (IsUnit.mk0 _ hr0).map _
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp⟩
      | tmul a w =>
        obtain ⟨c, hc, b, hb, hb0, hw⟩ := hR w
        have hbR : (⟨b, hb⟩ : R) ∈ nonZeroDivisors R :=
          mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))
        refine ⟨(a ⊗ₜ ⟨c, hc⟩, ⟨(1 : F) ⊗ₜ ⟨b, hb⟩, Submonoid.mem_map_of_mem _ hbR⟩), ?_⟩
        show (a ⊗ₜ w) * incl F R ((1 : F) ⊗ₜ ⟨b, hb⟩) = incl F R (a ⊗ₜ ⟨c, hc⟩)
        rw [incl_tmul, incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        exact congrArg _ hw
      | add x y hx hy =>
        obtain ⟨⟨x₁, s₁⟩, h₁⟩ := hx
        obtain ⟨⟨x₂, s₂⟩, h₂⟩ := hy
        refine ⟨(x₁ * s₂ + x₂ * s₁, s₁ * s₂), ?_⟩
        simp only [Submonoid.coe_mul, map_mul, map_add] at h₁ h₂ ⊢
        linear_combination (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₂) * h₁ +
          (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₁) * h₂
    · intro x y h
      exact ⟨1, congrArg _ (incl_injective F R h)⟩

/- English proof (translation)
Use `letI := (incl F R).toAlgebra`. Use `haveI := isLocalization_incl F R hR`. Establish `h` using `IsLocalization.minimalPrimes_comap (denoms F R) (F ⊗[K] Ω) (⊥ : Ideal (F ⊗[K] Ω))`. Establish `hb : Ideal.comap (algebraMap (F ⊗[K] R) (F ⊗[K] Ω)) ⊥ = ⊥`. Rewrite using `[← RingHom.ker_eq_comap_bot]`.

Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (incl_injective F R)`. Rewrite `h` using `[hb]`. Conclude with `h`.
-/
theorem minimalPrimes_eq (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    minimalPrimes (F ⊗[K] R) = Ideal.comap (incl F R) '' minimalPrimes (F ⊗[K] Ω) :=
  by
    letI := (incl F R).toAlgebra
    haveI := isLocalization_incl F R hR
    have h := IsLocalization.minimalPrimes_comap (denoms F R) (F ⊗[K] Ω) (⊥ : Ideal (F ⊗[K] Ω))
    have hb : Ideal.comap (algebraMap (F ⊗[K] R) (F ⊗[K] Ω)) ⊥ = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (incl_injective F R)
    rw [hb] at h
    exact h

/- English proof (translation)
Use `letI := (incl F R).toAlgebra`. Use `haveI := isLocalization_incl F R hR`. Use `haveI : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).1 hfg`. Use `haveI : IsNoetherianRing (F ⊗[K] R) := Algebra.FiniteType.isNoetherianRing F (F ⊗[K] R)`. Conclude with `IsLocalization.isNoetherianRing (denoms F R) (F ⊗[K] Ω) inferInstance`.
-/
theorem isNoetherianRing_tensor (R : Subalgebra K Ω) (hfg : R.FG)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) : IsNoetherianRing (F ⊗[K] Ω) :=
  by
    letI := (incl F R).toAlgebra
    haveI := isLocalization_incl F R hR
    haveI : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).1 hfg
    haveI : IsNoetherianRing (F ⊗[K] R) := Algebra.FiniteType.isNoetherianRing F (F ⊗[K] R)
    exact IsLocalization.isNoetherianRing (denoms F R) (F ⊗[K] Ω) inferInstance

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Subring.zero_mem _`.

Consider the case `tmul a r`. Establish `hsplit : (g.comp (incl F R)) (a ⊗ₜ r) = g (a ⊗ₜ (1 : Ω)) * g ((1 : F) ⊗ₜ (r : Ω))`. Rewrite using `[RingHom.comp_apply, incl_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hsplit]`. Conclude with `Subring.mul_mem _ (Subring.subset_closure (Or.inr ⟨a, rfl⟩)) (Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩))`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Subring.add_mem _ hx hy`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨w, hw, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `⟨(1 : F) ⊗ₜ ⟨w, hw⟩, by rw [RingHom.comp_apply, incl_tmul]; rfl⟩`.

Conclude with `⟨a ⊗ₜ (1 : R), by rw [RingHom.comp_apply, incl_tmul]; rfl⟩`.
-/
theorem range_comp_incl {E : Type} [CommRing E] (R : Subalgebra K Ω) (g : F ⊗[K] Ω →+* E) :
    (g.comp (incl F R)).range = Subring.closure
      ((g.comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω)
        ∪ Set.range (g.comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) :=
  by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Subring.zero_mem _
      | tmul a r =>
        have hsplit : (g.comp (incl F R)) (a ⊗ₜ r) =
            g (a ⊗ₜ (1 : Ω)) * g ((1 : F) ⊗ₜ (r : Ω)) := by
          rw [RingHom.comp_apply, incl_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        rw [hsplit]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inr ⟨a, rfl⟩))
          (Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩))
      | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
    · rw [Subring.closure_le]
      rintro _ (⟨w, hw, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨(1 : F) ⊗ₜ ⟨w, hw⟩, by rw [RingHom.comp_apply, incl_tmul]; rfl⟩
      · exact ⟨a ⊗ₜ (1 : R), by rw [RingHom.comp_apply, incl_tmul]; rfl⟩

set_option maxHeartbeats 400000 in
/- English proof (translation)
Establish `key : ∀ s : (F ⊗[K] Ω), ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) s ∈ Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight …` using `K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) := by`. Introduce `s`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Subfield.zero_mem _`.

Consider the case `tmul a w`. Establish `hsplit : ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ w) = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ (1 : Ω)) * ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P)) …`. Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hsplit]`. Conclude with `Subfield.mul_mem _ (Subfield.subset_closure (Or.inr ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨w, rfl⟩))`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Subfield.add_mem _ hx hy`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨x, y, -, rfl⟩` from `IsFractionRing.div_surjective (A := (F ⊗[K] Ω) ⧸ P) z`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `Subfield.div_mem _ (key s) (key t)`.
-/
private theorem closure_range_tensor_quotient_fraction (P : Ideal (F ⊗[K] Ω)) [P.IsPrime] :
    Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) = ⊤ := by
  have key : ∀ s : (F ⊗[K] Ω), ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) s ∈
      Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subfield.zero_mem _
    | tmul a w =>
      have hsplit : ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ w) =
          ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ (1 : Ω)) * ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) ((1 : F) ⊗ₜ w) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨w, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subfield.add_mem _ hx hy
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := (F ⊗[K] Ω) ⧸ P) z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact Subfield.div_mem _ (key s) (key t)

set_option maxHeartbeats 400000 in
/- English proof (translation)
Establish `hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P`. Use extensionality with `x`. Simplify using `only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`. Set `e` to `(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))`.

Establish `hmin : Ideal.comap (incl F R) P ∈ minimalPrimes (F ⊗[K] R)`. Rewrite using `[minimalPrimes_eq F R hR]`. Conclude with `⟨P, hP, rfl⟩`. Use `haveI : IsIntegrallyClosed ((F ⊗[K] R) ⧸ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R))) := GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth F (F ⊗[K] R) _ (hker.symm ▸ hmin)`. Conclude with `IsIntegrallyClosed.of_equiv e`.
-/
private theorem isIntegrallyClosed_closure_minimalPrime_quotient (R : Subalgebra K Ω) [Algebra.Smooth K R]
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (P : Ideal (F ⊗[K] Ω)) (hP : P ∈ minimalPrimes (F ⊗[K] Ω)) : IsIntegrallyClosed (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))))) := by
  have hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let e := (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))
  have hmin : Ideal.comap (incl F R) P ∈ minimalPrimes (F ⊗[K] R) := by
    rw [minimalPrimes_eq F R hR]
    exact ⟨P, hP, rfl⟩
  haveI : IsIntegrallyClosed ((F ⊗[K] R) ⧸ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R))) :=
    GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth F (F ⊗[K] R) _ (hker.symm ▸ hmin)
  exact IsIntegrallyClosed.of_equiv e

set_option maxHeartbeats 400000 in
/- English proof (translation)
Use `letI : Algebra K L := (χ.comp (algebraMap K F)).toAlgebra`. Set `χ' : F →ₐ[K] L` to `{ χ with commutes' := fun a => rfl }`. Set `ψ' : R →ₐ[K] L` to `{ ψ with commutes' := fun a => hχψ a }`. Set `θ : F ⊗[K] R →ₐ[K] L` to `Algebra.TensorProduct.productMap χ' ψ'`. Use `haveI : (RingHom.ker θ.toRingHom).IsPrime := RingHom.ker_isPrime _`.

Take `⟨q, hq, hqle⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (F ⊗[K] R))) (J := RingHom.ker θ.toRingHom) bot_le`. Establish `hq' : q ∈ minimalPrimes (F ⊗[K] R)` using `hq`. Rewrite `hq'` using `[minimalPrimes_eq F R hR]`. Take `⟨P, hP, rfl⟩` from `hq'`. Establish `hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P`.

Use extensionality with `x`. Simplify using `only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`. Set `e` to `(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))`. Establish `hlift : ∀ a ∈ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)), θ.toRingHom a = 0`.

Introduce `a ha`. Rewrite `ha` using `[hker]`. Conclude with `RingHom.mem_ker.1 (hqle ha)`. Set `φ` to `(Ideal.Quotient.lift _ θ.toRingHom hlift).comp e.symm.toRingHom`. Establish `hφ : ∀ x, φ (e (Ideal.Quotient.mk _ x)) = θ x`.

Introduce `x`. Simplify using `only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]`. Both sides reduce to the same expression. Use `⟨P, hP, φ, fun r h => ?_, fun a h => ?_⟩` and prove the remaining obligations. Establish `hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R` using `K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ ((1 : F) ⊗ₜ[K] r)) := Su …`.

Rewrite using `[incl_tmul]`. Use the proof step `rfl)`. Rewrite using `[hpt, hφ]`. Use `show χ 1 * ψ r = ψ r`. Rewrite using `[map_one, one_mul]`.

Establish `hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R` using `K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ (a ⊗ₜ[K] (1 : R))) := Su …`. Rewrite using `[incl_tmul]`. Use the proof step `rfl)`. Rewrite using `[hpt, hφ]`. Use `show χ a * ψ 1 = χ a`.

Rewrite using `[map_one, mul_one]`.
-/
private theorem exists_minimalPrime_closure_lift (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L)
    (hχψ : ∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) :
    ∃ (P : Ideal (F ⊗[K] Ω)) (_ : P ∈ minimalPrimes (F ⊗[K] Ω)) (φ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))))) →+* L),
      (∀ (r : R) (h : (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) r ∈ (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))), φ ⟨(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) r, h⟩ = ψ r) ∧
      ∀ (a : F) (h : (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))) a ∈ (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))), φ ⟨(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))) a, h⟩ = χ a := by
  letI : Algebra K L := (χ.comp (algebraMap K F)).toAlgebra
  let χ' : F →ₐ[K] L := { χ with commutes' := fun a => rfl }
  let ψ' : R →ₐ[K] L := { ψ with commutes' := fun a => hχψ a }
  let θ : F ⊗[K] R →ₐ[K] L := Algebra.TensorProduct.productMap χ' ψ'
  haveI : (RingHom.ker θ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal (F ⊗[K] R))) (J := RingHom.ker θ.toRingHom) bot_le
  have hq' : q ∈ minimalPrimes (F ⊗[K] R) := hq
  rw [minimalPrimes_eq F R hR] at hq'
  obtain ⟨P, hP, rfl⟩ := hq'
  have hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let e := (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))
  have hlift : ∀ a ∈ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)), θ.toRingHom a = 0 := by
    intro a ha
    rw [hker] at ha
    exact RingHom.mem_ker.1 (hqle ha)
  let φ := (Ideal.Quotient.lift _ θ.toRingHom hlift).comp e.symm.toRingHom
  have hφ : ∀ x, φ (e (Ideal.Quotient.mk _ x)) = θ x := by
    intro x
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
    rfl
  refine ⟨P, hP, φ, fun r h => ?_, fun a h => ?_⟩
  · have hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ ((1 : F) ⊗ₜ[K] r)) :=
      Subtype.ext (by
        show _ = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (incl F R ((1 : F) ⊗ₜ[K] r))
        rw [incl_tmul]; rfl)
    rw [hpt, hφ]
    show χ 1 * ψ r = ψ r
    rw [map_one, one_mul]
  · have hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ (a ⊗ₜ[K] (1 : R))) :=
      Subtype.ext (by
        show _ = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (incl F R (a ⊗ₜ[K] (1 : R)))
        rw [incl_tmul]; rfl)
    rw [hpt, hφ]
    show χ a * ψ 1 = χ a
    rw [map_one, mul_one]

/- English proof (translation)
Introduce `K F Ω _ _ _ _ _ R₀ hfg hR₀`. Use `haveI := isNoetherianRing_tensor F R₀ hfg hR₀`. Use `haveI hJ : Finite ↥(minimalPrimes (F ⊗[K] Ω)) := (minimalPrimes.finite_of_isNoetherianRing (F ⊗[K] Ω)).to_subtype`. Use `haveI hprime : ∀ j : ↥(minimalPrimes (F ⊗[K] Ω)), (j.1).IsPrime := fun j => Ideal.minimalPrimes_isPrime j.2`. Use `⟨↥(minimalPrimes (F ⊗[K] Ω)), hJ, fun j => FractionRing ((F ⊗[K] Ω) ⧸ j.1), fun j => inferInstance, fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRi …` and prove the remaining obligations.

Introduce `j a show ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) (Algebra.TensorProduct.includeRight (algebraMap K Ω a)) = ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) ((algebraMap K F a) …`. Rewrite using `[AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]`. Introduce `j`. Conclude with `closure_range_tensor_quotient_fraction F j.1`. Introduce `R _ hR`.

Use `⟨fun j => isIntegrallyClosed_closure_minimalPrime_quotient F R hR j.1 j.2, fun L _ χ ψ hχψ => ?_⟩` and prove the remaining obligations. Take `⟨P, hP, φ, h₁, h₂⟩` from `exists_minimalPrime_closure_lift F R hR L χ ψ hχψ`. Conclude with `⟨⟨P, hP⟩, φ, h₁, h₂⟩`.
-/
theorem components : ∀ (K F Ω : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω] (R₀ : Subalgebra K Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∃ (J : Type) (_ : Finite J) (Ω' : J → Type) (_ : ∀ j, Field (Ω' j)) (α : ∀ j, Ω →+* Ω' j) (γ : ∀ j, F →+* Ω' j), (∀ j (a : K), α j (algebraMap K Ω a) = γ j (algebraMap K F a)) ∧ (∀ j, Subfield.closure (Set.range (α j) ∪ Set.range (γ j)) = ⊤) ∧ ∀ (R : Subalgebra K Ω), Algebra.Smooth K R → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) → (∀ j, IsIntegrallyClosed (Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)))) ∧ ∀ (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L), (∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) → ∃ (j : J) (φ : Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)) →+* L), (∀ (r : R) (h : α j r ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨α j r, h⟩ = ψ r) ∧ ∀ (a : F) (h : γ j a ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨γ j a, h⟩ = χ a :=
  by
    intro K F Ω _ _ _ _ _ R₀ hfg hR₀
    haveI := isNoetherianRing_tensor F R₀ hfg hR₀
    haveI hJ : Finite ↥(minimalPrimes (F ⊗[K] Ω)) :=
      (minimalPrimes.finite_of_isNoetherianRing (F ⊗[K] Ω)).to_subtype
    haveI hprime : ∀ j : ↥(minimalPrimes (F ⊗[K] Ω)), (j.1).IsPrime :=
      fun j => Ideal.minimalPrimes_isPrime j.2
    refine ⟨↥(minimalPrimes (F ⊗[K] Ω)), hJ, fun j => FractionRing ((F ⊗[K] Ω) ⧸ j.1),
      fun j => inferInstance, fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom), fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))), ?_, ?_, ?_⟩
    · intro j a
      show ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) (Algebra.TensorProduct.includeRight (algebraMap K Ω a)) =
        ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) ((algebraMap K F a) ⊗ₜ (1 : Ω))
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    · intro j
      exact closure_range_tensor_quotient_fraction F j.1
    · intro R _ hR
      refine ⟨fun j => isIntegrallyClosed_closure_minimalPrime_quotient F R hR j.1 j.2, fun L _ χ ψ hχψ => ?_⟩
      obtain ⟨P, hP, φ, h₁, h₂⟩ := exists_minimalPrime_closure_lift F R hR L χ ψ hχψ
      exact ⟨⟨P, hP⟩, φ, h₁, h₂⟩

end GlobalTheory.BaseChangeComponents
