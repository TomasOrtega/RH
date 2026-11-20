import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

namespace GlobalTheory

namespace IntegralOverComplete

open IsLocalRing Polynomial

/- English proof (translation)
Establish `: Algebra.IsIntegral W' R` using `Algebra.IsIntegral.tower_top W`. Establish `: FaithfulSMul W' R` using `(faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective`. Conclude with `inferInstanceAs (IsLocalHom (algebraMap W' R))`.
-/
theorem isLocalHom_val {W R : Type} [CommRing W] [CommRing R] [Algebra W R]
    [Algebra.IsIntegral W R] (W' : Subalgebra W R) : IsLocalHom W'.val.toRingHom := by
  have : Algebra.IsIntegral W' R := Algebra.IsIntegral.tower_top W
  have : FaithfulSMul W' R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  exact inferInstanceAs (IsLocalHom (algebraMap W' R))

/- English proof (translation)
Set `F` to `FractionRing R`. Set `j : R →ₐ[W] F` to `IsScalarTower.toAlgHom W R F`. Establish `hj : Function.Injective j` using `IsFractionRing.injective R F`. Establish `: FaithfulSMul W F` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (by`. Rewrite using `[IsScalarTower.algebraMap_eq W R F]`.

Conclude with `hj.comp (FaithfulSMul.algebraMap_injective W R))`. Establish `: Algebra.IsAlgebraic R F` using `IsLocalization.isAlgebraic F (nonZeroDivisors R)`. Establish `: Algebra.IsAlgebraic W F` using `Algebra.IsAlgebraic.trans W R F`. Take `⟨V, hV, -, -, hfin, -, -, -, hs⟩` from `exists_complete_dvr_finite_subalgebra W F (s.image j)`. Establish `hle : V ≤ j.range` using `fun x hx => by`.

Establish `h1 : IsIntegral W x` using `(Algebra.IsIntegral.isIntegral (R := W) (⟨x, hx⟩ : V)).map V.val`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := R))`. Set `W' : Subalgebra W R` to `V.comap j`. Establish `hmap : W'.map j = V`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hx`. Introduce `x hx`. Take `⟨y, rfl⟩` from `hle hx`. Conclude with `⟨y, hx, rfl⟩`.

Set `e : V ≃ₐ[W] W'` to `((Subalgebra.equivMapOfInjective W' j hj).trans (Subalgebra.equivOfEq _ _ hmap)).symm`. Establish `hd : IsDiscreteValuationRing W'` using `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e`. Establish `hf : Module.Finite W W'` using `Module.Finite.equiv e.toLinearEquiv`. Use `⟨W', hd, fun x hx => ?_, CompleteFiniteExtension.isAdicComplete_of_finite_local W W', hf, isLocalHom_val W'⟩` and prove the remaining obligations. Conclude with `hs _ (Finset.mem_image_of_mem j hx) ((Algebra.IsIntegral.isIntegral x).map j)`.
-/
theorem exists_subalgebra (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra W R] [FaithfulSMul W R] [Algebra.IsIntegral W R]
    (s : Finset R) :
    ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ Module.Finite W W' ∧
      IsLocalHom W'.val.toRingHom := by
  classical
  let F := FractionRing R
  let j : R →ₐ[W] F := IsScalarTower.toAlgHom W R F
  have hj : Function.Injective j := IsFractionRing.injective R F
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq W R F]
    exact hj.comp (FaithfulSMul.algebraMap_injective W R))
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  have : Algebra.IsAlgebraic W F := Algebra.IsAlgebraic.trans W R F
  obtain ⟨V, hV, -, -, hfin, -, -, -, hs⟩ :=
    exists_complete_dvr_finite_subalgebra W F (s.image j)
  have hle : V ≤ j.range := fun x hx => by
    have h1 : IsIntegral W x :=
      (Algebra.IsIntegral.isIntegral (R := W) (⟨x, hx⟩ : V)).map V.val
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := R))
  let W' : Subalgebra W R := V.comap j
  have hmap : W'.map j = V := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx
      obtain ⟨y, rfl⟩ := hle hx
      exact ⟨y, hx, rfl⟩
  let e : V ≃ₐ[W] W' :=
    ((Subalgebra.equivMapOfInjective W' j hj).trans (Subalgebra.equivOfEq _ _ hmap)).symm
  have hd : IsDiscreteValuationRing W' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hf : Module.Finite W W' := Module.Finite.equiv e.toLinearEquiv
  refine ⟨W', hd, fun x hx => ?_,
    CompleteFiniteExtension.isAdicComplete_of_finite_local W W', hf, isLocalHom_val W'⟩
  exact hs _ (Finset.mem_image_of_mem j hx) ((Algebra.IsIntegral.isIntegral x).map j)

/- English proof (translation)
Use `⟨fun f hf a₀ h0 hu => ?_⟩` and prove the remaining obligations. Take `⟨V, _, hs, hc, hl⟩` from `h (insert a₀ f.coeffs ∪ {0})`. Set `i : V →+* R` to `V.val.toRingHom`. Establish `hlift : f ∈ lifts i`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `n`. Distinguish the cases in `hn : f.coeff n = 0`. Conclude with `⟨0, by simp [hn]⟩`. Conclude with `⟨⟨f.coeff n, hs (by simp [coeff_mem_coeffs hn])⟩, rfl⟩`. Take `⟨g, hg, -, hgm⟩` from `lifts_and_natDegree_eq_and_monic hlift hf`.

Take `⟨b, rfl⟩ : ∃ b : V, i b = a₀` from `⟨⟨a₀, hs (by simp)⟩, rfl⟩`. Substitute `hg` using the available equality. Rewrite `h0` using `[eval_map, eval₂_at_apply]`. Rewrite `hu` using `[derivative_map, eval_map, eval₂_at_apply]`. Establish `h0' : g.eval b ∈ maximalIdeal V` using `fun hu' => h0 (hu'.map i)`.

Establish `hu' : IsUnit (g.derivative.eval b)` using `IsLocalHom.map_nonunit _ hu`. Take `⟨a, ha, hab⟩` from `HenselianRing.is_henselian (I := maximalIdeal V) g hgm b h0' (hu'.map _)`. Use `⟨i a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]`. Rewrite using `[← map_sub]`.

Conclude with `fun hh => hab (IsLocalHom.map_nonunit _ hh)`.
-/
theorem henselian_of_union (W R : Type) [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (h : ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsLocalRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ IsLocalHom W'.val.toRingHom) :
    HenselianLocalRing R := by
  classical
  refine ⟨fun f hf a₀ h0 hu => ?_⟩
  obtain ⟨V, _, hs, hc, hl⟩ := h (insert a₀ f.coeffs ∪ {0})
  let i : V →+* R := V.val.toRingHom
  have hlift : f ∈ lifts i := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : f.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨f.coeff n, hs (by simp [coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  obtain ⟨b, rfl⟩ : ∃ b : V, i b = a₀ := ⟨⟨a₀, hs (by simp)⟩, rfl⟩
  subst hg
  rw [eval_map, eval₂_at_apply] at h0
  rw [derivative_map, eval_map, eval₂_at_apply] at hu
  have h0' : g.eval b ∈ maximalIdeal V := fun hu' => h0 (hu'.map i)
  have hu' : IsUnit (g.derivative.eval b) := IsLocalHom.map_nonunit _ hu
  obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian (I := maximalIdeal V) g hgm b h0' (hu'.map _)
  refine ⟨i a, ?_, ?_⟩
  · rw [IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact fun hh => hab (IsLocalHom.map_nonunit _ hh)

end IntegralOverComplete

/- English proof (translation)
Introduce `W R _ _ _ _ _ _ _ _ _ hinj hint`. Establish `: FaithfulSMul W R` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Use `⟨inferInstance, IntegralOverComplete.henselian_of_union W R fun s => ?_, IntegralOverComplete.exists_subalgebra W R⟩` and prove the remaining obligations. Take `⟨V, hV, h1, h2, -, h3⟩` from `IntegralOverComplete.exists_subalgebra W R s`. Conclude with `⟨V, inferInstance, h1, h2, h3⟩`.
-/
theorem henselian_and_union_of_isIntegral_complete :
    ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) →
      Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧
      ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'),
        (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧
        Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by
  intro W R _ _ _ _ _ _ _ _ _ hinj hint
  have : FaithfulSMul W R := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine ⟨inferInstance, IntegralOverComplete.henselian_of_union W R fun s => ?_,
    IntegralOverComplete.exists_subalgebra W R⟩
  obtain ⟨V, hV, h1, h2, -, h3⟩ := IntegralOverComplete.exists_subalgebra W R s
  exact ⟨V, inferInstance, h1, h2, h3⟩

end GlobalTheory
