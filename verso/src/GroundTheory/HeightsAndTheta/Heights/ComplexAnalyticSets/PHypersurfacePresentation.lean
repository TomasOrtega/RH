import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHypersurfacePresentation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace HypersurfacePresentation

section Core

variable {R A E L : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Field E] [Algebra R E] [IsFractionRing R E] [CharZero E]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra E L] [IsScalarTower R E L]

omit [CharZero E] [IsDomain A] in

/- English proof (translation)
Take `⟨b, hb, h⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) p`. Conclude with `⟨b, nonZeroDivisors.ne_zero hb, _, by rw [h, Algebra.smul_def, Polynomial.algebraMap_apply]⟩`.
-/
theorem exists_clear_denominators (p : Polynomial E) :
    ∃ b : R, b ≠ 0 ∧ ∃ p' : Polynomial R,
      p'.map (algebraMap R E) = Polynomial.C (algebraMap R E b) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  exact ⟨b, nonZeroDivisors.ne_zero hb, _, by rw [h, Algebra.smul_def, Polynomial.algebraMap_apply]⟩

omit [IsDomain A] in
include E L in

/- English proof (translation)
Establish `hθL : IsIntegral R (algebraMap A L θ)` using `hθ.map (IsScalarTower.toAlgHom R A L)`. Establish `hm : minpoly R (algebraMap A L θ) = minpoly R θ` using `minpoly.algHom_eq (IsScalarTower.toAlgHom R A L) (IsFractionRing.injective A L) θ`. Establish `hE : minpoly E (algebraMap A L θ) = (minpoly R θ).map (algebraMap R E)`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' E hθL, hm]`. Take `⟨a, b, hab⟩` from `(minpoly.irreducible (hθL.tower_top (A := E))).separable`.

Rewrite `hab` using `[hE, Polynomial.derivative_map]`. Take `⟨ba, hba, a', ha'⟩` from `exists_clear_denominators (R := R) a`. Take `⟨bb, hbb, b', hb'⟩` from `exists_clear_denominators (R := R) b`. Use `⟨ba * bb, mul_ne_zero hba hbb, Polynomial.C bb * a', Polynomial.C ba * b', ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective (algebraMap R E) (IsFractionRing.injective R E)` to reduce the goal to its premises.

Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ha', hb', map_mul]`. Take the linear combination `(Polynomial.C (algebraMap R E ba) * Polynomial.C (algebraMap R E bb)) * hab`.
-/
theorem minpoly_separable_up_to [IsIntegrallyClosed R] {θ : A} (hθ : IsIntegral R θ) :
    ∃ δ : R, δ ≠ 0 ∧ ∃ u v : Polynomial R,
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C δ := by
  have hθL : IsIntegral R (algebraMap A L θ) := hθ.map (IsScalarTower.toAlgHom R A L)
  have hm : minpoly R (algebraMap A L θ) = minpoly R θ :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom R A L) (IsFractionRing.injective A L) θ
  have hE : minpoly E (algebraMap A L θ) = (minpoly R θ).map (algebraMap R E) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' E hθL, hm]
  obtain ⟨a, b, hab⟩ := (minpoly.irreducible (hθL.tower_top (A := E))).separable
  rw [hE, Polynomial.derivative_map] at hab
  obtain ⟨ba, hba, a', ha'⟩ := exists_clear_denominators (R := R) a
  obtain ⟨bb, hbb, b', hb'⟩ := exists_clear_denominators (R := R) b
  refine ⟨ba * bb, mul_ne_zero hba hbb, Polynomial.C bb * a', Polynomial.C ba * b', ?_⟩
  apply Polynomial.map_injective (algebraMap R E) (IsFractionRing.injective R E)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ha', hb', map_mul]
  linear_combination (Polynomial.C (algebraMap R E ba) * Polynomial.C (algebraMap R E bb)) * hab

omit [CharZero E] [IsDomain A] in

/- English proof (translation)
Establish `hθE : IsIntegral E (algebraMap A L θ)` using `(hθ.map (IsScalarTower.toAlgHom R A L)).tower_top`. Establish `hx : algebraMap A L x ∈ (IntermediateField.adjoin E {algebraMap A L θ}).toSubalgebra`. Rewrite using `[hgen]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hx` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθE.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨p, hp⟩` from `hx`. Take `⟨b, hb, q, hq⟩` from `exists_clear_denominators (R := R) p`. Use `⟨b, hb, q, IsFractionRing.injective A L ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (Polynomial.aeval (algebraMap A L θ)) hq`. Rewrite `h1` using `[Polynomial.aeval_map_algebraMap, map_mul, Polynomial.aeval_C]`.

Rewrite using `[← Polynomial.aeval_algebraMap_apply, h1, map_mul, ← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R E L]`. Conclude with `congrArg _ hp`.
-/
theorem exists_mul_eq_aeval {θ : A} (hθ : IsIntegral R θ)
    (hgen : IntermediateField.adjoin E {algebraMap A L θ} = ⊤) (x : A) :
    ∃ b : R, b ≠ 0 ∧ ∃ q : Polynomial R, Polynomial.aeval θ q = algebraMap R A b * x := by
  have hθE : IsIntegral E (algebraMap A L θ) := (hθ.map (IsScalarTower.toAlgHom R A L)).tower_top
  have hx : algebraMap A L x ∈ (IntermediateField.adjoin E {algebraMap A L θ}).toSubalgebra := by
    rw [hgen]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθE.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨b, hb, q, hq⟩ := exists_clear_denominators (R := R) p
  refine ⟨b, hb, q, IsFractionRing.injective A L ?_⟩
  have h1 := congrArg (Polynomial.aeval (algebraMap A L θ)) hq
  rw [Polynomial.aeval_map_algebraMap, map_mul, Polynomial.aeval_C] at h1
  rw [← Polynomial.aeval_algebraMap_apply, h1, map_mul, ← IsScalarTower.algebraMap_apply R A L,
    IsScalarTower.algebraMap_apply R E L]
  exact congrArg _ hp

omit [IsDomain R] [IsDomain A] in

/- English proof (translation)
Establish `: CharZero L` using `charZero_of_injective_algebraMap (algebraMap E L).injective`. Establish `hint : ∀ j, IsIntegral E (algebraMap A L (x j))` using `fun j => (((Algebra.IsAlgebraic.isAlgebraic (R := R) (x j)).algHom (IsScalarTower.toAlgHom R A L)).extendScalars (IsFractionRing.injective R E)).isIntegral`. Establish `: FiniteDimensional E L`. Use `IntermediateField.finiteDimensional_adjoin (K := E) (S := Set.range fun j => algebraMap A L (x j)) (by rintro _ ⟨j, rfl⟩; exact hint j)` as an intermediate fact. Rewrite `this` using `[hgen]`.

Conclude with `IntermediateField.topEquiv.toLinearEquiv.finiteDimensional`. Establish `: Algebra.IsSeparable E L` using `Algebra.IsAlgebraic.isSeparable_of_perfectField`. Establish `: IsScalarTower ℚ E L` using `IsScalarTower.of_algebraMap_eq fun q => by`. Rewrite using `[eq_ratCast (algebraMap ℚ E) q, map_ratCast, eq_ratCast]`. Take `⟨D, hD, hDc⟩` from `ComplexSets.GenericPrimitive.proof ℚ E L n (fun j => algebraMap A L (x j)) hgen`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hcD⟩ : ∃ c ∈ Set.pi Set.univ (fun _ : Fin n => Set.range (Int.cast : ℤ → ℚ)), MvPolynomial.eval c D ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hD (MvPolynomial.funext_set _ (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun c hc => by simpa using h c hc)`. Use `choose z hz using fun j => hc j (Set.mem_univ j)`.

Use `set θ₁ : A := ∑ j, z j • x j with hθ₁def`. Establish `hθ₁ : IntermediateField.adjoin E {algebraMap A L θ₁} = ⊤`. Establish `h` using `hDc c hcD`. Establish `he : ∑ j, c j • algebraMap A L (x j) = algebraMap A L θ₁`. Simplify using `only [hθ₁def, map_sum, map_zsmul, ← hz, Int.cast_smul_eq_zsmul]`.

Rewrite `h` using `[he]`. Then use the resulting hypothesis. Take `⟨a, ha, hai⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := R) θ₁).exists_integral_multiple`. Use `⟨a • θ₁, hai, eq_top_iff.2 (hθ₁ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)⟩` and prove the remaining obligations. Establish `ha' : algebraMap E L (algebraMap R E a) ≠ 0`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A L]`.

Introduce `h0`. Conclude with `ha ((FaithfulSMul.algebraMap_injective R A).eq_iff' (map_zero _) |>.1 ((IsFractionRing.injective A L).eq_iff' (map_zero _) |>.1 h0))`. Establish `heq : algebraMap A L θ₁ = (algebraMap E L (algebraMap R E a))⁻¹ * algebraMap A L (a • θ₁)`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R E L, inv_mul_cancel_left₀ ha']`. Rewrite using `[heq]`.

Conclude with `mul_mem (IntermediateField.inv_mem _ (IntermediateField.algebraMap_mem _ _)) (IntermediateField.mem_adjoin_simple_self E _)`.
-/
theorem exists_integral_primitive [FaithfulSMul R A] [Algebra.IsAlgebraic R A] {n : ℕ} (x : Fin n → A)
    (hgen : IntermediateField.adjoin E (Set.range fun j => algebraMap A L (x j)) = ⊤) :
    ∃ θ : A, IsIntegral R θ ∧ IntermediateField.adjoin E {algebraMap A L θ} = ⊤ := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  have hint : ∀ j, IsIntegral E (algebraMap A L (x j)) := fun j =>
    (((Algebra.IsAlgebraic.isAlgebraic (R := R) (x j)).algHom (IsScalarTower.toAlgHom R A L)).extendScalars
      (IsFractionRing.injective R E)).isIntegral
  have : FiniteDimensional E L := by
    have := IntermediateField.finiteDimensional_adjoin (K := E)
      (S := Set.range fun j => algebraMap A L (x j)) (by rintro _ ⟨j, rfl⟩; exact hint j)
    rw [hgen] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have : Algebra.IsSeparable E L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ E) q, map_ratCast, eq_ratCast]
  obtain ⟨D, hD, hDc⟩ := ComplexSets.GenericPrimitive.proof ℚ E L n (fun j => algebraMap A L (x j)) hgen
  obtain ⟨c, hc, hcD⟩ : ∃ c ∈ Set.pi Set.univ (fun _ : Fin n => Set.range (Int.cast : ℤ → ℚ)),
      MvPolynomial.eval c D ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (MvPolynomial.funext_set _ (fun _ => Set.infinite_range_of_injective Int.cast_injective)
      fun c hc => by simpa using h c hc)
  choose z hz using fun j => hc j (Set.mem_univ j)
  set θ₁ : A := ∑ j, z j • x j with hθ₁def
  have hθ₁ : IntermediateField.adjoin E {algebraMap A L θ₁} = ⊤ := by
    have h := hDc c hcD
    have he : ∑ j, c j • algebraMap A L (x j) = algebraMap A L θ₁ := by
      simp only [hθ₁def, map_sum, map_zsmul, ← hz, Int.cast_smul_eq_zsmul]
    rwa [he] at h
  obtain ⟨a, ha, hai⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) θ₁).exists_integral_multiple
  refine ⟨a • θ₁, hai, eq_top_iff.2 (hθ₁ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)⟩
  have ha' : algebraMap E L (algebraMap R E a) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A L]
    intro h0
    exact ha ((FaithfulSMul.algebraMap_injective R A).eq_iff' (map_zero _) |>.1
      ((IsFractionRing.injective A L).eq_iff' (map_zero _) |>.1 h0))
  have heq : algebraMap A L θ₁ = (algebraMap E L (algebraMap R E a))⁻¹ * algebraMap A L (a • θ₁) := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A L,
      IsScalarTower.algebraMap_apply R E L, inv_mul_cancel_left₀ ha']
  rw [heq]
  exact mul_mem (IntermediateField.inv_mem _ (IntermediateField.algebraMap_mem _ _))
    (IntermediateField.mem_adjoin_simple_self E _)

end Core

section Generic

/- English proof (translation)
Establish `: FaithfulSMul R (FractionRing A)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (by`. Rewrite using `[IsScalarTower.algebraMap_eq R A (FractionRing A)]`. Conclude with `(IsFractionRing.injective A (FractionRing A)).comp (FaithfulSMul.algebraMap_injective R A))`. Set `: Algebra (FractionRing R) (FractionRing A)` to `FractionRing.liftAlgebra _ _`. Establish `: CharZero (FractionRing R)` using `charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))`.

Establish `hgen : IntermediateField.adjoin (FractionRing R) (Set.range fun j => algebraMap A (FractionRing A) (x j)) = ⊤` using `by set F := IntermediateField.adjoin (FractionRing R) (Set.range fun j => algebraMap A (FractionRing A) (x j))`. Establish `hA : ∀ a : A, algebraMap A (FractionRing A) a ∈ F`. Introduce `a`. Establish `ha : a ∈ Algebra.adjoin R (Set.range x)` using `hx ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`.

Consider the case `mem a h`. Take `⟨j, rfl⟩` from `h`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩`. Consider the case `algebraMap r`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A)]`.

Conclude with `F.algebraMap_mem _`. Consider the case `add a b _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`. Consider the case `mul a b _ _ h1 h2 => rw [map_mul]`. Conclude with `mul_mem h1 h2`.

Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective A w`. Conclude with `div_mem (hA a) (hA b)`. Take `⟨θ, hθ, hθgen⟩` from `exists_integral_primitive (R := R) (E := FractionRing R) (L := FractionRing A) x hgen`. Take `⟨δ, hδ, u, v, huv⟩` from `minpoly_separable_up_to (E := FractionRing R) (L := FractionRing A) hθ`.

Use `choose b hb q hq using fun i => exists_mul_eq_aeval (E := FractionRing R) (L := FractionRing A) hθ hθgen (z i)`. Establish `: Module.IsTorsionFree R A` using `Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective R A)`. Use `⟨θ, minpoly.monic hθ, minpoly.isIntegrallyClosed_dvd_iff hθ, δ * ∏ i, b i, mul_ne_zero hδ (Finset.prod_ne_zero_iff.2 fun i _ => hb i), fun i => Polynomial.C (δ * ∏ j ∈ Finset.univ.erase i, b j) * q i, Polynomial.C (∏ i, b i) * u, Polynomial.C (∏ i, b i) * v, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.C_mul]`. Take the linear combination `Polynomial.C (∏ i, b i) * huv`.

Rewrite using `[map_mul, Polynomial.aeval_C, hq i, ← mul_assoc, ← map_mul, mul_assoc δ, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`.
-/
theorem exists_separable_presentation {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Algebra.IsAlgebraic R A]
    {n : ℕ} (x : Fin n → A) (hx : Algebra.adjoin R (Set.range x) = ⊤) {ι : Type} [Fintype ι] (z : ι → A) :
    ∃ θ : A, (minpoly R θ).Monic ∧ (∀ H : Polynomial R, Polynomial.aeval θ H = 0 ↔ minpoly R θ ∣ H) ∧
      ∃ D : R, D ≠ 0 ∧ ∃ (q : ι → Polynomial R) (u v : Polynomial R),
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C D ∧
      ∀ i, Polynomial.aeval θ (q i) = algebraMap R A D * z i := by
  classical
  have : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp (FaithfulSMul.algebraMap_injective R A))
  let : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra _ _
  have : CharZero (FractionRing R) :=
    charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hgen : IntermediateField.adjoin (FractionRing R)
      (Set.range fun j => algebraMap A (FractionRing A) (x j)) = ⊤ := by
    set F := IntermediateField.adjoin (FractionRing R) (Set.range fun j => algebraMap A (FractionRing A) (x j))
    have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈ F := by
      intro a
      have ha : a ∈ Algebra.adjoin R (Set.range x) := hx ▸ Algebra.mem_top
      induction ha using Algebra.adjoin_induction with
      | mem a h =>
        obtain ⟨j, rfl⟩ := h
        exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
      | algebraMap r =>
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A)]
        exact F.algebraMap_mem _
      | add a b _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | mul a b _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective A w
    exact div_mem (hA a) (hA b)
  obtain ⟨θ, hθ, hθgen⟩ :=
    exists_integral_primitive (R := R) (E := FractionRing R) (L := FractionRing A) x hgen
  obtain ⟨δ, hδ, u, v, huv⟩ := minpoly_separable_up_to (E := FractionRing R) (L := FractionRing A) hθ
  choose b hb q hq using fun i =>
    exists_mul_eq_aeval (E := FractionRing R) (L := FractionRing A) hθ hθgen (z i)
  have : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective R A)
  refine ⟨θ, minpoly.monic hθ, minpoly.isIntegrallyClosed_dvd_iff hθ, δ * ∏ i, b i, mul_ne_zero hδ (Finset.prod_ne_zero_iff.2 fun i _ => hb i),
    fun i => Polynomial.C (δ * ∏ j ∈ Finset.univ.erase i, b j) * q i,
    Polynomial.C (∏ i, b i) * u, Polynomial.C (∏ i, b i) * v, ?_, fun i => ?_⟩
  · rw [Polynomial.C_mul]
    linear_combination Polynomial.C (∏ i, b i) * huv
  · rw [map_mul, Polynomial.aeval_C, hq i, ← mul_assoc, ← map_mul, mul_assoc δ,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/- English proof (translation)
Establish `: Algebra.IsAlgebraic (Algebra.adjoin S (Set.range x)) A` using `⟨fun a => by`. Establish `ha : a ∈ Algebra.adjoin S (Set.range x)` using `hx ▸ Algebra.mem_top`. Conclude with `isAlgebraic_algebraMap (R := Algebra.adjoin S (Set.range x)) (A := A) ⟨a, ha⟩⟩`. Take `⟨t, ht, hb⟩` from `exists_isTranscendenceBasis_subset (R := S) (Set.range x)`. Establish `: Finite t` using `((Set.finite_range x).subset ht).to_subtype`.

Conclude with `⟨_, _, hb.comp_equiv (Finite.equivFin t).symm⟩`.
-/
theorem exists_transcendenceBasis_fin {S A : Type} [CommRing S] [CommRing A] [IsDomain A] [Algebra S A]
    [FaithfulSMul S A] {ι : Type} [Finite ι] (x : ι → A) (hx : Algebra.adjoin S (Set.range x) = ⊤) :
    ∃ (d : ℕ) (y : Fin d → A), IsTranscendenceBasis S y := by
  have : Algebra.IsAlgebraic (Algebra.adjoin S (Set.range x)) A := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin S (Set.range x) := hx ▸ Algebra.mem_top
    exact isAlgebraic_algebraMap (R := Algebra.adjoin S (Set.range x)) (A := A) ⟨a, ha⟩⟩
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := S) (Set.range x)
  have : Finite t := ((Set.finite_range x).subset ht).to_subtype
  exact ⟨_, _, hb.comp_equiv (Finite.equivFin t).symm⟩

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin d) S) A` to `(MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra`. Use `hb.isAlgebraic` as an intermediate fact. Establish `h : (algebraMap (MvPolynomial (Fin d) S) A).comp (hb.1.aevalEquiv.symm : _ →+* _) = (RingHom.id A).comp (algebraMap (Algebra.adjoin S (Set.range y)) A)` using `RingHom.ext fun z => by show MvPolynomial.aeval y (hb.1.aevalEquiv.symm z) = (z : A)`. Rewrite using `[← hb.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Conclude with `⟨fun a => (isAlgebraic_ringHom_iff_of_comp_eq hb.1.aevalEquiv.symm (RingHom.id A) Function.injective_id h).2 (Algebra.IsAlgebraic.isAlgebraic a)⟩`.
-/
theorem isAlgebraic_aeval_of_isTranscendenceBasis {S A : Type} [CommRing S] [Nontrivial S] [CommRing A]
    [Algebra S A] {d : ℕ} {y : Fin d → A} (hb : IsTranscendenceBasis S y) :
    letI := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
    Algebra.IsAlgebraic (MvPolynomial (Fin d) S) A := by
  let _ : Algebra (MvPolynomial (Fin d) S) A := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
  have := hb.isAlgebraic
  have h : (algebraMap (MvPolynomial (Fin d) S) A).comp (hb.1.aevalEquiv.symm : _ →+* _) =
      (RingHom.id A).comp (algebraMap (Algebra.adjoin S (Set.range y)) A) := RingHom.ext fun z => by
    show MvPolynomial.aeval y (hb.1.aevalEquiv.symm z) = (z : A)
    rw [← hb.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
    rfl
  exact ⟨fun a => (isAlgebraic_ringHom_iff_of_comp_eq hb.1.aevalEquiv.symm (RingHom.id A)
    Function.injective_id h).2 (Algebra.IsAlgebraic.isAlgebraic a)⟩

end Generic

section Main

variable {σ ι : Type} [Finite σ] [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) [K.IsPrime]

local notation "𝔸" => MvPolynomial ι (MvPolynomial σ ℂ) ⧸ K

omit [Finite σ] in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Establish `hmkC : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial σ ℂ) 𝔸 s` using `fun s => rfl`. Establish `hSinj : Function.Injective (algebraMap (MvPolynomial σ ℂ) 𝔸)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `s hs`.

Rewrite `hs` using `[← hmkC, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hKS s hs`. Establish `: FaithfulSMul (MvPolynomial σ ℂ) 𝔸` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hSinj`. Set `x : ι → 𝔸` to `fun i => Ideal.Quotient.mk K (X i)`. Establish `hadj : Algebra.adjoin (MvPolynomial σ ℂ) (Set.range x) = ⊤`.

Use `eq_top_iff.2 fun a _ => ?_` and prove the remaining obligations. Use `clear ‹a ∈ ⊤›`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C s => rw [hmkC]`.

Conclude with `Subalgebra.algebraMap_mem _ s`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp => rw [map_mul]`. Conclude with `mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)`.

Take `⟨d, yA, hbd⟩` from `exists_transcendenceBasis_fin x hadj`. Set `: Algebra (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸` to `(MvPolynomial.aeval yA).toRingHom.toAlgebra`. Establish `hmap : ∀ r, algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r = MvPolynomial.aeval yA r` using `fun _ => rfl`. Establish `hRinj : Function.Injective (algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸)` using `fun a b h => algebraicIndependent_iff_injective_aeval.1 hbd.1 (by rwa [hmap, hmap] at h)`. Establish `: FaithfulSMul (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hRinj`.

Establish `: Algebra.IsAlgebraic (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸` using `isAlgebraic_aeval_of_isTranscendenceBasis hbd`. Establish `hmkCR : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 (C s)` using `fun s => by`. Rewrite using `[hmkC]`. Use `show _ = MvPolynomial.aeval yA (C s)`. Rewrite using `[MvPolynomial.aeval_C]`.

Set `eι` to `Finite.equivFin ι`. Establish `hadjR : Algebra.adjoin (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (Set.range fun j => x (eι.symm j)) = ⊤`. Use `eq_top_iff.2 fun a _ => ?_` and prove the remaining obligations. Use `clear ‹a ∈ ⊤›`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C s => rw [hmkCR]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`. Conclude with `mul_mem hp (Algebra.subset_adjoin ⟨eι i, by simp [x]⟩)`. Take `⟨θA, hmon, hker, D, hD, q, u, v, huv, hq⟩` from `exists_separable_presentation (R := MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (fun j => x (eι.symm j)) hadjR x`. Use `choose y hy using fun j => Ideal.Quotient.mk_surjective (yA j)`.

Take `⟨θ, hθmk⟩` from `Ideal.Quotient.mk_surjective θA`. Establish `hcompA : (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) K).comp (aeval y) = MvPolynomial.aeval yA` using `MvPolynomial.algHom_ext fun j => by`. Rewrite using `[AlgHom.comp_apply, aeval_X, aeval_X, Ideal.Quotient.mkₐ_eq_mk, hy]`. Establish `hcomp : ∀ r, Ideal.Quotient.mk K (aeval y r) = algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r` using `fun r => by`. Rewrite using `[hmap, ← hcompA, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`.

Establish `heval : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)), Ideal.Quotient.mk K (Polynomial.eval₂ (aeval y).toRingHom θ H) = Polynomial.aeval θA H`. Introduce `H`. Rewrite using `[Polynomial.hom_eval₂, hθmk, Polynomial.aeval_def]`. Use `congr 1`. Conclude with `RingHom.ext hcomp`.

Use `⟨d, y, θ, minpoly (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) θA, D, q, u, v, hmon, hD, huv, fun H => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, heval]`. Conclude with `hker H`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, heval, hcomp, hq i, sub_eq_zero]`.
-/
theorem hypersurfacePresentation_of (hKS : ∀ s : MvPolynomial σ ℂ, C s ∈ K → s = 0) :
    ∃ (d : ℕ) (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
      (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
      (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
      (u v : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      m.Monic ∧ D ≠ 0 ∧ u * m + v * Polynomial.derivative m = Polynomial.C D ∧
      (∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
        Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H) ∧
      ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K := by
  classical
  have := Fintype.ofFinite ι
  have hmkC : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial σ ℂ) 𝔸 s := fun s => rfl
  have hSinj : Function.Injective (algebraMap (MvPolynomial σ ℂ) 𝔸) := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    rw [← hmkC, Ideal.Quotient.eq_zero_iff_mem] at hs
    exact hKS s hs
  have : FaithfulSMul (MvPolynomial σ ℂ) 𝔸 := (faithfulSMul_iff_algebraMap_injective _ _).2 hSinj
  let x : ι → 𝔸 := fun i => Ideal.Quotient.mk K (X i)
  have hadj : Algebra.adjoin (MvPolynomial σ ℂ) (Set.range x) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    clear ‹a ∈ ⊤›
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C s => rw [hmkC]; exact Subalgebra.algebraMap_mem _ s
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  obtain ⟨d, yA, hbd⟩ := exists_transcendenceBasis_fin x hadj

  let : Algebra (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 := (MvPolynomial.aeval yA).toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r = MvPolynomial.aeval yA r :=
    fun _ => rfl
  have hRinj : Function.Injective (algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸) := fun a b h =>
    algebraicIndependent_iff_injective_aeval.1 hbd.1 (by rwa [hmap, hmap] at h)
  have : FaithfulSMul (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hRinj
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 :=
    isAlgebraic_aeval_of_isTranscendenceBasis hbd
  have hmkCR : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 (C s) :=
    fun s => by
      rw [hmkC]
      show _ = MvPolynomial.aeval yA (C s)
      rw [MvPolynomial.aeval_C]
  let eι := Finite.equivFin ι
  have hadjR : Algebra.adjoin (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (Set.range fun j => x (eι.symm j)) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    clear ‹a ∈ ⊤›
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C s => rw [hmkCR]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨eι i, by simp [x]⟩)
  obtain ⟨θA, hmon, hker, D, hD, q, u, v, huv, hq⟩ :=
    exists_separable_presentation (R := MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (fun j => x (eι.symm j)) hadjR x

  choose y hy using fun j => Ideal.Quotient.mk_surjective (yA j)
  obtain ⟨θ, hθmk⟩ := Ideal.Quotient.mk_surjective θA
  have hcompA : (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) K).comp (aeval y) = MvPolynomial.aeval yA :=
    MvPolynomial.algHom_ext fun j => by
      rw [AlgHom.comp_apply, aeval_X, aeval_X, Ideal.Quotient.mkₐ_eq_mk, hy]
  have hcomp : ∀ r, Ideal.Quotient.mk K (aeval y r) =
      algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r := fun r => by
    rw [hmap, ← hcompA, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have heval : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Ideal.Quotient.mk K (Polynomial.eval₂ (aeval y).toRingHom θ H) = Polynomial.aeval θA H := by
    intro H
    rw [Polynomial.hom_eval₂, hθmk, Polynomial.aeval_def]
    congr 1
    exact RingHom.ext hcomp
  refine ⟨d, y, θ, minpoly (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) θA, D, q, u, v, hmon, hD, huv,
    fun H => ?_, fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, heval]
    exact hker H
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, heval, hcomp, hq i, sub_eq_zero]

end Main

end HypersurfacePresentation

/- English proof (translation)
Introduce `σ _ ι _ K hK hKS`. Conclude with `HypersurfacePresentation.hypersurfacePresentation_of K hKS`.
-/
theorem HypersurfacePresentation.proof : HypersurfacePresentation.Statement := by
  intro σ _ ι _ K hK hKS
  exact HypersurfacePresentation.hypersurfacePresentation_of K hKS

end

end GroundTheory.Heights₂.Heights
