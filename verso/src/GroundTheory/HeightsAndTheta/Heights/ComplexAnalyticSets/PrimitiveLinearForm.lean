import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial TensorProduct

noncomputable section

namespace PrimitiveLinearForm

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]

abbrev tensorRightAlgebra : Algebra B (FractionRing R ⊗[R] B) := Algebra.TensorProduct.rightAlgebra

attribute [local instance] tensorRightAlgebra

/- English proof (translation)
Use `isLocalizedModule_iff_isLocalization.mp ?_` and prove the remaining obligations. Establish `h` using `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) (FractionRing R) (IsScalarTower.toAlgHom R B (FractionRing R ⊗[R] B)).toLinearMap).mpr ?_`. Conclude with `h`. Conclude with `TensorProduct.isBaseChange R B (FractionRing R)`.
-/
theorem isLocalization_tensor :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (FractionRing R ⊗[R] B) := by
  refine isLocalizedModule_iff_isLocalization.mp ?_
  have h := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) (FractionRing R)
    (IsScalarTower.toAlgHom R B (FractionRing R ⊗[R] B)).toLinearMap).mpr ?_
  · exact h
  · exact TensorProduct.isBaseChange R B (FractionRing R)

/- English proof (translation)
Set `A` to `AlgebraicClosure K`. Set `ι' : ℂ →+* A` to `(algebraMap K A).comp ι`. Set `p : (L →ₐ[K] A) × (L →ₐ[K] A) → Polynomial A` to `fun φψ => ∑ j : Fin n, Polynomial.monomial (j : ℕ) (φψ.1 (x j) - φψ.2 (x j))`. Establish `hp : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), φψ.1 ≠ φψ.2 → p φψ ≠ 0`. Introduce `φψ hne h`.

Apply `hne` to reduce the goal to its premises. Apply `hx` to reduce the goal to its premises. Introduce `j`. Establish `hc` using `congrArg (fun q => Polynomial.coeff q (j : ℕ)) h`. Simplify using `only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc`.

Rewrite `hc` using `[Finset.sum_eq_single j]`. Simplify `hc` using `[sub_eq_zero]`. Introduce `b _ hb`. Rewrite using `[if_neg]`. Conclude with `fun h => hb (Fin.ext h)`.

Simplify using the standard rewrite rules. Establish `hev : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), ∀ t : A, (p φψ).eval t = ∑ j : Fin n, (φψ.1 (x j) - φψ.2 (x j)) * t ^ (j : ℕ)`. Introduce `φψ t`. Simplify using `only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]`. Set `S : Finset A` to `(Finset.univ.filter (fun φψ : (L →ₐ[K] A) × (L →ₐ[K] A) => φψ.1 ≠ φψ.2)).biUnion (fun φψ => (p φψ).roots.toFinset)`.

Establish `hSf : {t : ℂ | ι' t ∈ S}.Finite` using `(S.finite_toSet.preimage (ι'.injective.injOn))`. Take `⟨t, ht⟩` from `hSf.infinite_compl.nonempty`. Use `⟨fun j => t ^ (j : ℕ), ?_⟩` and prove the remaining obligations. Establish `hA : ∀ y : L, ((minpoly K y).map (algebraMap K A)).Splits` using `fun y => IsAlgClosed.splits _`. Rewrite using `[Field.primitive_element_iff_algHom_eq_of_eval' K A hA]`.

Introduce `φ ψ hφψ`. Assume the negation of the conclusion as `hne`. Apply `ht` to reduce the goal to its premises. Simplify using `only [Set.mem_ofPred_eq, S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨(φ, ψ), hne, ?_⟩` and prove the remaining obligations.

Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots (hp (φ, ψ) hne), Polynomial.IsRoot, hev]`. Establish `h1 : ∀ χ : L →ₐ[K] A, χ (∑ j : Fin n, algebraMap K L (ι (t ^ (j : ℕ))) * x j) = ∑ j : Fin n, ι' t ^ (j : ℕ) * χ (x j)`. Introduce `χ`. Simplify using `[map_sum, map_mul, AlgHom.commutes, ι', map_pow]`. Establish `h2` using `congrArg id hφψ`.

Simplify using `only [id] at h2`. Rewrite `h2` using `[h1, h1]`. Rewrite `h2` using `[← sub_eq_zero]`. Rewrite using `[← h2, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem exists_linear_primitive {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {n : ℕ} (ι : ℂ →+* K) (x : Fin n → L)
    (hx : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K, (∀ j, φ (x j) = ψ (x j)) → φ = ψ) :
    ∃ c : Fin n → ℂ, IntermediateField.adjoin K {∑ j, algebraMap K L (ι (c j)) * x j} = ⊤ := by
  classical
  let A := AlgebraicClosure K
  let ι' : ℂ →+* A := (algebraMap K A).comp ι
  let p : (L →ₐ[K] A) × (L →ₐ[K] A) → Polynomial A := fun φψ =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (φψ.1 (x j) - φψ.2 (x j))
  have hp : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), φψ.1 ≠ φψ.2 → p φψ ≠ 0 := by
    intro φψ hne h
    apply hne
    apply hx
    intro j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · simp
  have hev : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), ∀ t : A,
      (p φψ).eval t = ∑ j : Fin n, (φψ.1 (x j) - φψ.2 (x j)) * t ^ (j : ℕ) := by
    intro φψ t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  let S : Finset A := (Finset.univ.filter (fun φψ : (L →ₐ[K] A) × (L →ₐ[K] A) => φψ.1 ≠ φψ.2)).biUnion
    (fun φψ => (p φψ).roots.toFinset)
  have hSf : {t : ℂ | ι' t ∈ S}.Finite :=
    (S.finite_toSet.preimage (ι'.injective.injOn))
  obtain ⟨t, ht⟩ := hSf.infinite_compl.nonempty
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  have hA : ∀ y : L, ((minpoly K y).map (algebraMap K A)).Splits := fun y => IsAlgClosed.splits _
  rw [Field.primitive_element_iff_algHom_eq_of_eval' K A hA]
  intro φ ψ hφψ
  by_contra hne
  apply ht
  simp only [Set.mem_ofPred_eq, S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(φ, ψ), hne, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp (φ, ψ) hne), Polynomial.IsRoot, hev]
  have h1 : ∀ χ : L →ₐ[K] A, χ (∑ j : Fin n, algebraMap K L (ι (t ^ (j : ℕ))) * x j) =
      ∑ j : Fin n, ι' t ^ (j : ℕ) * χ (x j) := by
    intro χ
    simp [map_sum, map_mul, AlgHom.commutes, ι', map_pow]
  have h2 := congrArg id hφψ
  simp only [id] at h2
  rw [h1, h1] at h2
  rw [← sub_eq_zero] at h2
  rw [← h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Set `K` to `FractionRing R`. Set `L` to `K ⊗[R] B`. Set `_ : Algebra B L` to `Algebra.TensorProduct.rightAlgebra`. Establish `: IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) L` using `isLocalization_tensor R B`. Establish `hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors R) ≤ nonZeroDivisors B`.

Introduce and unpack `_ ⟨r, hr, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero (fun h => nonZeroDivisors.ne_zero hr (hinj (by rw [h, map_zero])))`. Establish `: IsDomain L` using `IsLocalization.isDomain_of_le_nonZeroDivisors L hM`. Establish `hBL : Function.Injective (algebraMap B L)` using `IsLocalization.injective L hM`. Establish `: Algebra.IsIntegral K L` using `Algebra.IsIntegral.of_finite K L`.

Set `_ : Field L` to `(isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)).toField`. Set `ιK : ℂ →+* K` to `(algebraMap R K).comp ι`. Establish `: CharZero K` using `⟨fun a b h => by`. Establish `h' : ιK (a : ℂ) = ιK (b : ℂ)` using `by simpa [map_natCast] using h`. Conclude with `ιK.injective h'⟩` after adjusting the coercions.

Establish `: Algebra.IsSeparable K L` using `Algebra.IsAlgebraic.isSeparable_of_perfectField`. Establish `hxgen : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K, (∀ j, φ (algebraMap B L (x j)) = ψ (algebraMap B L (x j))) → φ = ψ`. Introduce `φ ψ h`. Establish `h1 : (φ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) = (ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L)`. Apply `AlgHom.ext_of_adjoin_eq_top hx` to reduce the goal to its premises.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `h j`. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))` to reduce the goal to its premises. Conclude with `RingHom.ext fun b => AlgHom.congr_fun h1 b`.

Take `⟨c, hc⟩` from `exists_linear_primitive ιK (fun j => algebraMap B L (x j)) hxgen`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `set ℓ : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓ`. Establish `hℓL : algebraMap B L ℓ = ∑ j, algebraMap K L (ιK (c j)) * algebraMap B L (x j)`. Rewrite using `[hℓ, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]`. Both sides reduce to the same expression. Rewrite `hc` using `[← hℓL]`. Establish `: Algebra.IsIntegral R B` using `Algebra.IsIntegral.of_finite R B`.

Establish `hint : IsIntegral R ℓ` using `Algebra.IsIntegral.isIntegral ℓ`. Establish `hmK : minpoly K (algebraMap B L ℓ) = (minpoly R ℓ).map (algebraMap R K)` using `minpoly.isIntegrallyClosed_eq_field_fractions K L hint`. Establish `hdeg : (minpoly R ℓ).natDegree = Module.finrank K L`. Rewrite using `[← (minpoly.monic hint).natDegree_map (algebraMap R K), ← hmK]`. Conclude with `(Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hc`.

Establish `: Module.IsTorsionFree R B` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hinj`. Establish `hdiv : ∀ p : R[X], aeval ℓ p = 0 ↔ minpoly R ℓ ∣ p` using `fun p => ⟨minpoly.isIntegrallyClosed_dvd hint, fun ⟨q, hq⟩ => by rw [hq, map_mul, minpoly.aeval, zero_mul]⟩`. Establish `hirr : Irreducible ((minpoly R ℓ).map (algebraMap R K))` using `hmK ▸ minpoly.irreducible (IsIntegral.of_finite K _)`. Establish `hsep : IsCoprime ((minpoly R ℓ).map (algebraMap R K)) (derivative ((minpoly R ℓ).map (algebraMap R K)))` using `hirr.separable`. Take `⟨a, b, hab⟩` from `hsep`.

Rewrite `hab` using `[Polynomial.derivative_map]`. Take `⟨α, hα, hαa⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) a`. Take `⟨β, hβ, hβb⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) b`. Establish `hinjK : Function.Injective (Polynomial.map (algebraMap R K))` using `Polynomial.map_injective _ (IsFractionRing.injective R K)`. Establish `hid : C β * IsLocalization.integerNormalization (nonZeroDivisors R) a * minpoly R ℓ + C α * IsLocalization.integerNormalization (nonZeroDivisors R) b * derivative (minpoly R ℓ) = C (α * β)`.

Apply `hinjK` to reduce the goal to its premises. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hαa, hβb, Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]`. Take the linear combination `(C (algebraMap R K α) * C (algebraMap R K β)) * hab`. Establish `hmem : ∀ j, ∃ P : K[X], aeval (algebraMap B L ℓ) P = algebraMap B L (x j)`. Introduce `j`.

Establish `h1 : algebraMap B L (x j) ∈ (IntermediateField.adjoin K {algebraMap B L ℓ}).toSubalgebra`. Rewrite using `[hc]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `h1` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨P, hP⟩` from `h1`.

Conclude with `⟨P, hP⟩`. Use `choose P hP using hmem`. Establish `hclear : ∀ j, ∃ e ∈ nonZeroDivisors R, ∃ P' : R[X], aeval ℓ P' = algebraMap R B e * x j`. Introduce `j`. Take `⟨e, he, hPe⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) (P j)`.

Use `⟨e, he, IsLocalization.integerNormalization (nonZeroDivisors R) (P j), hBL ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap K, hPe, Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.aeval_C, hP j, map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]`. Use `choose e he Q' hQ' using hclear`. Use `⟨minpoly R ℓ, α * β * ∏ j, e j, fun j => C (α * β * ∏ k ∈ Finset.univ.erase j, e k) * Q' j, minpoly.monic hint, hdeg, hdiv, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hα) (nonZeroDivisors.ne_zero hβ)) ?_` and prove the remaining obligations.

Conclude with `Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.ne_zero (he j)`. Use `⟨C (∏ j, e j) * (C β * IsLocalization.integerNormalization (nonZeroDivisors R) a), C (∏ j, e j) * (C α * IsLocalization.integerNormalization (nonZeroDivisors R) b), ?_⟩` and prove the remaining obligations. Rewrite using `[C_mul (a := α * β)]`. Take the linear combination `C (∏ j, e j) * hid`. Introduce `j`.

Rewrite using `[map_mul (aeval ℓ), Polynomial.aeval_C, hQ' j, ← Finset.mul_prod_erase Finset.univ e (Finset.mem_univ j)]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_primitive_data {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) (ι : ℂ →+* R) {n : ℕ} (x : Fin n → B)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    ∃ (c : Fin n → ℂ) (m : R[X]) (D : R) (Q : Fin n → R[X]),
      m.Monic ∧ m.natDegree = Module.finrank (FractionRing R) (FractionRing R ⊗[R] B) ∧
      (∀ p : R[X], aeval (∑ j, algebraMap R B (ι (c j)) * x j) p = 0 ↔ m ∣ p) ∧
      D ≠ 0 ∧ (∃ a b : R[X], a * m + b * derivative m = C D) ∧
      ∀ j, algebraMap R B D * x j = aeval (∑ j, algebraMap R B (ι (c j)) * x j) (Q j) := by
  classical
  let K := FractionRing R
  let L := K ⊗[R] B
  let _ : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) L :=
    isLocalization_tensor R B
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors R) ≤ nonZeroDivisors B := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hr (hinj (by rw [h, map_zero])))
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L hM
  have hBL : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  let _ : Field L := (isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)).toField
  let ιK : ℂ →+* K := (algebraMap R K).comp ι
  have : CharZero K := ⟨fun a b h => by
    have h' : ιK (a : ℂ) = ιK (b : ℂ) := by simpa [map_natCast] using h
    exact_mod_cast ιK.injective h'⟩
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hxgen : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K,
      (∀ j, φ (algebraMap B L (x j)) = ψ (algebraMap B L (x j))) → φ = ψ := by
    intro φ ψ h
    have h1 : (φ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) =
        (ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) := by
      apply AlgHom.ext_of_adjoin_eq_top hx
      rintro _ ⟨j, rfl⟩
      exact h j
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
    exact RingHom.ext fun b => AlgHom.congr_fun h1 b
  obtain ⟨c, hc⟩ := exists_linear_primitive ιK (fun j => algebraMap B L (x j)) hxgen
  refine ⟨c, ?_⟩
  set ℓ : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓ
  have hℓL : algebraMap B L ℓ = ∑ j, algebraMap K L (ιK (c j)) * algebraMap B L (x j) := by
    rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
    rfl
  rw [← hℓL] at hc
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hint : IsIntegral R ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hmK : minpoly K (algebraMap B L ℓ) = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    rw [← (minpoly.monic hint).natDegree_map (algebraMap R K), ← hmK]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hc
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hdiv : ∀ p : R[X], aeval ℓ p = 0 ↔ minpoly R ℓ ∣ p := fun p =>
    ⟨minpoly.isIntegrallyClosed_dvd hint, fun ⟨q, hq⟩ => by rw [hq, map_mul, minpoly.aeval, zero_mul]⟩

  have hirr : Irreducible ((minpoly R ℓ).map (algebraMap R K)) :=
    hmK ▸ minpoly.irreducible (IsIntegral.of_finite K _)
  have hsep : IsCoprime ((minpoly R ℓ).map (algebraMap R K))
      (derivative ((minpoly R ℓ).map (algebraMap R K))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  rw [Polynomial.derivative_map] at hab
  obtain ⟨α, hα, hαa⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨β, hβ, hβb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  have hinjK : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective R K)
  have hid : C β * IsLocalization.integerNormalization (nonZeroDivisors R) a * minpoly R ℓ +
      C α * IsLocalization.integerNormalization (nonZeroDivisors R) b * derivative (minpoly R ℓ) =
      C (α * β) := by
    apply hinjK
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hαa, hβb,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R K α) * C (algebraMap R K β)) * hab

  have hmem : ∀ j, ∃ P : K[X], aeval (algebraMap B L ℓ) P = algebraMap B L (x j) := by
    intro j
    have h1 : algebraMap B L (x j) ∈ (IntermediateField.adjoin K {algebraMap B L ℓ}).toSubalgebra := by
      rw [hc]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨P, hP⟩ := h1
    exact ⟨P, hP⟩
  choose P hP using hmem
  have hclear : ∀ j, ∃ e ∈ nonZeroDivisors R, ∃ P' : R[X], aeval ℓ P' = algebraMap R B e * x j := by
    intro j
    obtain ⟨e, he, hPe⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) (P j)
    refine ⟨e, he, IsLocalization.integerNormalization (nonZeroDivisors R) (P j), hBL ?_⟩
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap K, hPe,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.aeval_C, hP j, map_mul,
      ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
  choose e he Q' hQ' using hclear
  refine ⟨minpoly R ℓ, α * β * ∏ j, e j,
    fun j => C (α * β * ∏ k ∈ Finset.univ.erase j, e k) * Q' j, minpoly.monic hint, hdeg, hdiv,
    ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hα) (nonZeroDivisors.ne_zero hβ)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.ne_zero (he j)
  · refine ⟨C (∏ j, e j) * (C β * IsLocalization.integerNormalization (nonZeroDivisors R) a),
      C (∏ j, e j) * (C α * IsLocalization.integerNormalization (nonZeroDivisors R) b), ?_⟩
    rw [C_mul (a := α * β)]
    linear_combination C (∏ j, e j) * hid
  · intro j
    rw [map_mul (aeval ℓ), Polynomial.aeval_C, hQ' j, ← Finset.mul_prod_erase Finset.univ e
      (Finset.mem_univ j)]
    simp only [map_mul]
    ring

end PrimitiveLinearForm

end

end GroundTheory.Heights₂.Heights.ComplexSets
