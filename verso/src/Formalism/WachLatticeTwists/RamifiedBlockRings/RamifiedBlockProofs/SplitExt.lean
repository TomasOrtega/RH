import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SpacedProductLowerBound

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG

/- English proof (translation)
Assume the negation of the conclusion as `hnl`. Take `⟨M₁, M₂, hM₁, hM₂, hne⟩` from `(IsLocalRing.not_isLocalRing_tfae.out 0 2).mp hnl`. Set `m` to `IsLocalRing.maximalIdeal O`. Set `I : Ideal A` to `m.map (algebraMap O A)`. Establish `hIM : ∀ M : Ideal A, M.IsMaximal → I ≤ M`.

Introduce `M hM`. Establish `h1 : (M.comap (algebraMap O A)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Conclude with `Ideal.map_le_iff_le_comap.mpr (le_of_eq (IsLocalRing.eq_maximalIdeal h1).symm)`. Establish `hart : IsArtinianRing (A ⧸ I)`. Set `: Field (O ⧸ m)` to `Ideal.Quotient.field m`.

Set `: Algebra (O ⧸ m) (A ⧸ I)` to `Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map`. Establish `: IsScalarTower O (O ⧸ m) (A ⧸ I)` using `IsScalarTower.of_algebraMap_eq fun x => rfl`. Establish `: Module.Finite (O ⧸ m) (A ⧸ I)` using `Module.Finite.of_restrictScalars_finite O _ _`. Conclude with `IsArtinianRing.of_finite (O ⧸ m) (A ⧸ I)`. Set `q : A →+* A ⧸ I` to `Ideal.Quotient.mk I`.

Establish `hq : Function.Surjective q` using `Ideal.Quotient.mk_surjective`. Establish `hmax : ∀ M : Ideal A, M.IsMaximal → (M.map q).IsMaximal ∧ (M.map q).comap q = M`. Introduce `M hM`. Establish `h1 : (M.map q).comap q = M`. Rewrite using `[Ideal.comap_map_of_surjective q hq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`.

Conclude with `sup_eq_left.mpr (hIM M hM)`. Use `⟨(Ideal.map_eq_top_or_isMaximal_of_surjective q hq hM).resolve_left fun h => ?_, h1⟩` and prove the remaining obligations. Rewrite `h1` using `[h, Ideal.comap_top]`. Conclude with `hM.ne_top h1.symm`. Set `J₁ : MaximalSpectrum (A ⧸ I)` to `⟨M₁.map q, (hmax M₁ hM₁).1⟩`.

Set `J₂ : MaximalSpectrum (A ⧸ I)` to `⟨M₂.map q, (hmax M₂ hM₂).1⟩`. Establish `hJ : J₁ ≠ J₂`. Introduce `h`. Establish `h1 : M₁.map q = M₂.map q` using `congrArg MaximalSpectrum.asIdeal h`. Conclude with `hne (by rw [← (hmax M₁ hM₁).2, h1, (hmax M₂ hM₂).2])`.

Set `φ` to `IsArtinianRing.quotNilradicalEquivPi (A ⧸ I)`. Set `f : A →+* (A ⧸ I) ⧸ nilradical (A ⧸ I)` to `(Ideal.Quotient.mk _).comp q`. Establish `hf : Function.Surjective f` using `Ideal.Quotient.mk_surjective.comp hq`. Establish `hker : ∀ x : A, f x = 0 → ∃ n : ℕ, x ^ n ∈ m • (⊤ : Submodule O A)`. Introduce `x hx`.

Establish `h1 : q x ∈ nilradical (A ⧸ I)` using `Ideal.Quotient.eq_zero_iff_mem.mp hx`. Take `⟨n, hn⟩` from `mem_nilradical.mp h1`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_pow]; exact hn)`.

Set `u : ∀ J : MaximalSpectrum (A ⧸ I), (A ⧸ I) ⧸ J.asIdeal` to `Pi.single J₁ 1`. Establish `hu : u * u = u`. Use function extensionality and compare the values at `J`. Distinguish the cases in `h : J = J₁`. Substitute `h` using the available equality.

Simplify using `[u]`. Simplify using `[u, Pi.single_eq_of_ne h]`. Take `⟨E, -, hE, -, -, -, hfE, -⟩` from `idemLift O A _ f hf hker (φ.symm u) 0 (by show φ.symm u * φ.symm u = φ.symm u; rw [← map_mul, hu]) (IsIdempotentElem.zero) (mul_zero _) (zero_mul _)`. Establish `hφ : φ (f E) = u` using `by rw [hfE]; exact φ.apply_symm_apply u`. Break down `(IsIdempotentElem.iff_eq_zero_or_one.mp hE) with h0 | h1` into its components or cases.

Rewrite `hφ` using `[h0, map_zero, map_zero]`. Establish `h2` using `congrFun hφ J₁`. Establish `: Nontrivial ((A ⧸ I) ⧸ J₁.asIdeal)` using `Ideal.Quotient.nontrivial_iff.mpr J₁.isMaximal.ne_top`. Simplify using `[u] at h2`. Rewrite `hφ` using `[h1, map_one, map_one]`.

Establish `h2` using `congrFun hφ J₂`. Establish `: Nontrivial ((A ⧸ I) ⧸ J₂.asIdeal)` using `Ideal.Quotient.nontrivial_iff.mpr J₂.isMaximal.ne_top`. Simplify using `[u, Pi.single_eq_of_ne (Ne.symm hJ)] at h2`.
-/
theorem local_of_complete (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CommRing A] [IsDomain A] [Algebra O A]
    [Module.Finite O A] : IsLocalRing A := by
  by_contra hnl
  obtain ⟨M₁, M₂, hM₁, hM₂, hne⟩ := (IsLocalRing.not_isLocalRing_tfae.out 0 2).mp hnl
  let m := IsLocalRing.maximalIdeal O
  let I : Ideal A := m.map (algebraMap O A)
  have hIM : ∀ M : Ideal A, M.IsMaximal → I ≤ M := by
    intro M hM
    have h1 : (M.comap (algebraMap O A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact Ideal.map_le_iff_le_comap.mpr (le_of_eq (IsLocalRing.eq_maximalIdeal h1).symm)
  have hart : IsArtinianRing (A ⧸ I) := by
    let : Field (O ⧸ m) := Ideal.Quotient.field m
    let : Algebra (O ⧸ m) (A ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have : IsScalarTower O (O ⧸ m) (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun x => rfl
    have : Module.Finite (O ⧸ m) (A ⧸ I) := Module.Finite.of_restrictScalars_finite O _ _
    exact IsArtinianRing.of_finite (O ⧸ m) (A ⧸ I)
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hmax : ∀ M : Ideal A, M.IsMaximal → (M.map q).IsMaximal ∧ (M.map q).comap q = M := by
    intro M hM
    have h1 : (M.map q).comap q = M := by
      rw [Ideal.comap_map_of_surjective q hq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr (hIM M hM)
    refine ⟨(Ideal.map_eq_top_or_isMaximal_of_surjective q hq hM).resolve_left fun h => ?_, h1⟩
    rw [h, Ideal.comap_top] at h1
    exact hM.ne_top h1.symm
  let J₁ : MaximalSpectrum (A ⧸ I) := ⟨M₁.map q, (hmax M₁ hM₁).1⟩
  let J₂ : MaximalSpectrum (A ⧸ I) := ⟨M₂.map q, (hmax M₂ hM₂).1⟩
  have hJ : J₁ ≠ J₂ := by
    intro h
    have h1 : M₁.map q = M₂.map q := congrArg MaximalSpectrum.asIdeal h
    exact hne (by rw [← (hmax M₁ hM₁).2, h1, (hmax M₂ hM₂).2])
  let φ := IsArtinianRing.quotNilradicalEquivPi (A ⧸ I)
  let f : A →+* (A ⧸ I) ⧸ nilradical (A ⧸ I) := (Ideal.Quotient.mk _).comp q
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hq
  have hker : ∀ x : A, f x = 0 → ∃ n : ℕ, x ^ n ∈ m • (⊤ : Submodule O A) := by
    intro x hx
    have h1 : q x ∈ nilradical (A ⧸ I) := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨n, hn⟩ := mem_nilradical.mp h1
    refine ⟨n, ?_⟩
    rw [Ideal.smul_top_eq_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_pow]; exact hn)
  let u : ∀ J : MaximalSpectrum (A ⧸ I), (A ⧸ I) ⧸ J.asIdeal := Pi.single J₁ 1
  have hu : u * u = u := by
    funext J
    by_cases h : J = J₁
    · subst h; simp [u]
    · simp [u, Pi.single_eq_of_ne h]
  obtain ⟨E, -, hE, -, -, -, hfE, -⟩ := idemLift O A _ f hf hker (φ.symm u) 0
    (by show φ.symm u * φ.symm u = φ.symm u; rw [← map_mul, hu]) (IsIdempotentElem.zero)
    (mul_zero _) (zero_mul _)
  have hφ : φ (f E) = u := by rw [hfE]; exact φ.apply_symm_apply u
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hE) with h0 | h1
  · rw [h0, map_zero, map_zero] at hφ
    have h2 := congrFun hφ J₁
    have : Nontrivial ((A ⧸ I) ⧸ J₁.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr J₁.isMaximal.ne_top
    simp [u] at h2
  · rw [h1, map_one, map_one] at hφ
    have h2 := congrFun hφ J₂
    have : Nontrivial ((A ⧸ I) ⧸ J₂.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr J₂.isMaximal.ne_top
    simp [u, Pi.single_eq_of_ne (Ne.symm hJ)] at h2

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible O'`. Establish `hφϖ0 : algebraMap O O' ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))`. Establish `hφϖnu : ¬ IsUnit (algebraMap O O' ϖ)` using `fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)`. Take `⟨e, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ0 hϖ'`.

Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Apply `hφϖnu` to reduce the goal to its premises. Rewrite using `[hv, pow_zero, mul_one]`. Conclude with `v.isUnit`.

Use `⟨e, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using `[he0, ENat.mul_top]`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`.

Establish `hu : IsDiscreteValuationRing.addVal O' (algebraMap O O' (u : O)) = 0` using `IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map _)`. Simplify using `only [map_mul, map_pow, hv, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hu, IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_uniformizer hϖ']`. Simplify using `only [zero_add, nsmul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_ramification (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) [IsLocalHom (algebraMap O O')] :
    ∃ e : ℕ, ∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hφϖ0 : algebraMap O O' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hφϖnu : ¬ IsUnit (algebraMap O O' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ0 hϖ'
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hφϖnu
    rw [hv, pow_zero, mul_one]
    exact v.isUnit
  refine ⟨e, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp [he0, ENat.mul_top]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    have hu : IsDiscreteValuationRing.addVal O' (algebraMap O O' (u : O)) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map _)
    simp only [map_mul, map_pow, hv, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hu,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_uniformizer hϖ,
      IsDiscreteValuationRing.addVal_uniformizer hϖ']
    simp only [zero_add, nsmul_eq_mul, mul_one]
    ring

open Polynomial in

/- English proof (translation)
Rewrite using `[← separableClosure.eq_top_iff, eq_top_iff]`. Introduce `z _`. Establish `hz : z ∈ Algebra.adjoin K ((∏ x, F x).rootSet L)`. Rewrite using `[Polynomial.IsSplittingField.adjoin_rootSet]`. Conclude with `Algebra.mem_top`.

Use `Algebra.adjoin_le (S := (separableClosure K L).toSubalgebra) ?_ hz` and prove the remaining obligations. Introduce `α hα`. Rewrite `hα` using `[Polynomial.mem_rootSet]`. Take `⟨-, hα0⟩` from `hα`. Rewrite `hα0` using `[map_prod, Finset.prod_eq_zero_iff]`.

Take `⟨x, -, hx⟩` from `hα0`. Conclude with `mem_separableClosure_iff.2 ((hF x).of_dvd (minpoly.dvd K α hx))`.
-/
theorem sep_splitting {K : Type} [Field K] {X : Type} [Fintype X] (F : X → K[X])
    (hF : ∀ x, (F x).Separable) (L : Type) [Field L] [Algebra K L] [IsSplittingField K L (∏ x, F x)] :
    Algebra.IsSeparable K L := by
  classical
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  intro z _
  have hz : z ∈ Algebra.adjoin K ((∏ x, F x).rootSet L) := by
    rw [Polynomial.IsSplittingField.adjoin_rootSet]
    exact Algebra.mem_top
  refine Algebra.adjoin_le (S := (separableClosure K L).toSubalgebra) ?_ hz
  intro α hα
  rw [Polynomial.mem_rootSet] at hα
  obtain ⟨-, hα0⟩ := hα
  rw [map_prod, Finset.prod_eq_zero_iff] at hα0
  obtain ⟨x, -, hx⟩ := hα0
  exact mem_separableClosure_iff.2 ((hF x).of_dvd (minpoly.dvd K α hx))

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `O _ _ _ _ X _ P hmon hsep`. Set `K` to `FractionRing O`. Set `Q : Polynomial K` to `∏ x, (P x).map (algebraMap O K)`. Set `L` to `Q.SplittingField`. Establish `hsepL : Algebra.IsSeparable K L` using `sep_splitting (fun x => (P x).map (algebraMap O K)) hsep L`.

Set `O'` to `integralClosure O L`. Establish `hfin : Module.Finite O O'` using `IsIntegralClosure.finite O K L O'`. Establish `htf : Module.IsTorsionFree O L` using `Module.IsTorsionFree.trans_faithfulSMul O K L`. Establish `hfree : Module.Free O O'` using `IsIntegralClosure.module_free O K L O'`. Establish `hded : IsDedekindDomain O'` using `inferInstance`.

Establish `hloc : IsLocalRing O'` using `local_of_complete O O'`. Establish `hinj : Function.Injective (algebraMap O O')` using `FaithfulSMul.algebraMap_injective O O'`. Establish `hnf : ¬ IsField O'` using `fun h => IsDiscreteValuationRing.not_isField O (isField_of_isIntegral_of_isField hinj h)`. Establish `hdvr : IsDiscreteValuationRing O'` using `((IsDiscreteValuationRing.TFAE O' hnf).out 0 2).mpr hded`. Take `⟨e, he⟩` from `exists_ramification O O' hinj`.

Use `⟨O', inferInstance, inferInstance, hdvr, inferInstance, hfree, hfin, e, he, fun x => ?_⟩` and prove the remaining obligations. Establish `hfr : IsFractionRing O' L` using `integralClosure.isFractionRing_of_finite_extension K L`. Set `σ : L →+* FractionRing O'` to `(FractionRing.algEquiv O' L).symm.toRingEquiv.toRingHom`. Establish `hσ : (algebraMap O' (FractionRing O')).comp (algebraMap O O') = σ.comp ((algebraMap K L).comp (algebraMap O K))`. Use `RingHom.ext fun y => ?_` and prove the remaining obligations.

Establish `h1 : algebraMap K L (algebraMap O K y) = algebraMap O' L (algebraMap O O' y)`. Rewrite using `[← IsScalarTower.algebraMap_apply O K L, ← IsScalarTower.algebraMap_apply O O' L]`. Use `show _ = (FractionRing.algEquiv O' L).symm (algebraMap K L (algebraMap O K y))`. Rewrite using `[h1, AlgEquiv.commutes]`. Both sides reduce to the same expression.

Rewrite using `[hσ, ← Polynomial.map_map, ← Polynomial.map_map]`. Use `Polynomial.Splits.map ?_ σ` and prove the remaining obligations. Establish `hQ : (Q.map (algebraMap K L)).Splits` using `Polynomial.SplittingField.splits Q`. Establish `hQ0 : Q.map (algebraMap K L) ≠ 0` using `Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun x _ => ((hmon x).map _).ne_zero)`. Conclude with `hQ.of_dvd hQ0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ x)))`.
-/
theorem splitExt : StatSplitExt := by
  intro O _ _ _ _ X _ P hmon hsep
  let K := FractionRing O
  let Q : Polynomial K := ∏ x, (P x).map (algebraMap O K)
  let L := Q.SplittingField
  have hsepL : Algebra.IsSeparable K L := sep_splitting (fun x => (P x).map (algebraMap O K)) hsep L
  let O' := integralClosure O L
  have hfin : Module.Finite O O' := IsIntegralClosure.finite O K L O'
  have htf : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  have hfree : Module.Free O O' := IsIntegralClosure.module_free O K L O'
  have hded : IsDedekindDomain O' := inferInstance
  have hloc : IsLocalRing O' := local_of_complete O O'
  have hinj : Function.Injective (algebraMap O O') := FaithfulSMul.algebraMap_injective O O'
  have hnf : ¬ IsField O' := fun h =>
    IsDiscreteValuationRing.not_isField O (isField_of_isIntegral_of_isField hinj h)
  have hdvr : IsDiscreteValuationRing O' := ((IsDiscreteValuationRing.TFAE O' hnf).out 0 2).mpr hded
  obtain ⟨e, he⟩ := exists_ramification O O' hinj
  refine ⟨O', inferInstance, inferInstance, hdvr, inferInstance, hfree, hfin, e, he, fun x => ?_⟩
  have hfr : IsFractionRing O' L := integralClosure.isFractionRing_of_finite_extension K L
  let σ : L →+* FractionRing O' := (FractionRing.algEquiv O' L).symm.toRingEquiv.toRingHom
  have hσ : (algebraMap O' (FractionRing O')).comp (algebraMap O O') =
      σ.comp ((algebraMap K L).comp (algebraMap O K)) := by
    refine RingHom.ext fun y => ?_
    have h1 : algebraMap K L (algebraMap O K y) = algebraMap O' L (algebraMap O O' y) := by
      rw [← IsScalarTower.algebraMap_apply O K L, ← IsScalarTower.algebraMap_apply O O' L]
    show _ = (FractionRing.algEquiv O' L).symm (algebraMap K L (algebraMap O K y))
    rw [h1, AlgEquiv.commutes]
    rfl
  rw [hσ, ← Polynomial.map_map, ← Polynomial.map_map]
  refine Polynomial.Splits.map ?_ σ
  have hQ : (Q.map (algebraMap K L)).Splits := Polynomial.SplittingField.splits Q
  have hQ0 : Q.map (algebraMap K L) ≠ 0 :=
    Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun x _ => ((hmon x).map _).ne_zero)
  exact hQ.of_dvd hQ0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ x)))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
