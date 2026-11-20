import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerRest

open Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.PrimTransc

/- English proof (translation)
Use `set R := MvPolynomial (Fin D) ℚ`. Use `set F := FractionRing R`. Take `⟨a, b, hab⟩` from `h`. Take `⟨da, hda, hA⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) a`. Take `⟨db, hdb, hB⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) b`.

Use `set A := IsLocalization.integerNormalization (nonZeroDivisors R) a`. Use `set B := IsLocalization.integerNormalization (nonZeroDivisors R) b`. Establish `key : (C db * A) * P + (C da * B) * derivative P = C (da * db)`. Apply `Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)` to reduce the goal to its premises. Establish `hA' : A.map (algebraMap R F) = C (algebraMap R F da) * a`.

Rewrite using `[hA, ← algebraMap_smul F da a, smul_eq_C_mul]`. Establish `hB' : B.map (algebraMap R F) = C (algebraMap R F db) * b`. Rewrite using `[hB, ← algebraMap_smul F db b, smul_eq_C_mul]`. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA', hB', ← derivative_map, map_mul]`. Take the linear combination `(C (algebraMap R F da) * C (algebraMap R F db)) * hab`.

Establish `hδ : da * db ≠ 0` using `mul_ne_zero (nonZeroDivisors.ne_zero hda) (nonZeroDivisors.ne_zero hdb)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : Fin D → ℚ, MvPolynomial.eval c (da * db) ≠ 0 := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hδ (MvPolynomial.funext fun c => by simpa using hno c)`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `key'` using `congrArg (Polynomial.map (MvPolynomial.eval c)) key`. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at key'`. Establish `hinv : C (MvPolynomial.eval c (da * db))⁻¹ * C (MvPolynomial.eval c (da * db)) = 1`. Rewrite using `[← C_mul, inv_mul_cancel₀ hc, C_1]`.

Use `⟨C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c db) * A.map (MvPolynomial.eval c)), C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c da) * B.map (MvPolynomial.eval c)), ?_⟩` and prove the remaining obligations. Take the linear combination `C (MvPolynomial.eval c (da * db))⁻¹ * key' + hinv`.
-/
theorem exists_separable_specialization {D : ℕ} (P : (MvPolynomial (Fin D) ℚ)[X])
    (h : (P.map (algebraMap (MvPolynomial (Fin D) ℚ) (FractionRing (MvPolynomial (Fin D) ℚ)))).Separable) :
    ∃ c : Fin D → ℚ, (P.map (MvPolynomial.eval c)).Separable := by
  set R := MvPolynomial (Fin D) ℚ
  set F := FractionRing R
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨da, hda, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨db, hdb, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors R) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors R) b
  have key : (C db * A) * P + (C da * B) * derivative P = C (da * db) := by
    apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
    have hA' : A.map (algebraMap R F) = C (algebraMap R F da) * a := by
      rw [hA, ← algebraMap_smul F da a, smul_eq_C_mul]
    have hB' : B.map (algebraMap R F) = C (algebraMap R F db) * b := by
      rw [hB, ← algebraMap_smul F db b, smul_eq_C_mul]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA', hB',
      ← derivative_map, map_mul]
    linear_combination (C (algebraMap R F da) * C (algebraMap R F db)) * hab
  have hδ : da * db ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hda) (nonZeroDivisors.ne_zero hdb)
  obtain ⟨c, hc⟩ : ∃ c : Fin D → ℚ, MvPolynomial.eval c (da * db) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hδ (MvPolynomial.funext fun c => by simpa using hno c)
  refine ⟨c, ?_⟩
  have key' := congrArg (Polynomial.map (MvPolynomial.eval c)) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at key'
  have hinv : C (MvPolynomial.eval c (da * db))⁻¹ * C (MvPolynomial.eval c (da * db)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  refine ⟨C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c db) * A.map (MvPolynomial.eval c)),
    C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c da) * B.map (MvPolynomial.eval c)), ?_⟩
  linear_combination C (MvPolynomial.eval c (da * db))⁻¹ * key' + hinv

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R F K h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 θ z hz; exact @_root_.GlobalTheory.TargetInequalityLemmas.target)`. Consider the case `exact @_root_.GlobalTheory.TargetInequalityLemmas.target`. Consider the case `exact _root_.GlobalTheory.TargetInequalityLemmas.target`. Consider the case `(apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.TargetInequalityLemmas.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TargetInequalityLemmas.target ..)`.
-/
theorem exists_mul_mem_adjoin {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F {θ}) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R K d * z ∈ Algebra.adjoin R {θ} := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R F K h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 θ z hz; exact @_root_.GlobalTheory.TargetInequalityLemmas.target)
  | exact @_root_.GlobalTheory.TargetInequalityLemmas.target
  | exact _root_.GlobalTheory.TargetInequalityLemmas.target
  | (apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetInequalityLemmas.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetInequalityLemmas.target ..)

/- English proof (translation)
Introduce `K _ _ D x hx J _ e`. Use `Fintype.ofFinite J` as an intermediate fact. Set `R` to `MvPolynomial (Fin D) ℚ`. Set `F` to `FractionRing R`. Set `φ : R →ₐ[ℚ] K` to `MvPolynomial.aeval x`.

Establish `φinj : Function.Injective φ` using `hx.1`. Use `letI : Algebra R K := φ.toRingHom.toAlgebra`. Establish `hφ : ∀ r : R, algebraMap R K r = φ r` using `fun r => rfl`. Use `haveI : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm`. Use `haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 φinj`.

Use `letI : Algebra F K := FractionRing.liftAlgebra R K`. Use `haveI : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K`. Use `haveI : CharZero F := RingHom.charZero (algebraMap F K)`. Use `haveI : Algebra.IsAlgebraic R K := haveI := hx.isAlgebraic ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hx.1.aevalEquiv.symm.toRingHom) (g := RingHom.id K) (Algebra.IsAlgebraic.isAlgebraic y) hx.1.aevalEquiv.symm.injective (RingHom.ext fun z => by`. Take `⟨p, rfl⟩` from `hx.1.aevalEquiv.surjective z`.

Simplify using `[RingHom.algebraMap_toAlgebra, φ]))⟩`. Use `haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R F)`. Set `E` to `IntermediateField.adjoin F (Set.range e)`. Use `haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin (fun y _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) y).isIntegral)`. Take `⟨α, hα⟩` from `Field.exists_primitive_element F E`.

Establish `hαE : F⟮(α : K)⟯ = E`. Simplify `congrArg IntermediateField.lift hα` using `only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]`. Take `⟨y, hy0, hyint⟩` from `IsAlgebraic.exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (R := R) (α : K))`. Use `set θ : K := y • (α : K) with hθdef`. Establish `hθF : IsIntegral F θ` using `(Algebra.IsAlgebraic.isAlgebraic (R := F) θ).isIntegral`.

Establish `hyF : algebraMap R F y ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hy0`. Establish `hαθ : (α : K) ∈ F⟮θ⟯`. Establish `: (α : K) = algebraMap F K (algebraMap R F y)⁻¹ * θ`. Rewrite using `[hθdef, Algebra.smul_def, IsScalarTower.algebraMap_apply R F K, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hyF, map_one, one_mul]`. Rewrite using `[this]`.

Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)`. Establish `heθ : ∀ j, e j ∈ Algebra.adjoin F {θ}`. Introduce `j`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθF.isAlgebraic]`. Establish `h1 : E ≤ F⟮θ⟯` using `hαE ▸ IntermediateField.adjoin_simple_le_iff.2 hαθ`.

Conclude with `h1 (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)`. Use `choose d hd0 hdm using fun j => exists_mul_mem_adjoin (R := R) (F := F) θ (e j) (heθ j)`. Set `P` to `minpoly R θ`. Set `ψ₀ : AdjoinRoot P →ₐ[R] K` to `AdjoinRoot.liftAlgHom P (Algebra.ofId R K) θ (minpoly.aeval R θ)`. Set `ψ : AdjoinRoot P →ₐ[ℚ] K` to `ψ₀.restrictScalars ℚ`.

Establish `hψinj : Function.Injective ψ`. Use `(injective_iff_map_eq_zero ψ).2 fun q hq => ?_` and prove the remaining obligations. Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective q`. Establish `hq' : Polynomial.aeval θ q = 0` using `hq`. Conclude with `AdjoinRoot.mk_eq_zero.2 ((minpoly.isIntegrallyClosed_dvd_iff hyint q).1 hq')`.

Establish `hrange : Algebra.adjoin R {θ} ≤ ψ₀.range`. Rewrite using `[Algebra.adjoin_le_iff, Set.singleton_subset_iff]`. Conclude with `⟨AdjoinRoot.root P, AdjoinRoot.liftAlgHom_root _ _ _ _⟩`. Establish `hsep : (P.map (algebraMap R F)).Separable`. Rewrite using `[← minpoly.isIntegrallyClosed_eq_field_fractions' F hyint]`.

Conclude with `(minpoly.irreducible hθF).separable`. Take `⟨c, hc⟩` from `exists_separable_specialization P hsep`. Use `⟨P, ψ, algebraMap R K (∏ j, d j), c, minpoly.monic hyint, hψinj, fun i => ?_, ?_, fun j => ?_, hc⟩` and prove the remaining obligations. Use `show ψ₀ (AdjoinRoot.of P (MvPolynomial.X i)) = x i`. Rewrite using `[← AdjoinRoot.algebraMap_eq, AlgHom.commutes, hφ]`.

Conclude with `MvPolynomial.aeval_X x i`. Conclude with `(map_ne_zero_iff _ φinj).2 (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)`. Establish `hm : algebraMap R K (∏ j, d j) * e j ∈ Algebra.adjoin R {θ}`. Rewrite using `[← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j), mul_comm (d j), map_mul, mul_assoc]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ _) (hdm j)`.

Take `⟨a, ha⟩` from `hrange hm`. Conclude with `⟨a, ha⟩`.
-/
theorem exists_primitive_monic_separable_specialization :
    ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x →
      ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ))
        (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧
        (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧
        (P.map (MvPolynomial.eval c)).Separable := by
  intro K _ _ D x hx J _ e
  classical
  have := Fintype.ofFinite J
  let R := MvPolynomial (Fin D) ℚ
  let F := FractionRing R
  let φ : R →ₐ[ℚ] K := MvPolynomial.aeval x
  have φinj : Function.Injective φ := hx.1
  letI : Algebra R K := φ.toRingHom.toAlgebra
  have hφ : ∀ r : R, algebraMap R K r = φ r := fun r => rfl
  haveI : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 φinj
  letI : Algebra F K := FractionRing.liftAlgebra R K
  haveI : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  haveI : CharZero F := RingHom.charZero (algebraMap F K)
  haveI : Algebra.IsAlgebraic R K :=
    haveI := hx.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hx.1.aevalEquiv.symm.toRingHom) (g := RingHom.id K)
      (Algebra.IsAlgebraic.isAlgebraic y) hx.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra, φ]))⟩
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R F)

  let E := IntermediateField.adjoin F (Set.range e)
  haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    (fun y _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) y).isIntegral)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hαE : F⟮(α : K)⟯ = E := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congrArg IntermediateField.lift hα
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (R := R) (α : K))
  set θ : K := y • (α : K) with hθdef
  have hθF : IsIntegral F θ := (Algebra.IsAlgebraic.isAlgebraic (R := F) θ).isIntegral
  have hyF : algebraMap R F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hy0
  have hαθ : (α : K) ∈ F⟮θ⟯ := by
    have : (α : K) = algebraMap F K (algebraMap R F y)⁻¹ * θ := by
      rw [hθdef, Algebra.smul_def, IsScalarTower.algebraMap_apply R F K, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hyF, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)
  have heθ : ∀ j, e j ∈ Algebra.adjoin F {θ} := by
    intro j
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθF.isAlgebraic]
    have h1 : E ≤ F⟮θ⟯ := hαE ▸ IntermediateField.adjoin_simple_le_iff.2 hαθ
    exact h1 (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  choose d hd0 hdm using fun j => exists_mul_mem_adjoin (R := R) (F := F) θ (e j) (heθ j)

  let P := minpoly R θ
  let ψ₀ : AdjoinRoot P →ₐ[R] K := AdjoinRoot.liftAlgHom P (Algebra.ofId R K) θ (minpoly.aeval R θ)
  let ψ : AdjoinRoot P →ₐ[ℚ] K := ψ₀.restrictScalars ℚ
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun q hq => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective q
    have hq' : Polynomial.aeval θ q = 0 := hq
    exact AdjoinRoot.mk_eq_zero.2 ((minpoly.isIntegrallyClosed_dvd_iff hyint q).1 hq')
  have hrange : Algebra.adjoin R {θ} ≤ ψ₀.range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨AdjoinRoot.root P, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
  have hsep : (P.map (algebraMap R F)).Separable := by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F hyint]
    exact (minpoly.irreducible hθF).separable
  obtain ⟨c, hc⟩ := exists_separable_specialization P hsep
  refine ⟨P, ψ, algebraMap R K (∏ j, d j), c, minpoly.monic hyint, hψinj, fun i => ?_, ?_, fun j => ?_, hc⟩
  · show ψ₀ (AdjoinRoot.of P (MvPolynomial.X i)) = x i
    rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes, hφ]
    exact MvPolynomial.aeval_X x i
  · exact (map_ne_zero_iff _ φinj).2 (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)
  · have hm : algebraMap R K (∏ j, d j) * e j ∈ Algebra.adjoin R {θ} := by
      rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j), mul_comm (d j), map_mul, mul_assoc]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdm j)
    obtain ⟨a, ha⟩ := hrange hm
    exact ⟨a, ha⟩

end GlobalTheory.PrimTransc
