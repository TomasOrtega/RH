import Mathlib

open IsLocalRing

namespace GlobalTheory.ConormalDer

/- English proof (translation)
Use `set m := maximalIdeal B with hm`. Set `π : (B ⧸ m ^ 2) →ₐ[R] ResidueField B` to `Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R B (ResidueField B)) fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha)`. Establish `hπ : ∀ a, π (Ideal.Quotient.mk _ a) = residue B a` using `fun _ => rfl`. Establish `hsurj : Function.Surjective π` using `fun y => by`. Take `⟨a, rfl⟩` from `residue_surjective y`.

Conclude with `⟨_, hπ a⟩`. Establish `hker : ∀ z, π z = 0 → z ∈ m.cotangentIdeal` using `fun z hz => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `Ideal.mk_mem_cotangentIdeal.2 ((residue_eq_zero_iff a).1 hz)`. Establish `hnil : IsNilpotent (RingHom.ker (π : (B ⧸ m ^ 2) →+* ResidueField B))`.

Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, ← m.cotangentIdeal_square]`. Conclude with `Ideal.pow_right_mono (fun z hz => hker z hz) 2`. Set `s` to `Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R (ResidueField B)) π hsurj hnil`. Establish `hs : ∀ y, π (s y) = y` using `fun y => Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y`.

Establish `hmem : ∀ a, Ideal.Quotient.mk _ a - s (residue B a) ∈ m.cotangentIdeal` using `fun a => hker _ (by rw [map_sub, hs, hπ, sub_self])`. Set `D : B → CotangentSpace B` to `fun a => m.cotangentEquivIdeal.symm ⟨_, hmem a⟩`. Establish `hD : ∀ a, m.cotangentToQuotientSquare (D a) = Ideal.Quotient.mk _ a - s (residue B a)` using `fun a => by`. Rewrite using `[← Ideal.cotangentEquivIdeal_apply]`. Simplify using `only [D, LinearEquiv.apply_symm_apply]`.

Establish `hinj` using `m.cotangentToQuotientSquare_injective`. Establish `hsq : ∀ a b, (Ideal.Quotient.mk _ a - s (residue B a)) * (Ideal.Quotient.mk _ b - s (residue B b)) = 0` using `fun a b => by`. Use `Ideal.mul_mem_mul (hmem a) (hmem b)` as an intermediate fact. Rewrite `this` using `[← pow_two, m.cotangentIdeal_square, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hsm : ∀ (a : B) (z : B ⧸ m ^ 2), a • z = Ideal.Quotient.mk _ a * z` using `fun a z => Algebra.smul_def a z`.

Establish `hmul : ∀ a b, D (a * b) = a • D b + b • D a` using `fun a b => by`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, map_smul, map_smul, hD, hD, hD, hsm, hsm, map_mul, map_mul, map_mul]`. Take the linear combination `(-1 : B ⧸ m ^ 2) * hsq a b`. Establish `hR : ∀ c : R, D (algebraMap R B c) = 0` using `fun c => by`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hD, map_zero, sub_eq_zero]`. Conclude with `(s.commutes c).symm`. Use `⟨⟨⟨D, fun a b => ?_⟩, fun c a => ?_⟩, hmul, fun t => ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_add, hD, hD, hD, map_add, map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Use `show D (c • a) = c • D a`. Rewrite using `[Algebra.smul_def, hmul, hR, smul_zero, add_zero, algebraMap_smul]`. Apply `hinj show m.cotangentToQuotientSquare (D t) = _` to reduce the goal to its premises.

Rewrite using `[hD, (residue_eq_zero_iff _).2 t.2, map_zero, sub_zero, Ideal.toCotangent_to_quotient_square]`. Both sides reduce to the same expression.
-/
theorem exists_derivation_cotangent (R B : Type) [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.FormallySmooth R (ResidueField B)] :
    ∃ D : B →ₗ[R] CotangentSpace B, (∀ a b, D (a * b) = a • D b + b • D a) ∧
      ∀ t : maximalIdeal B, D t = (maximalIdeal B).toCotangent t := by
  set m := maximalIdeal B with hm
  let π : (B ⧸ m ^ 2) →ₐ[R] ResidueField B :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R B (ResidueField B)) fun a ha =>
      (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = residue B a := fun _ => rfl
  have hsurj : Function.Surjective π := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨_, hπ a⟩
  have hker : ∀ z, π z = 0 → z ∈ m.cotangentIdeal := fun z hz => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.mk_mem_cotangentIdeal.2 ((residue_eq_zero_iff a).1 hz)
  have hnil : IsNilpotent (RingHom.ker (π : (B ⧸ m ^ 2) →+* ResidueField B)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← m.cotangentIdeal_square]
    exact Ideal.pow_right_mono (fun z hz => hker z hz) 2
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R (ResidueField B)) π hsurj hnil
  have hs : ∀ y, π (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y
  have hmem : ∀ a, Ideal.Quotient.mk _ a - s (residue B a) ∈ m.cotangentIdeal := fun a =>
    hker _ (by rw [map_sub, hs, hπ, sub_self])
  let D : B → CotangentSpace B := fun a => m.cotangentEquivIdeal.symm ⟨_, hmem a⟩
  have hD : ∀ a, m.cotangentToQuotientSquare (D a) = Ideal.Quotient.mk _ a - s (residue B a) :=
    fun a => by
      rw [← Ideal.cotangentEquivIdeal_apply]
      simp only [D, LinearEquiv.apply_symm_apply]
  have hinj := m.cotangentToQuotientSquare_injective
  have hsq : ∀ a b, (Ideal.Quotient.mk _ a - s (residue B a)) *
      (Ideal.Quotient.mk _ b - s (residue B b)) = 0 := fun a b => by
    have := Ideal.mul_mem_mul (hmem a) (hmem b)
    rwa [← pow_two, m.cotangentIdeal_square, Ideal.mem_bot] at this
  have hsm : ∀ (a : B) (z : B ⧸ m ^ 2), a • z = Ideal.Quotient.mk _ a * z := fun a z =>
    Algebra.smul_def a z
  have hmul : ∀ a b, D (a * b) = a • D b + b • D a := fun a b => by
    apply hinj
    rw [map_add, map_smul, map_smul, hD, hD, hD, hsm, hsm, map_mul, map_mul, map_mul]
    linear_combination (-1 : B ⧸ m ^ 2) * hsq a b
  have hR : ∀ c : R, D (algebraMap R B c) = 0 := fun c => by
    apply hinj
    rw [hD, map_zero, sub_eq_zero]
    exact (s.commutes c).symm
  refine ⟨⟨⟨D, fun a b => ?_⟩, fun c a => ?_⟩, hmul, fun t => ?_⟩
  · apply hinj
    rw [map_add, hD, hD, hD, map_add, map_add, map_add]
    ring
  · show D (c • a) = c • D a
    rw [Algebra.smul_def, hmul, hR, smul_zero, add_zero, algebraMap_smul]
  · apply hinj
    show m.cotangentToQuotientSquare (D t) = _
    rw [hD, (residue_eq_zero_iff _).2 t.2, map_zero, sub_zero, Ideal.toCotangent_to_quotient_square]
    rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_isTranscendenceBasis F K`. Use `haveI := hs.isAlgebraic_field`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective`. Use `haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) := charZero_of_injective_algebraMap (algebraMap F _).injective`. Use `haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K := Algebra.IsAlgebraic.isSeparable_of_perfectField`.

Conclude with `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1`.
-/
theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/- English proof (translation)
Set `K` to `FractionRing R`. Establish `hu' : ∀ c : nonZeroDivisors R, IsUnit (algebraMap R B c)` using `fun c => hu c (nonZeroDivisors.ne_zero c.2)`. Use `letI : Algebra K B := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hu').toAlgebra`. Use `haveI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun c => (IsLocalization.lift_eq hu' c).symm`. Use `haveI : IsScalarTower R K (ResidueField B) := IsScalarTower.of_algebraMap_eq fun c => by`.

Rewrite using `[IsScalarTower.algebraMap_apply K B (ResidueField B), ← IsScalarTower.algebraMap_apply R K B, ← IsScalarTower.algebraMap_apply]`. Use `haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective`. Use `haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R`. Use `haveI : Algebra.FormallySmooth K (ResidueField B) := formallySmooth_of_charZero K _`. Use `haveI : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)`.

Conclude with `.comp R K (ResidueField B)`.
-/
theorem formallySmooth_residueField (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (hu : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) :
    Algebra.FormallySmooth R (ResidueField B) := by
  let K := FractionRing R
  have hu' : ∀ c : nonZeroDivisors R, IsUnit (algebraMap R B c) := fun c =>
    hu c (nonZeroDivisors.ne_zero c.2)
  letI : Algebra K B := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hu').toAlgebra
  haveI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun c =>
    (IsLocalization.lift_eq hu' c).symm
  haveI : IsScalarTower R K (ResidueField B) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (ResidueField B), ← IsScalarTower.algebraMap_apply R K B,
      ← IsScalarTower.algebraMap_apply]
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.FormallySmooth K (ResidueField B) := formallySmooth_of_charZero K _
  haveI : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  exact .comp R K (ResidueField B)

/- English proof (translation)
Introduce `R B _ _ _ _ _ _ hu lam`. Use `haveI := formallySmooth_residueField R B hu`. Take `⟨D, hmul, hD⟩` from `exists_derivation_cotangent R B`. Establish `hsm : ∀ (a : B) (v : CotangentSpace B), lam (a • v) = a • lam v` using `fun a v => by`. Rewrite using `[← algebraMap_smul (ResidueField B) a v, map_smul, algebraMap_smul]`.

Set `L : B →ₗ[R] ResidueField B` to `{ toFun := fun a => lam (D a) map_add' := fun a b => by rw [map_add, map_add] map_smul' := fun c a => by`. Rewrite using `[RingHom.id_apply, map_smul, ← algebraMap_smul B c (D a), hsm, algebraMap_smul] }`. Use `⟨Derivation.mk' L fun a b => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `lam (D (a * b)) = a • lam (D b) + b • lam (D a)`. Rewrite using `[hmul, map_add, hsm, hsm]`.

Use `show lam (D y) = _`. Conclude with `congrArg lam (hD ⟨y, hy⟩)`.
-/
theorem exists_derivation_extending :
    ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  intro R B _ _ _ _ _ _ hu lam
  haveI := formallySmooth_residueField R B hu
  obtain ⟨D, hmul, hD⟩ := exists_derivation_cotangent R B
  have hsm : ∀ (a : B) (v : CotangentSpace B), lam (a • v) = a • lam v := fun a v => by
    rw [← algebraMap_smul (ResidueField B) a v, map_smul, algebraMap_smul]
  let L : B →ₗ[R] ResidueField B :=
    { toFun := fun a => lam (D a)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, map_smul, ← algebraMap_smul B c (D a), hsm, algebraMap_smul] }
  refine ⟨Derivation.mk' L fun a b => ?_, fun y hy => ?_⟩
  · change lam (D (a * b)) = a • lam (D b) + b • lam (D a)
    rw [hmul, map_add, hsm, hsm]
  · show lam (D y) = _
    exact congrArg lam (hD ⟨y, hy⟩)

end GlobalTheory.ConormalDer
