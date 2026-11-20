import Mathlib
open IsDedekindDomain

namespace GlobalTheory.InertiaFixedVal

/- English proof (translation)
Introduce `hy hv`. Set `H : Subgroup (L ≃ₐ[K] L)` to `P.asIdeal.inertia (L ≃ₐ[K] L)`. Set `E : IntermediateField K L` to `FixedPoints.intermediateField H`. Use `haveI : IsGaloisGroup H E L := IsGaloisGroup.subgroup (L ≃ₐ[K] L) K L H`. Use `haveI : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq fun r => by`.

Rewrite using `[IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K E]`. Both sides reduce to the same expression. Set `OE` to `integralClosure R E`. Use `haveI : IsFractionRing OE E := integralClosure.isFractionRing_of_finite_extension K E`. Use `haveI : IsDedekindDomain OE := integralClosure.isDedekindDomain R K E`.

Set `f : OE →ₐ[R] integralClosure R L` to `((IsScalarTower.toAlgHom R E L).comp OE.val).codRestrict _ (fun x => x.2.map (IsScalarTower.toAlgHom R E L))`. Use `letI : Algebra OE (integralClosure R L) := f.toRingHom.toAlgebra`. Use `haveI : IsScalarTower OE (integralClosure R L) L := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower R OE (integralClosure R L) := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm`. Use `haveI : Algebra.IsIntegral OE (integralClosure R L) := Algebra.IsIntegral.tower_top R`.

Use `haveI : FaithfulSMul OE (integralClosure R L) := by`. Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `a b hab`. Use `congrArg (fun x : integralClosure R L => (x : L)) hab` as an intermediate fact. Conclude with `Subtype.ext (FaithfulSMul.algebraMap_injective E L this)`.

Use `haveI : Module.IsTorsionFree OE (integralClosure R L) := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance`. Use `haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L (integralClosure R L)`. Use `haveI : Module.Finite OE (integralClosure R L) := Module.Finite.of_restrictScalars_finite R OE _`. Use `haveI : Module.Flat OE (integralClosure R L) := inferInstance`. Use `haveI : SMulDistribClass H (integralClosure R L) L := inferInstance`.

Use `haveI : IsGaloisGroup H OE (integralClosure R L) := IsGaloisGroup.of_isFractionRing H OE (integralClosure R L) E L`. Set `Q : Ideal OE` to `P.asIdeal.under OE`. Establish `hPne : P.asIdeal ≠ ⊥` using `P.ne_bot`. Establish `hQne : Q ≠ ⊥`. Conclude with `Ideal.under_ne_bot OE hPne`.

Use `haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne`. Establish `hQR : (Q.under R).IsMaximal` using `Ideal.IsMaximal.under R Q`. Use `haveI : Q.LiesOver (IsLocalRing.maximalIdeal R) := ⟨(IsLocalRing.eq_maximalIdeal hQR).symm⟩`. Use `letI : Field (OE ⧸ Q) := Ideal.Quotient.field Q`. Use `letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _`.

Use `haveI : Algebra.IsIntegral R OE := ⟨fun x => integralClosure.isIntegral x⟩`. Use `haveI : Algebra.IsIntegral (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := inferInstance`. Use `haveI : Algebra.IsAlgebraic (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := Algebra.IsIntegral.isAlgebraic`. Use `haveI : PerfectField (OE ⧸ Q) := by haveI : PerfectField (R ⧸ IsLocalRing.maximalIdeal R) := ‹PerfectField (IsLocalRing.ResidueField R)›`. Conclude with `Algebra.IsAlgebraic.perfectField (R ⧸ IsLocalRing.maximalIdeal R)`.

Use `haveI : PerfectField Q.ResidueField := PerfectField.of_ringEquiv (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField Q))`. Establish `htop : P.asIdeal.inertia H = ⊤`. Rewrite using `[Subgroup.eq_top_iff']`. Introduce `σ`. Conclude with `AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x`.

Establish `hcard : Nat.card H = P.asIdeal.ramificationIdx OE`. Establish `h` using `Ideal.card_inertia_eq_ramificationIdxIn (G := H) Q P.asIdeal`. Rewrite `h` using `[Ideal.ramificationIdxIn_eq_ramificationIdx Q P.asIdeal H, htop, Subgroup.card_top]`. Conclude with `h`. Establish `hyE : y ∈ E` using `fun σ => hy σ σ.2`.

Set `z : E` to `⟨y, hyE⟩`. Set `w : HeightOneSpectrum OE` to `⟨Q, inferInstance, hQne⟩`. Use `haveI : P.asIdeal.LiesOver w.asIdeal := inferInstance`. Establish `hval` using `HeightOneSpectrum.valuation_liesOver L w P z`. Rewrite `hval` using `[Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal P.asIdeal hQne, ← hcard]`.

Express the relevant statement in the definitionally equal form `w.valuation E z ^ Nat.card H = P.valuation L y at hval`. Establish `hn : Nat.card H ≠ 0` using `Nat.card_pos.ne'`. Establish `hz : w.valuation E z < 1`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_lt]`.

Use `one_le_pow₀ (n := Nat.card H) h` as an intermediate fact. Rewrite `this` using `[hval]`. Conclude with `absurd hv (not_lt.mpr this)`. Establish `hz1 : w.valuation E z ≤ WithZero.exp (-1)`. Distinguish the cases in `h0 : w.valuation E z = 0`.

Rewrite using `[h0]`. Conclude with `zero_le`. Rewrite `hz`, the goal using `[← WithZero.exp_log h0]`. Rewrite `hz` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← hval]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_nsmul]`. Use `congr 1`.

Simplify using the standard rewrite rules.
-/
theorem valuation_le_exp_neg_card_inertia (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L) :
    (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 →
      P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by
  intro hy hv
  classical
  let H : Subgroup (L ≃ₐ[K] L) := P.asIdeal.inertia (L ≃ₐ[K] L)
  let E : IntermediateField K L := FixedPoints.intermediateField H
  haveI : IsGaloisGroup H E L := IsGaloisGroup.subgroup (L ≃ₐ[K] L) K L H
  haveI : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K E]; rfl
  let OE := integralClosure R E
  haveI : IsFractionRing OE E := integralClosure.isFractionRing_of_finite_extension K E
  haveI : IsDedekindDomain OE := integralClosure.isDedekindDomain R K E
  let f : OE →ₐ[R] integralClosure R L := ((IsScalarTower.toAlgHom R E L).comp OE.val).codRestrict _
    (fun x => x.2.map (IsScalarTower.toAlgHom R E L))
  letI : Algebra OE (integralClosure R L) := f.toRingHom.toAlgebra
  haveI : IsScalarTower OE (integralClosure R L) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R OE (integralClosure R L) := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI : Algebra.IsIntegral OE (integralClosure R L) := Algebra.IsIntegral.tower_top R
  haveI : FaithfulSMul OE (integralClosure R L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun x : integralClosure R L => (x : L)) hab
    exact Subtype.ext (FaithfulSMul.algebraMap_injective E L this)
  haveI : Module.IsTorsionFree OE (integralClosure R L) := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L (integralClosure R L)
  haveI : Module.Finite OE (integralClosure R L) := Module.Finite.of_restrictScalars_finite R OE _
  haveI : Module.Flat OE (integralClosure R L) := inferInstance
  haveI : SMulDistribClass H (integralClosure R L) L := inferInstance
  haveI : IsGaloisGroup H OE (integralClosure R L) := IsGaloisGroup.of_isFractionRing H OE (integralClosure R L) E L

  let Q : Ideal OE := P.asIdeal.under OE
  have hPne : P.asIdeal ≠ ⊥ := P.ne_bot
  have hQne : Q ≠ ⊥ := by
    exact Ideal.under_ne_bot OE hPne
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
  have hQR : (Q.under R).IsMaximal := Ideal.IsMaximal.under R Q
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal R) := ⟨(IsLocalRing.eq_maximalIdeal hQR).symm⟩
  letI : Field (OE ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  haveI : Algebra.IsIntegral R OE := ⟨fun x => integralClosure.isIntegral x⟩
  haveI : Algebra.IsIntegral (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : PerfectField (OE ⧸ Q) := by
    haveI : PerfectField (R ⧸ IsLocalRing.maximalIdeal R) := ‹PerfectField (IsLocalRing.ResidueField R)›
    exact Algebra.IsAlgebraic.perfectField (R ⧸ IsLocalRing.maximalIdeal R)
  haveI : PerfectField Q.ResidueField :=
    PerfectField.of_ringEquiv (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField Q))
  have htop : P.asIdeal.inertia H = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro σ
    exact AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x
  have hcard : Nat.card H = P.asIdeal.ramificationIdx OE := by
    have h := Ideal.card_inertia_eq_ramificationIdxIn (G := H) Q P.asIdeal
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P.asIdeal H, htop, Subgroup.card_top] at h
    exact h

  have hyE : y ∈ E := fun σ => hy σ σ.2
  let z : E := ⟨y, hyE⟩
  let w : HeightOneSpectrum OE := ⟨Q, inferInstance, hQne⟩
  haveI : P.asIdeal.LiesOver w.asIdeal := inferInstance
  have hval := HeightOneSpectrum.valuation_liesOver L w P z
  rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal P.asIdeal hQne, ← hcard] at hval
  change w.valuation E z ^ Nat.card H = P.valuation L y at hval
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hz : w.valuation E z < 1 := by
    by_contra h
    rw [not_lt] at h
    have := one_le_pow₀ (n := Nat.card H) h
    rw [hval] at this
    exact absurd hv (not_lt.mpr this)
  have hz1 : w.valuation E z ≤ WithZero.exp (-1) := by
    by_cases h0 : w.valuation E z = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at hz ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [WithZero.exp_le_exp]
      omega
  rw [← hval]
  calc w.valuation E z ^ Nat.card H ≤ WithZero.exp (-1) ^ Nat.card H := pow_le_pow_left₀ zero_le hz1 _
    _ = WithZero.exp (-(Nat.card H : ℤ)) := by
      rw [← WithZero.exp_nsmul]; congr 1; simp
end GlobalTheory.InertiaFixedVal
