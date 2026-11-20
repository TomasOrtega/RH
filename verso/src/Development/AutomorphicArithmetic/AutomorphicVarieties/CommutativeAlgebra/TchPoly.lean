import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private noncomputable def tchU (n : ℕ) (O : Type) [CommRing O] (i : Fin n) : (MvPowerSeries (Fin n) O)ˣ :=
  (show IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) O) from
    MvPowerSeries.isUnit_iff_constantCoeff.2 (by simp)).unit

/- English proof (translation)
The claim follows from `IsUnit.unit_spec _`.
-/
private lemma tchU_val (n : ℕ) (O : Type) [CommRing O] (i : Fin n) :
    (tchU n O i : MvPowerSeries (Fin n) O) = 1 + MvPowerSeries.X i := IsUnit.unit_spec _

/- English proof (translation)
Establish `h1 : (∑ j ∈ s, (∏ i, (1 + MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (e j i)) * MvPolynomial.C (x j)) = 0`. Apply `MvPolynomial.coe_injective (Fin n) R` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coe_zero, ← h, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_prod]`.

Simplify using the standard rewrite rules. Establish `h2` using `congrArg (MvPolynomial.aeval (R := R) (fun i : Fin n => (MvPolynomial.X i - 1 : MvPolynomial (Fin n) R))) h1`. Rewrite `h2` using `[map_sum, map_zero]`. Establish `h3 : ∑ j ∈ s, MvPolynomial.monomial (e j) (x j) = 0`. Rewrite using `[← h2]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `[map_prod, mul_comm]`. Introduce `j hj`. Establish `h4` using `congrArg (MvPolynomial.coeff (e j)) h3`.

Rewrite `h4` using `[MvPolynomial.coeff_sum, Finset.sum_eq_single j]`. Simplify using `using h4`. Introduce `k hk hkj`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`. Introduce `hh`.

Conclude with `hkj (he hk hj hh)`. Introduce `h`. Conclude with `absurd hj h`.
-/
private lemma tch_poly (n : ℕ) (R : Type) [CommRing R] {X : Type} (s : Finset X) (x : X → R)
    (e : X → Fin n →₀ ℕ) (he : Set.InjOn e s)
    (h : ∑ j ∈ s, (∏ i, (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) R) ^ (e j i)) * C (x j) = 0) :
    ∀ j ∈ s, x j = 0 := by
  classical
  have h1 : (∑ j ∈ s, (∏ i, (1 + MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (e j i)) *
      MvPolynomial.C (x j)) = 0 := by
    apply MvPolynomial.coe_injective (Fin n) R
    rw [MvPolynomial.coe_zero, ← h, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_prod]
    simp
  have h2 := congrArg (MvPolynomial.aeval (R := R)
    (fun i : Fin n => (MvPolynomial.X i - 1 : MvPolynomial (Fin n) R))) h1
  rw [map_sum, map_zero] at h2
  have h3 : ∑ j ∈ s, MvPolynomial.monomial (e j) (x j) = 0 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp [map_prod, mul_comm]
  intro j hj
  have h4 := congrArg (MvPolynomial.coeff (e j)) h3
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j] at h4
  · simpa using h4
  · intro k hk hkj
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hh
    exact hkj (he hk hj hh)
  · intro h; exact absurd hj h

/- English proof (translation)
Introduce `O _ _ X _ _ _`. Set `n` to `Module.finrank ℤ X`. Set `b : Module.Basis (Fin n) ℤ X` to `Module.finBasis ℤ X`. Set `t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ` to `{ toFun := fun j => ∏ i, tchU n O i ^ (b.repr j.toAdd i) map_one' := by simp map_mul' := by`. Introduce `a c`.

Simplify using `[zpow_add, Finset.prod_mul_distrib] }`. Establish `ht : ∀ j : X, t (Multiplicative.ofAdd j) = ∏ i, tchU n O i ^ (b.repr j i)` using `fun j => rfl`. Use `⟨n, t, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Establish `h1 : ∀ i, Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (tchU n O i) = 1`.

Introduce `i`. Use `ext`. Simplify using `[tchU_val]`. Establish `h2 : Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (t j) = 1`. Use `ht j.toAdd` as an intermediate fact.

Rewrite `this` using `[ofAdd_toAdd]`. Rewrite using `[this, map_prod]`. Simplify using `only [map_zpow, h1, one_zpow, Finset.prod_const_one]`. Simplify using `using congrArg Units.val h2`. Introduce `R _ _ s x h`.

Set `N : ℕ` to `∑ j ∈ s, ∑ i, (b.repr j i).natAbs`. Establish `hN : ∀ j ∈ s, ∀ i, 0 ≤ b.repr j i + N`. Introduce `j hj i`. Establish `h1 : (b.repr j i).natAbs ≤ ∑ i, (b.repr j i).natAbs` using `Finset.single_le_sum (f := fun i => (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `h2 : ∑ i, (b.repr j i).natAbs ≤ N` using `Finset.single_le_sum (f := fun j => ∑ i, (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) hj`.

Use linear arithmetic over natural numbers and integers. Set `e : X → Fin n →₀ ℕ` to `fun j => Finsupp.equivFunOnFinite.symm fun i => (b.repr j i + N).toNat`. Establish `he : ∀ j i, e j i = (b.repr j i + N).toNat` using `fun j i => rfl`. Use `tch_poly n R s x e ?_ ?_` and prove the remaining obligations. Introduce `j hj k hk hjk`.

Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `h1` using `he j i`. Rewrite `h1` using `[hjk, he]`. Use `hN j hj i` as an intermediate fact.

Use `hN k hk i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (fun y => MvPowerSeries.map (algebraMap O R) ((∏ i, tchU n O i ^ (N : ℤ) : (MvPowerSeries (Fin n) O)ˣ) : MvPowerSeries (Fin n) O) * y) h`. Simplify using `only [mul_zero] at h1`. Rewrite `h1` using `[Finset.mul_sum]`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul, ← Units.val_mul, ht, ← Finset.prod_mul_distrib]`. Use `congr 1`. Establish `h2 : ∀ i, tchU n O i ^ (N : ℤ) * tchU n O i ^ (b.repr j i) = tchU n O i ^ (e j i)`.

Introduce `i`. Rewrite using `[← zpow_add, ← zpow_natCast, he, Int.toNat_of_nonneg (hN j hj i), add_comm]`. Simplify using `only [h2]`. Simplify using `[map_prod, tchU_val]`.
-/
theorem UpperTheory.V.Alg.tchar :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (n : ℕ) (t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ), (∀ j, constantCoeff (t j : MvPowerSeries (Fin n) O) = 1) ∧
      ∀ (R : Type) [CommRing R] [Algebra O R] (s : Finset X) (x : X → R),
        ∑ j ∈ s, MvPowerSeries.map (algebraMap O R) (t (Multiplicative.ofAdd j) : MvPowerSeries (Fin n) O) * C (x j) = 0 → ∀ j ∈ s, x j = 0 := by
  intro O _ _ X _ _ _
  classical
  let n := Module.finrank ℤ X
  let b : Module.Basis (Fin n) ℤ X := Module.finBasis ℤ X
  let t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ :=
    { toFun := fun j => ∏ i, tchU n O i ^ (b.repr j.toAdd i)
      map_one' := by simp
      map_mul' := by
        intro a c
        simp [zpow_add, Finset.prod_mul_distrib] }
  have ht : ∀ j : X, t (Multiplicative.ofAdd j) = ∏ i, tchU n O i ^ (b.repr j i) := fun j => rfl
  refine ⟨n, t, ?_, ?_⟩
  · intro j
    have h1 : ∀ i, Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (tchU n O i) = 1 := by
      intro i
      ext
      simp [tchU_val]
    have h2 : Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (t j) = 1 := by
      have := ht j.toAdd
      rw [ofAdd_toAdd] at this
      rw [this, map_prod]
      simp only [map_zpow, h1, one_zpow, Finset.prod_const_one]
    simpa using congrArg Units.val h2
  · intro R _ _ s x h
    let N : ℕ := ∑ j ∈ s, ∑ i, (b.repr j i).natAbs
    have hN : ∀ j ∈ s, ∀ i, 0 ≤ b.repr j i + N := by
      intro j hj i
      have h1 : (b.repr j i).natAbs ≤ ∑ i, (b.repr j i).natAbs :=
        Finset.single_le_sum (f := fun i => (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : ∑ i, (b.repr j i).natAbs ≤ N :=
        Finset.single_le_sum (f := fun j => ∑ i, (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) hj
      omega
    let e : X → Fin n →₀ ℕ := fun j => Finsupp.equivFunOnFinite.symm fun i => (b.repr j i + N).toNat
    have he : ∀ j i, e j i = (b.repr j i + N).toNat := fun j i => rfl
    refine tch_poly n R s x e ?_ ?_
    · intro j hj k hk hjk
      apply b.repr.injective
      ext i
      have h1 := he j i
      rw [hjk, he] at h1
      have := hN j hj i
      have := hN k hk i
      omega
    · have h1 := congrArg (fun y => MvPowerSeries.map (algebraMap O R)
        ((∏ i, tchU n O i ^ (N : ℤ) : (MvPowerSeries (Fin n) O)ˣ) : MvPowerSeries (Fin n) O) * y) h
      simp only [mul_zero] at h1
      rw [Finset.mul_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, ht, ← Finset.prod_mul_distrib]
      congr 1
      have h2 : ∀ i, tchU n O i ^ (N : ℤ) * tchU n O i ^ (b.repr j i) = tchU n O i ^ (e j i) := by
        intro i
        rw [← zpow_add, ← zpow_natCast, he, Int.toNat_of_nonneg (hN j hj i), add_comm]
      simp only [h2]
      simp [map_prod, tchU_val]
