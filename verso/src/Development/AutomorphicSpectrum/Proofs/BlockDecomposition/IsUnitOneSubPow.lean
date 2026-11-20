import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimAlgProof

open Polynomial

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `hlift : ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 → ∃ φ : AdjoinRoot (cyclotomic q ℤ) →+* A, φ (AdjoinRoot.root _) = z`. Introduce `A _ z hz`. Establish `h : (cyclotomic q ℤ).eval₂ (Int.castRingHom A) z = 0`. Rewrite `hz` using `[aeval_def]`.

Simplify `hz` using `[eq_intCast]`. Conclude with `⟨AdjoinRoot.lift _ z h, AdjoinRoot.lift_root h⟩`. Use `haveI hdom : IsDomain (AdjoinRoot (cyclotomic q ℤ)) := AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hq).prime`. Use `⟨AdjoinRoot (cyclotomic q ℤ), inferInstance, hdom, AdjoinRoot.root _, ?_, hlift⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `hlift ℂ (Complex.exp (2 * Real.pi * Complex.I / q)) (by`.

Establish `hp` using `Complex.isPrimitiveRoot_exp q (NeZero.ne q)`. Establish `: IsRoot (cyclotomic q ℂ) (Complex.exp (2 * Real.pi * Complex.I / q))` using `(isRoot_cyclotomic_iff).2 hp`. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `this)`. Use `haveI : NeZero ((q : ℕ) : AdjoinRoot (cyclotomic q ℤ)) := ⟨fun h0 => by`.

Use `congrArg ψ h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `NeZero.ne q (by exact_mod_cast this)⟩`. Use `(isRoot_cyclotomic_iff).1 ?_` and prove the remaining obligations. Establish `h` using `AdjoinRoot.eval₂_root (cyclotomic q ℤ)`.

Rewrite `h` using `[eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `h`.
-/
theorem exists_universal (q : ℕ) [NeZero q] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ξ : R), IsPrimitiveRoot ξ q ∧
      ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
        ∃ φ : R →+* A, φ ξ = z := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlift : ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
      ∃ φ : AdjoinRoot (cyclotomic q ℤ) →+* A, φ (AdjoinRoot.root _) = z := by
    intro A _ z hz
    have h : (cyclotomic q ℤ).eval₂ (Int.castRingHom A) z = 0 := by
      rw [aeval_def] at hz
      simpa [eq_intCast] using hz
    exact ⟨AdjoinRoot.lift _ z h, AdjoinRoot.lift_root h⟩
  haveI hdom : IsDomain (AdjoinRoot (cyclotomic q ℤ)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hq).prime
  refine ⟨AdjoinRoot (cyclotomic q ℤ), inferInstance, hdom, AdjoinRoot.root _, ?_, hlift⟩
  obtain ⟨ψ, hψ⟩ := hlift ℂ (Complex.exp (2 * Real.pi * Complex.I / q)) (by
    have hp := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
    have : IsRoot (cyclotomic q ℂ) (Complex.exp (2 * Real.pi * Complex.I / q)) :=
      (isRoot_cyclotomic_iff).2 hp
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact this)
  haveI : NeZero ((q : ℕ) : AdjoinRoot (cyclotomic q ℤ)) := ⟨fun h0 => by
    have := congrArg ψ h0
    rw [map_natCast, map_zero] at this
    exact NeZero.ne q (by exact_mod_cast this)⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  have h := AdjoinRoot.eval₂_root (cyclotomic q ℤ)
  rw [eval₂_eq_eval_map, map_cyclotomic] at h
  exact h

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Rewrite using `[X_pow_sub_one_eq_prod hq hξ]`. Use `symm`. Use `Finset.prod_bij (fun a _ => ξ ^ a.val) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`.

Rewrite using `[mem_nthRootsFinset hq]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]`. Introduce `a _ b _ h`. Conclude with `ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)`. Introduce `μ hμ`.

Rewrite `hμ` using `[mem_nthRootsFinset hq]`. Take `⟨i, hi, rfl⟩` from `hξ.eq_pow_of_pow_eq_one hμ`. Conclude with `⟨(i : ZMod q), Finset.mem_univ _, by rw [ZMod.val_cast_of_lt hi]⟩`. Introduce `a _`. Both sides reduce to the same expression.
-/
theorem X_pow_sub_one_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    (X ^ q - 1 : R[X]) = ∏ a : ZMod q, (X - C (ξ ^ a.val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [X_pow_sub_one_eq_prod hq hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ a.val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_nthRootsFinset hq]
    rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  · intro a _ b _ h
    exact ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  · intro μ hμ
    rw [mem_nthRootsFinset hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ
    exact ⟨(i : ZMod q), Finset.mem_univ _, by rw [ZMod.val_cast_of_lt hi]⟩
  · intro a _
    rfl

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Rewrite using `[cyclotomic_eq_prod_X_sub_primitiveRoots hξ]`. Use `symm`. Use `Finset.prod_bij (fun a _ => ξ ^ (a : ZMod q).val) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`.

Rewrite using `[mem_primitiveRoots hq]`. Conclude with `hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)`. Introduce `a _ b _ h`. Conclude with `Units.ext (ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))`. Introduce `μ hμ`.

Rewrite `hμ` using `[mem_primitiveRoots hq]`. Take `⟨i, hi, rfl⟩` from `hξ.eq_pow_of_pow_eq_one hμ.pow_eq_one`. Establish `hc : Nat.Coprime i q` using `(hξ.pow_iff_coprime hq i).1 hμ`. Use `⟨ZMod.unitOfCoprime i hc, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Simplify using `only [ZMod.coe_unitOfCoprime]`.

Rewrite using `[ZMod.val_cast_of_lt hi]`. Introduce `a _`. Both sides reduce to the same expression.
-/
theorem cyclotomic_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    cyclotomic q R = ∏ a : (ZMod q)ˣ, (X - C (ξ ^ (a : ZMod q).val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_primitiveRoots hq]
    exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hc : Nat.Coprime i q := (hξ.pow_iff_coprime hq i).1 hμ
    refine ⟨ZMod.unitOfCoprime i hc, Finset.mem_univ _, ?_⟩
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_cast_of_lt hi]
  · intro a _
    rfl

/- English proof (translation)
Establish `h` using `congrArg φ hξ.prod_one_sub_pow_eq_order`. Rewrite `h` using `[map_prod]`. Establish `hn : φ ((n : R) + 1) = ((n + 1 : ℕ) : A)` using `by simp`. Establish `hd : φ (1 - ξ ^ (k + 1)) ∣ ∏ i ∈ Finset.range n, φ (1 - ξ ^ (i + 1))` using `Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)`. Rewrite `hd` using `[h, hn]`.

Use `isUnit_of_dvd_unit hd hu` as an intermediate fact. Simplify using `using this`.
-/
theorem isUnit_one_sub_pow {R A : Type} [CommRing R] [IsDomain R] [CommRing A] (n : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (n + 1)) (φ : R →+* A) (hu : IsUnit ((n + 1 : ℕ) : A))
    (k : ℕ) (hk : k < n) : IsUnit (1 - φ ξ ^ (k + 1)) := by
  have h := congrArg φ hξ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  have hn : φ ((n : R) + 1) = ((n + 1 : ℕ) : A) := by simp
  have hd : φ (1 - ξ ^ (k + 1)) ∣ ∏ i ∈ Finset.range n, φ (1 - ξ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)
  rw [h, hn] at hd
  have := isUnit_of_dvd_unit hd hu
  simpa using this

/- English proof (translation)
Introduce `q _ A _ ζ`. Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Take `⟨R, _, _, ξ, hξ, hl⟩` from `exists_universal q`. Take `⟨φ, hφ⟩` from `hl A ζ.1 ζ.2.2`. Establish `hpow : ζ.1 ^ q = 1` using `by rw [← hφ, ← map_pow, hξ.pow_eq_one, map_one]`.

Establish `hζu : IsUnit ζ.1`. Use `IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) ?_` and prove the remaining obligations. Rewrite using `[← pow_succ', Nat.sub_add_cancel hq, hpow]`. Establish `h1 : ∀ k, 0 < k → k < q → IsUnit (1 - ζ.1 ^ k)`. Introduce `k hk0 hkq`.

Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hk0.ne'`. Substitute `hn` using the available equality. Use `isUnit_one_sub_pow n hξ φ ζ.2.1 m (by omega)` as an intermediate fact. Rewrite `this` using `[hφ]`. Then use the resulting hypothesis.

Establish `hlt : ∀ a b : ℕ, a < b → b < q → IsUnit (ζ.1 ^ a - ζ.1 ^ b)`. Introduce `a b hab hb`. Establish `: ζ.1 ^ a - ζ.1 ^ b = ζ.1 ^ a * (1 - ζ.1 ^ (b - a))`. Rewrite using `[mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]`. Rewrite using `[this]`.

Conclude with `(hζu.pow a).mul (h1 _ (by omega) (by omega))`. Use `⟨hpow, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `hv : a.val ≠ b.val` using `fun h => hab (ZMod.val_injective q h)`. Break down `lt_or_gt_of_ne hv with h | h` into its components or cases.

Conclude with `hlt _ _ h (ZMod.val_lt b)`. Use `(hlt _ _ h (ZMod.val_lt a)).neg` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Introduce `r`. Establish `h` using `congrArg (fun p => eval r (p.map φ)) (X_pow_sub_one_eq q hξ)`.

Simplify `h` using `[Polynomial.map_prod, eval_prod, hφ]`. Introduce `r`. Establish `h` using `congrArg (fun p => eval r (p.map φ)) (cyclotomic_eq q hξ)`. Simplify using `only [map_cyclotomic, Polynomial.map_prod, eval_prod] at h`. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic, h]`.

Simplify using `[hφ]`.
-/
theorem primAlg : CrystallineSemistableComparison.E.PrimAlg := by
  intro q _ A _ ζ
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨R, _, _, ξ, hξ, hl⟩ := exists_universal q
  obtain ⟨φ, hφ⟩ := hl A ζ.1 ζ.2.2
  have hpow : ζ.1 ^ q = 1 := by rw [← hφ, ← map_pow, hξ.pow_eq_one, map_one]
  have hζu : IsUnit ζ.1 := by
    refine IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) ?_
    rw [← pow_succ', Nat.sub_add_cancel hq, hpow]
  have h1 : ∀ k, 0 < k → k < q → IsUnit (1 - ζ.1 ^ k) := by
    intro k hk0 hkq
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    subst hn
    have := isUnit_one_sub_pow n hξ φ ζ.2.1 m (by omega)
    rwa [hφ] at this
  have hlt : ∀ a b : ℕ, a < b → b < q → IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
    intro a b hab hb
    have : ζ.1 ^ a - ζ.1 ^ b = ζ.1 ^ a * (1 - ζ.1 ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this]
    exact (hζu.pow a).mul (h1 _ (by omega) (by omega))
  refine ⟨hpow, ?_, ?_, ?_⟩
  · intro a b hab
    have hv : a.val ≠ b.val := fun h => hab (ZMod.val_injective q h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact hlt _ _ h (ZMod.val_lt b)
    · have := (hlt _ _ h (ZMod.val_lt a)).neg
      rwa [neg_sub] at this
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (X_pow_sub_one_eq q hξ)
    simpa [Polynomial.map_prod, eval_prod, hφ] using h
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (cyclotomic_eq q hξ)
    simp only [map_cyclotomic, Polynomial.map_prod, eval_prod] at h
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, h]
    simp [hφ]

end GlobalTheory.CompanionTheory.PrimAlgProof
