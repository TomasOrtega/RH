import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.FiniteStability

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped TensorProduct

/- English proof (translation)
Use `haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)`. Establish `hj : Q.jacobson = Q` using `IsJacobsonRing.out inferInstance hQ.isRadical`. Rewrite `hx` using `[← hj, Ideal.jacobson, Ideal.mem_sInf]`. Use `push Not at hx`. Take `⟨M, ⟨hQM, hM⟩, hxM⟩` from `hx`.

Use `letI : Field (R ⧸ M) := Ideal.Quotient.field M`. Use `haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)`. Use `haveI : Algebra.IsAlgebraic K (R ⧸ M) := Algebra.IsAlgebraic.of_finite K _`. Set `e : (R ⧸ M) →ₐ[K] K` to `IsAlgClosed.lift`. Use `⟨e.comp (Ideal.Quotient.mkₐ K M), fun y hy => ?_, ?_⟩` and prove the remaining obligations.

Establish `: Ideal.Quotient.mk M y = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (hQM hy)`. Simplify using `[this]`. Establish `: Ideal.Quotient.mk M x ≠ 0` using `fun h => hxM (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Simplify using `using this`.
-/
private theorem ns_point (K R : Type) [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (Q : Ideal R) (hQ : Q.IsPrime) (x : R) (hx : x ∉ Q) :
    ∃ ψ : R →ₐ[K] K, (∀ y ∈ Q, ψ y = 0) ∧ ψ x ≠ 0 := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hj : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hx
  push Not at hx
  obtain ⟨M, ⟨hQM, hM⟩, hxM⟩ := hx
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  haveI : Algebra.IsAlgebraic K (R ⧸ M) := Algebra.IsAlgebraic.of_finite K _
  let e : (R ⧸ M) →ₐ[K] K := IsAlgClosed.lift
  refine ⟨e.comp (Ideal.Quotient.mkₐ K M), fun y hy => ?_, ?_⟩
  · have : Ideal.Quotient.mk M y = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hQM hy)
    simp [this]
  · have : Ideal.Quotient.mk M x ≠ 0 := fun h => hxM (Ideal.Quotient.eq_zero_iff_mem.1 h)
    simpa using this

/- English proof (translation)
Set `p : Ideal B` to `P.under B`. Use `haveI : p.IsPrime := inferInstance`. Establish `h1 : p ≤ RingHom.ker (algebraMap B K)` using `fun b hb => (hP b).1 hb`. Establish `h2 : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap B K)` using `fun b hb => (isUnit_iff_ne_zero.2 (fun h => hb ((hP b).2 h)) : IsUnit (algebraMap B K b))`. Establish `h1' : p ≤ RingHom.ker (algebraMap B P.ResidueField)` using `fun b hb => by`.

Rewrite using `[RingHom.mem_ker, IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero]`. Conclude with `hb`. Establish `h2' : p.primeCompl ≤ (IsUnit.submonoid P.ResidueField).comap (algebraMap B P.ResidueField)` using `fun b hb => (isUnit_iff_ne_zero.2 (fun h => hb (by`. Rewrite `h` using `[IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero]`. Conclude with `h)) : IsUnit (algebraMap B P.ResidueField b))`.

Use `letI aK : Algebra p.ResidueField K := (Ideal.ResidueField.lift p _ h1 h2).toAlgebra`. Use `letI aL : Algebra p.ResidueField P.ResidueField := (Ideal.ResidueField.lift p _ h1' h2').toAlgebra`. Use `haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun b => (Ideal.ResidueField.lift_algebraMap p _ h1 h2 b).symm`. Use `haveI : IsScalarTower B p.ResidueField P.ResidueField := IsScalarTower.of_algebraMap_eq fun b => (Ideal.ResidueField.lift_algebraMap p _ h1' h2' b).symm`. Set `T` to `K ⊗[p.ResidueField] P.ResidueField`.

Use `haveI : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain p.ResidueField K P.ResidueField (RingHom.injective _) (RingHom.injective _)`. Take `⟨N, hN⟩` from `Ideal.exists_maximal T`. Set `i1 : K →ₐ[B] T` to `(Algebra.TensorProduct.includeLeft (S := B))`. Set `j : P.ResidueField →ₐ[p.ResidueField] T` to `Algebra.TensorProduct.includeRight`. Set `i2 : A →ₐ[B] T` to `(j.restrictScalars B).comp (IsScalarTower.toAlgHom B A P.ResidueField)`.

Set `φ : K ⊗[B] A →ₐ[B] T` to `Algebra.TensorProduct.lift i1 i2 (fun _ _ => Commute.all _ _)`. Use `⟨N.comap φ, Ideal.comap_isPrime _ _, fun a => ?_⟩` and prove the remaining obligations. Establish `hφ : φ ((1 : K) ⊗ₜ[B] a) = j (algebraMap A P.ResidueField a)`. Simplify using `[φ, i2]`. Rewrite using `[Ideal.mem_comap, hφ]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `ha`. Establish `hu : IsUnit (algebraMap A P.ResidueField a)` using `isUnit_iff_ne_zero.2 (fun h => ha (Ideal.algebraMap_residueField_eq_zero.1 h))`. Conclude with `hN.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.map j))`.

Introduce `h`. Rewrite using `[Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]`. Conclude with `N.zero_mem`.
-/
private theorem ns_prime (B A K : Type) [CommRing B] [CommRing A] [Field K] [Algebra B A] [Algebra B K]
    (P : Ideal A) [P.IsPrime] (hP : ∀ b, algebraMap B A b ∈ P ↔ algebraMap B K b = 0) :
    ∃ Q : Ideal (K ⊗[B] A), Q.IsPrime ∧ ∀ a : A, (1 : K) ⊗ₜ[B] a ∈ Q ↔ a ∈ P := by
  let p : Ideal B := P.under B
  haveI : p.IsPrime := inferInstance
  have h1 : p ≤ RingHom.ker (algebraMap B K) := fun b hb => (hP b).1 hb
  have h2 : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap B K) := fun b hb =>
    (isUnit_iff_ne_zero.2 (fun h => hb ((hP b).2 h)) : IsUnit (algebraMap B K b))
  have h1' : p ≤ RingHom.ker (algebraMap B P.ResidueField) := fun b hb => by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero]
    exact hb
  have h2' : p.primeCompl ≤ (IsUnit.submonoid P.ResidueField).comap (algebraMap B P.ResidueField) :=
    fun b hb => (isUnit_iff_ne_zero.2 (fun h => hb (by
      rw [IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero] at h
      exact h)) : IsUnit (algebraMap B P.ResidueField b))
  letI aK : Algebra p.ResidueField K := (Ideal.ResidueField.lift p _ h1 h2).toAlgebra
  letI aL : Algebra p.ResidueField P.ResidueField := (Ideal.ResidueField.lift p _ h1' h2').toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1 h2 b).symm
  haveI : IsScalarTower B p.ResidueField P.ResidueField := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1' h2' b).symm
  let T := K ⊗[p.ResidueField] P.ResidueField
  haveI : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    p.ResidueField K P.ResidueField (RingHom.injective _) (RingHom.injective _)
  obtain ⟨N, hN⟩ := Ideal.exists_maximal T
  let i1 : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft (S := B))
  let j : P.ResidueField →ₐ[p.ResidueField] T := Algebra.TensorProduct.includeRight
  let i2 : A →ₐ[B] T := (j.restrictScalars B).comp (IsScalarTower.toAlgHom B A P.ResidueField)
  let φ : K ⊗[B] A →ₐ[B] T := Algebra.TensorProduct.lift i1 i2 (fun _ _ => Commute.all _ _)
  refine ⟨N.comap φ, Ideal.comap_isPrime _ _, fun a => ?_⟩
  have hφ : φ ((1 : K) ⊗ₜ[B] a) = j (algebraMap A P.ResidueField a) := by
    simp [φ, i2]
  rw [Ideal.mem_comap, hφ]
  constructor
  · intro h
    by_contra ha
    have hu : IsUnit (algebraMap A P.ResidueField a) :=
      isUnit_iff_ne_zero.2 (fun h => ha (Ideal.algebraMap_residueField_eq_zero.1 h))
    exact hN.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.map j))
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
    exact N.zero_mem

/- English proof (translation)
Introduce `O B A K _ _ _ _ _ _ _ _ _ _ _ σ J f h0 h1`. Set `S : Submonoid A` to `{ carrier := {a | ∃ (b : B) (n : ℕ), σ b ≠ 0 ∧ a = algebraMap B A b * f ^ n} one_mem' := ⟨1, 0, by simp, by simp⟩ mul_mem' := by`. Introduce and unpack `_ _ ⟨b, n, hb, rfl⟩ ⟨c, m, hc, rfl⟩`. Conclude with `⟨b * c, n + m, by simp [hb, hc], by rw [map_mul]; ring⟩ }`. Establish `hd : Disjoint (J : Set A) (S : Set A)`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ha ⟨b, n, hb, rfl⟩`. Conclude with `h1 b n hb ha`. Take `⟨P, hP, hJP, hPS⟩` from `Ideal.exists_le_prime_disjoint J S hd`. Rewrite `hPS` using `[Set.disjoint_left]`.

Use `letI : Algebra B K := σ.toRingHom.toAlgebra`. Establish `hσ : ∀ b, algebraMap B K b = σ b` using `fun _ => rfl`. Use `haveI : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun o => by`. Rewrite using `[hσ, AlgHom.commutes]`. Take `⟨Q, hQ, hQP⟩` from `ns_prime B A K P (fun b => by`.

Rewrite using `[hσ]`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Assume the negation of the conclusion as `hne`. Conclude with `hPS hb ⟨b, 0, hne, by simp⟩`.

Introduce `hb`. Conclude with `hJP (h0 b hb))`. Establish `hf : f ∉ P` using `fun h => hPS h ⟨1, 1, by simp, by simp⟩`. Take `⟨ψ, hψ0, hψ1⟩` from `ns_point K (K ⊗[B] A) Q hQ ((1 : K) ⊗ₜ[B] f) (fun h => hf ((hQP f).1 h))`. Set `ξ : A →ₐ[B] K` to `(ψ.restrictScalars B).comp Algebra.TensorProduct.includeRight`.

Use `⟨ξ.restrictScalars O, fun b => ?_, fun g hg => ?_, hψ1⟩` and prove the remaining obligations. Conclude with `(ξ.commutes b).trans (hσ b)`. Conclude with `hψ0 _ ((hQP g).2 (hJP hg))`.
-/
theorem UpperTheory.V.Alg.M.ns_holds :
    ∀ (O B A K : Type) [CommRing O] [CommRing B] [CommRing A] [Field K] [IsAlgClosed K] [Algebra O B] [Algebra B A]
      [Algebra O A] [IsScalarTower O B A] [Algebra O K] [Algebra.FiniteType B A] (σ : B →ₐ[O] K) (J : Ideal A) (f : A),
      (∀ b, σ b = 0 → algebraMap B A b ∈ J) → (∀ (b : B) (n : ℕ), σ b ≠ 0 → algebraMap B A b * f ^ n ∉ J) →
      ∃ ξ : A →ₐ[O] K, (∀ b, ξ (algebraMap B A b) = σ b) ∧ (∀ g ∈ J, ξ g = 0) ∧ ξ f ≠ 0 := by
  intro O B A K _ _ _ _ _ _ _ _ _ _ _ σ J f h0 h1
  let S : Submonoid A :=
    { carrier := {a | ∃ (b : B) (n : ℕ), σ b ≠ 0 ∧ a = algebraMap B A b * f ^ n}
      one_mem' := ⟨1, 0, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, n, hb, rfl⟩ ⟨c, m, hc, rfl⟩
        exact ⟨b * c, n + m, by simp [hb, hc], by rw [map_mul]; ring⟩ }
  have hd : Disjoint (J : Set A) (S : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ha ⟨b, n, hb, rfl⟩
    exact h1 b n hb ha
  obtain ⟨P, hP, hJP, hPS⟩ := Ideal.exists_le_prime_disjoint J S hd
  rw [Set.disjoint_left] at hPS
  letI : Algebra B K := σ.toRingHom.toAlgebra
  have hσ : ∀ b, algebraMap B K b = σ b := fun _ => rfl
  haveI : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun o => by
    rw [hσ, AlgHom.commutes]
  obtain ⟨Q, hQ, hQP⟩ := ns_prime B A K P (fun b => by
    rw [hσ]
    constructor
    · intro hb
      by_contra hne
      exact hPS hb ⟨b, 0, hne, by simp⟩
    · intro hb
      exact hJP (h0 b hb))
  have hf : f ∉ P := fun h => hPS h ⟨1, 1, by simp, by simp⟩
  obtain ⟨ψ, hψ0, hψ1⟩ := ns_point K (K ⊗[B] A) Q hQ ((1 : K) ⊗ₜ[B] f) (fun h => hf ((hQP f).1 h))
  let ξ : A →ₐ[B] K := (ψ.restrictScalars B).comp Algebra.TensorProduct.includeRight
  refine ⟨ξ.restrictScalars O, fun b => ?_, fun g hg => ?_, hψ1⟩
  · exact (ξ.commutes b).trans (hσ b)
  · exact hψ0 _ ((hQP g).2 (hJP hg))
