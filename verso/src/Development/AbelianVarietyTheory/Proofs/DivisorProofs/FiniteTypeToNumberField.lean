import Mathlib
open scoped TensorProduct Polynomial

namespace GlobalTheory

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal R`. Use `letI : Field (R ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Algebra.FiniteType ℚ (R ⧸ m) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) Ideal.Quotient.mk_surjective`. Use `haveI : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)`. Use `haveI : CharZero (R ⧸ m) := algebraRat.charZero _`.

Establish `hfin` using `(inferInstance : Module.Finite ℚ (R ⧸ m))`. Use `haveI : @FiniteDimensional ℚ (R ⧸ m) _ _ (@Algebra.toModule ℚ (R ⧸ m) _ _ DivisionRing.toRatAlgebra) := by`. Establish `e : (Ideal.Quotient.algebra ℚ : Algebra ℚ (R ⧸ m)) = DivisionRing.toRatAlgebra` using `Subsingleton.elim _ _`. Use `hfin` and compare the differences between its conclusion and the goal. Use `first`.

Consider the case `exact (congrArg (@Algebra.toModule ℚ (R ⧸ m) _ _) e).symm`. Consider the case `(rw [← e]; rfl)`. Use `haveI : NumberField (R ⧸ m) := ⟨⟩`. Conclude with `⟨R ⧸ m, inferInstance, inferInstance, Ideal.Quotient.mk m, trivial⟩`.
-/
theorem exists_numberField_of_finiteType_rat (R : Type) [CommRing R] [Nontrivial R] [Algebra ℚ R]
    [Algebra.FiniteType ℚ R] : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : R →+* K), True := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  haveI : CharZero (R ⧸ m) := algebraRat.charZero _
  have hfin := (inferInstance : Module.Finite ℚ (R ⧸ m))
  haveI : @FiniteDimensional ℚ (R ⧸ m) _ _ (@Algebra.toModule ℚ (R ⧸ m) _ _ DivisionRing.toRatAlgebra) := by
    have e : (Ideal.Quotient.algebra ℚ : Algebra ℚ (R ⧸ m)) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    convert hfin
    first
      | exact (congrArg (@Algebra.toModule ℚ (R ⧸ m) _ _) e).symm
      | (rw [← e]; rfl)
  haveI : NumberField (R ⧸ m) := ⟨⟩
  exact ⟨R ⧸ m, inferInstance, inferInstance, Ideal.Quotient.mk m, trivial⟩

/- English proof (translation)
Introduce `A _ _ _ hA a ha`. Take `⟨s, hs⟩` from `hA.out`. Set `F` to `FractionRing A`. Set `f : A →+* F` to `algebraMap A F`. Set `B : Subalgebra ℚ F` to `Algebra.adjoin ℚ (insert (f a)⁻¹ ((s.image f : Finset F) : Set F))`.

Establish `hmem : ∀ x : A, f x ∈ B`. Introduce `x`. Establish `hx : x ∈ Algebra.adjoin ℤ (s : Set A)` using `by rw [hs]; trivial`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Conclude with `Algebra.subset_adjoin (Set.mem_insert_of_mem _ (by simpa using ⟨x, hx, rfl⟩))`. Consider the case `algebraMap n`. Establish `: f (algebraMap ℤ A n) = algebraMap ℚ F (n : ℚ)` using `by simp [f]`. Rewrite using `[this]`. Conclude with `B.algebraMap_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `B.add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `B.mul_mem hx hy`. Establish `hinv : (f a)⁻¹ ∈ B` using `Algebra.subset_adjoin (Set.mem_insert _ _)`.

Use `haveI hBft : Algebra.FiniteType ℚ B := by`. Rewrite using `[← Subalgebra.fg_iff_finiteType]`. Conclude with `⟨insert (f a)⁻¹ (s.image f), by simp [B]⟩`. Establish `hfa : f a ≠ 0`. Simplify `(IsFractionRing.injective A F).ne ha` using `[f]`.

Set `ψ : A →+* B` to `f.codRestrict B hmem`. Establish `hu : IsUnit (ψ a)`. Use `isUnit_iff_exists_inv.mpr ⟨⟨(f a)⁻¹, hinv⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show f a * (f a)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ hfa`.

Take `⟨K, _, _, φ, -⟩` from `exists_numberField_of_finiteType_rat B`. Conclude with `⟨K, inferInstance, inferInstance, φ.comp ψ, (hu.map φ).ne_zero⟩`.
-/
theorem exists_numberField_point_ne_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A →
      ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  intro A _ _ _ hA a ha
  classical
  obtain ⟨s, hs⟩ := hA.out
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  let B : Subalgebra ℚ F := Algebra.adjoin ℚ (insert (f a)⁻¹ ((s.image f : Finset F) : Set F))
  have hmem : ∀ x : A, f x ∈ B := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap n =>
      have : f (algebraMap ℤ A n) = algebraMap ℚ F (n : ℚ) := by simp [f]
      rw [this]; exact B.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
  have hinv : (f a)⁻¹ ∈ B := Algebra.subset_adjoin (Set.mem_insert _ _)
  haveI hBft : Algebra.FiniteType ℚ B := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨insert (f a)⁻¹ (s.image f), by simp [B]⟩
  have hfa : f a ≠ 0 := by
    simpa [f] using (IsFractionRing.injective A F).ne ha
  let ψ : A →+* B := f.codRestrict B hmem
  have hu : IsUnit (ψ a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f a)⁻¹, hinv⟩, Subtype.ext ?_⟩
    show f a * (f a)⁻¹ = 1
    exact mul_inv_cancel₀ hfa
  obtain ⟨K, _, _, φ, -⟩ := exists_numberField_of_finiteType_rat B
  exact ⟨K, inferInstance, inferInstance, φ.comp ψ, (hu.map φ).ne_zero⟩

end GlobalTheory
