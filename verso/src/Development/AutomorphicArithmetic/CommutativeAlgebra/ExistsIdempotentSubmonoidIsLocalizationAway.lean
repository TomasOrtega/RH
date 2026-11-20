import Mathlib

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

/- English proof (translation)
Introduce `R B L B' _ _ _ _ e he T hT _ _ _ _ _ _ jB hj`. Use `letI : Algebra R B' := ((algebraMap L B').comp (algebraMap R L)).toAlgebra`. Use `haveI : IsScalarTower R L B' := IsScalarTower.of_algebraMap_eq' rfl`. Use `letI : Algebra B B' := jB.toAlgebra`. Use `haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq (fun r => (hj r).symm)`.

Establish `hloc : IsLocalization (T ⊔ Submonoid.powers e) B'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Take `⟨y, hy, z, ⟨n, rfl⟩, rfl⟩` from `Submonoid.mem_sup.mp hx`. Establish `h1` using `(IsLocalization.map_units L ⟨y, hy⟩).map (algebraMap L B')`.

Establish `h2` using `IsLocalization.map_units B' (⟨algebraMap R L e ^ n, n, rfl⟩ : Submonoid.powers (algebraMap R L e))`. Simplify using `only [IsScalarTower.algebraMap_apply R L B', map_mul, map_pow] at h1 h2 ⊢`. Conclude with `h1.mul h2`. Introduce `z`. Take `⟨⟨a, ⟨_, n, rfl⟩⟩, h1⟩` from `IsLocalization.surj (Submonoid.powers (algebraMap R L e)) z`.

Take `⟨⟨r, t⟩, h2⟩` from `IsLocalization.surj T a`. Use `⟨⟨r, ⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only at h1 h2 ⊢`. Rewrite using `[IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' r, ← h2]`. Simplify using `only [map_mul, map_pow] at h1 ⊢`.

Take the linear combination `(algebraMap L B' (algebraMap R L t)) * h1`. Introduce `x y hxy`. Rewrite `hxy` using `[IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' y]`. Take `⟨⟨_, n, rfl⟩, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R L e)) B').mp hxy`. Simplify using `only at hc`.

Rewrite `hc` using `[← map_pow, ← map_mul, ← map_mul, IsLocalization.eq_iff_exists T L]`. Take `⟨t, ht⟩` from `hc`. Use `⟨⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Take the linear combination `ht`.

Establish `key` using `IsLocalization.isLocalization_of_submonoid_le B B' (Submonoid.powers e) (T ⊔ Submonoid.powers e) le_sup_right`. Use `⟨(T ⊔ Submonoid.powers e).map (algebraMap R B), ?_, key⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, hy, z, ⟨n, rfl⟩, rfl⟩` from `Submonoid.mem_sup.mp hx`. Conclude with `((hT y hy).mul (he.pow n)).map (algebraMap R B)`.
-/
theorem UpperTheory.exists_idempotent_submonoid_isLocalization_away :
    ∀ {R B L B' : Type} [CommRing R] [CommRing B] [CommRing L] [CommRing B'] (e : R), IsIdempotentElem e →
        ∀ (T : Submonoid R), (∀ s ∈ T, IsIdempotentElem s) →
        ∀ [Algebra R B] [IsLocalization.Away e B] [Algebra R L] [IsLocalization T L] [Algebra L B']
          [IsLocalization.Away (algebraMap R L e) B'] (jB : B →+* B'),
        (∀ r, jB (algebraMap R B r) = algebraMap L B' (algebraMap R L r)) →
        ∃ S : Submonoid B, (∀ s ∈ S, IsIdempotentElem s) ∧ @IsLocalization B _ S B' _ jB.toAlgebra := by
  intro R B L B' _ _ _ _ e he T hT _ _ _ _ _ _ jB hj
  letI : Algebra R B' := ((algebraMap L B').comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B B' := jB.toAlgebra
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq (fun r => (hj r).symm)
  have hloc : IsLocalization (T ⊔ Submonoid.powers e) B' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
      have h1 := (IsLocalization.map_units L ⟨y, hy⟩).map (algebraMap L B')
      have h2 := IsLocalization.map_units B'
        (⟨algebraMap R L e ^ n, n, rfl⟩ : Submonoid.powers (algebraMap R L e))
      simp only [IsScalarTower.algebraMap_apply R L B', map_mul, map_pow] at h1 h2 ⊢
      exact h1.mul h2
    · intro z
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h1⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R L e)) z
      obtain ⟨⟨r, t⟩, h2⟩ := IsLocalization.surj T a
      refine ⟨⟨r, ⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩⟩, ?_⟩
      simp only at h1 h2 ⊢
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' r, ← h2]
      simp only [map_mul, map_pow] at h1 ⊢
      linear_combination (algebraMap L B' (algebraMap R L t)) * h1
    · intro x y hxy
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' y] at hxy
      obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R L e)) B').mp hxy
      simp only at hc
      rw [← map_pow, ← map_mul, ← map_mul, IsLocalization.eq_iff_exists T L] at hc
      obtain ⟨t, ht⟩ := hc
      refine ⟨⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩, ?_⟩
      simp only
      linear_combination ht
  have key := IsLocalization.isLocalization_of_submonoid_le B B' (Submonoid.powers e)
    (T ⊔ Submonoid.powers e) le_sup_right
  refine ⟨(T ⊔ Submonoid.powers e).map (algebraMap R B), ?_, key⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
  exact ((hT y hy).mul (he.pow n)).map (algebraMap R B)
