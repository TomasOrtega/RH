import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

namespace GlobalTheory

open IsDiscreteValuationRing

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `h0 : algebraMap O O' ϖ ≠ 0`. Introduce `h`. Conclude with `hϖ.ne_zero (hinj (by simpa using h))`. Establish `h1 : addVal O' (algebraMap O O' ϖ) ≠ ⊤`.

Rewrite using `[Ne, addVal_eq_top_iff]` and apply the resulting hypothesis. Establish `h2 : addVal O' (algebraMap O O' ϖ) ≠ 0`. Rewrite using `[Ne, addVal_eq_zero_iff]`. Introduce `h`. Conclude with `hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)`.

Take `⟨e, he⟩` from `ENat.ne_top_iff_exists.1 h1`. Use `⟨e, ?_, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `h2 (by rw [← he]; rfl)`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`. Establish `hv : addVal O x = n` using `addVal_def x u hϖ n hu`. Establish `hu0 : addVal O' (algebraMap O O' (u : O)) = 0`.

Rewrite using `[addVal_eq_zero_iff]`. Conclude with `u.isUnit.map _`. Establish `hv' : addVal O' (algebraMap O O' x) = ((e * n : ℕ) : ℕ∞)`. Rewrite using `[hu, map_mul, map_pow, addVal_mul, addVal_pow, hu0, ← he, zero_add, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hv, hv', ENat.toNat_natCast, ENat.toNat_natCast]`.
-/
theorem exists_toNat_addVal_algebraMap_eq_mul (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [Algebra O O'] [IsLocalHom (algebraMap O O')] (hinj : Function.Injective (algebraMap O O')) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ x : O,
      (addVal O' (algebraMap O O' x)).toNat = e * (addVal O x).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : algebraMap O O' ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (hinj (by simpa using h))
  have h1 : addVal O' (algebraMap O O' ϖ) ≠ ⊤ := by
    rwa [Ne, addVal_eq_top_iff]
  have h2 : addVal O' (algebraMap O O' ϖ) ≠ 0 := by
    rw [Ne, addVal_eq_zero_iff]
    intro h
    exact hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 h1
  refine ⟨e, ?_, fun x => ?_⟩
  · rintro rfl
    exact h2 (by rw [← he]; rfl)
  · by_cases hx : x = 0
    · subst hx
      simp
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
      have hv : addVal O x = n := addVal_def x u hϖ n hu
      have hu0 : addVal O' (algebraMap O O' (u : O)) = 0 := by
        rw [addVal_eq_zero_iff]
        exact u.isUnit.map _
      have hv' : addVal O' (algebraMap O O' x) = ((e * n : ℕ) : ℕ∞) := by
        rw [hu, map_mul, map_pow, addVal_mul, addVal_pow, hu0, ← he, zero_add, nsmul_eq_mul]
        push_cast
        ring
      rw [hv, hv', ENat.toNat_natCast, ENat.toNat_natCast]

/- English proof (translation)
Introduce `O _ _ _ O' _ _ _ _ _ hinj l x`. Take `⟨e, he, h⟩` from `exists_toNat_addVal_algebraMap_eq_mul O O' hinj`. Establish `hl : (l : O') = algebraMap O O' (l : O)` using `(map_natCast _ l).symm`. Unfold `Formalism.MainNotions.BlochKatoReduction.Gen.nval`. Rewrite using `[hl, h, h]`.

Use `push_cast`. Conclude with `mul_div_mul_left _ _ (by exact_mod_cast he)`.
-/
theorem nval_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  intro O _ _ _ O' _ _ _ _ _ hinj l x
  obtain ⟨e, he, h⟩ := exists_toNat_addVal_algebraMap_eq_mul O O' hinj
  have hl : (l : O') = algebraMap O O' (l : O) := (map_natCast _ l).symm
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hl, h, h]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

end GlobalTheory
