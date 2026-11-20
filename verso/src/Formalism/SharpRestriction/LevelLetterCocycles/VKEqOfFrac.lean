import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants

noncomputable section

namespace Formalism.MainNotions.TwOe

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible R'`. Establish `h0 : algebraMap R R' ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))`. Take `⟨e, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'`. Establish `hnu : ¬ IsUnit (algebraMap R R' ϖ)`.

Introduce `hu`. Establish `hmax` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (IsLocalRing.maximalIdeal R')`. Establish `heq` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `hmem : ϖ ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R')`. Rewrite using `[heq]`.

Conclude with `(IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hu`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Apply `hnu` to reduce the goal to its premises.

Rewrite using `[hw, pow_zero, mul_one]`. Conclude with `w.isUnit`. Use `⟨e, he, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality.

Rewrite using `[map_zero, AddValuation.map_zero, AddValuation.map_zero, ENat.mul_top (by exact_mod_cast he)]`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Rewrite using `[IsDiscreteValuationRing.addVal_def y u hϖ n hu]`. Establish `hy' : algebraMap R R' y = ↑(Units.map (algebraMap R R' : R →* R') u * w ^ n) * ϖ' ^ (e * n)`. Rewrite using `[hu, map_mul, map_pow, hw]`.

Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[IsDiscreteValuationRing.addVal_def _ _ hϖ' _ hy']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_ne_zero_addVal_algebraMap_eq_mul (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ y : R, IsDiscreteValuationRing.addVal R' (algebraMap R R' y) =
      (e : ℕ∞) * IsDiscreteValuationRing.addVal R y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have h0 : algebraMap R R' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap R R' ϖ) := by
    intro hu
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
      (IsLocalRing.maximalIdeal R')
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hmem : ϖ ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := by
      rw [heq]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hu
  have he : e ≠ 0 := by
    rintro rfl
    apply hnu
    rw [hw, pow_zero, mul_one]
    exact w.isUnit
  refine ⟨e, he, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, AddValuation.map_zero, AddValuation.map_zero, ENat.mul_top (by exact_mod_cast he)]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    rw [IsDiscreteValuationRing.addVal_def y u hϖ n hu]
    have hy' : algebraMap R R' y =
        ↑(Units.map (algebraMap R R' : R →* R') u * w ^ n) * ϖ' ^ (e * n) := by
      rw [hu, map_mul, map_pow, hw]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
      ring
    rw [IsDiscreteValuationRing.addVal_def _ _ hϖ' _ hy']
    push_cast
    ring

/- English proof (translation)
Take `⟨e, he, hE⟩` from `exists_ne_zero_addVal_algebraMap_eq_mul hinj`. Simplify using `only [nval]`. Rewrite using `[hE x, ← map_natCast (algebraMap R R') l, hE]`. Simplify using `only [ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul]`. Conclude with `mul_div_mul_left _ _ (by exact_mod_cast he)`.
-/
theorem nval_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) (x : R) :
    nval R' l (algebraMap R R' x) = nval R l x := by
  obtain ⟨e, he, hE⟩ := exists_ne_zero_addVal_algebraMap_eq_mul hinj
  simp only [nval]
  rw [hE x, ← map_natCast (algebraMap R R') l, hE]
  simp only [ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

/- English proof (translation)
Simplify using `only [nval]`. Rewrite using `[(IsDiscreteValuationRing.addVal R).map_mul, ENat.toNat_add, Nat.cast_add, add_div]`. Conclude with `fun h => ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)`. Conclude with `fun h => hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)`.
-/
private theorem nval_mul_eq_add_of_ne_zero (l : ℕ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    nval R l (a * b) = nval R l a + nval R l b := by
  simp only [nval]
  rw [(IsDiscreteValuationRing.addVal R).map_mul, ENat.toNat_add, Nat.cast_add, add_div]
  · exact fun h => ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  · exact fun h => hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)

/- English proof (translation)
Establish `key : vK R l x = nval R l (IsLocalization.surj (nonZeroDivisors R) x).choose.1 - nval R l ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R)` using `rfl`. Establish `hspec` using `(IsLocalization.surj (nonZeroDivisors R) x).choose_spec`. Rewrite using `[key]`. Generalize the expression as in `(IsLocalization.surj (nonZeroDivisors R) x).choose = q at hspec ⊢`. Break down `q with ⟨c, d, hd⟩` into its components or cases.

Simplify using `only at hspec ⊢`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hinjK` using `IsFractionRing.injective R (FractionRing R)`. Establish `hb' : algebraMap R (FractionRing R) b ≠ 0` using `fun h0 => hb (hinjK (by rw [h0, map_zero]))`. Establish `hd' : algebraMap R (FractionRing R) d ≠ 0` using `fun h0 => hd0 (hinjK (by rw [h0, map_zero]))`.

Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[map_zero]`. Conclude with `mul_ne_zero hx hb' h`. Establish `hc : c ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hspec` using `[map_zero]`. Conclude with `mul_ne_zero hx hd' hspec`. Establish `hcross : a * d = c * b`. Apply `hinjK` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, ← h, ← hspec]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `nval_mul_eq_add_of_ne_zero (R := R) l ha hd0`. Establish `e2` using `nval_mul_eq_add_of_ne_zero (R := R) l hc hb`. Rewrite `e1` using `[hcross]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vK_eq_of_frac (l : ℕ) {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) :
    vK R l x = nval R l a - nval R l b := by
  have key : vK R l x = nval R l (IsLocalization.surj (nonZeroDivisors R) x).choose.1 -
      nval R l ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R) := rfl
  have hspec := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  rw [key]
  generalize (IsLocalization.surj (nonZeroDivisors R) x).choose = q at hspec ⊢
  rcases q with ⟨c, d, hd⟩
  dsimp only at hspec ⊢
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hinjK := IsFractionRing.injective R (FractionRing R)
  have hb' : algebraMap R (FractionRing R) b ≠ 0 := fun h0 => hb (hinjK (by rw [h0, map_zero]))
  have hd' : algebraMap R (FractionRing R) d ≠ 0 := fun h0 => hd0 (hinjK (by rw [h0, map_zero]))
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact mul_ne_zero hx hb' h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hspec
    exact mul_ne_zero hx hd' hspec
  have hcross : a * d = c * b := by
    apply hinjK
    rw [map_mul, map_mul, ← h, ← hspec]
    ring
  have e1 := nval_mul_eq_add_of_ne_zero (R := R) l ha hd0
  have e2 := nval_mul_eq_add_of_ne_zero (R := R) l hc hb
  rw [hcross] at e1
  linarith

abbrev fracMap (hinj : Function.Injective (algebraMap R R')) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (j := algebraMap R R') hinj

/- English proof (translation)
Establish `key : vK R l x = nval R l (IsLocalization.surj (nonZeroDivisors R) x).choose.1 - nval R l ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R)` using `rfl`. Establish `hspec` using `(IsLocalization.surj (nonZeroDivisors R) x).choose_spec`. Rewrite using `[key]`. Generalize the expression as in `(IsLocalization.surj (nonZeroDivisors R) x).choose = q at hspec ⊢`. Break down `q with ⟨c, d, hd⟩` into its components or cases.

Simplify using `only at hspec ⊢`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hfx : fracMap hinj x ≠ 0` using `fun h0 => hx ((fracMap hinj).injective (by rw [h0, map_zero]))`. Establish `hd' : algebraMap R R' d ≠ 0` using `fun h0 => hd0 (hinj (by rw [h0, map_zero]))`. Establish `hcomm : ∀ r : R, fracMap hinj (algebraMap R (FractionRing R) r) = algebraMap R' (FractionRing R') (algebraMap R R' r)` using `fun r => IsLocalization.map_eq _ _`.

Establish `hmap : fracMap hinj x * algebraMap R' (FractionRing R') (algebraMap R R' d) = algebraMap R' (FractionRing R') (algebraMap R R' c)`. Rewrite using `[← hcomm, ← hcomm, ← map_mul, hspec]`. Rewrite using `[vK_eq_of_frac l hfx hd' hmap, nval_map hinj l c, nval_map hinj l d]`.
-/
theorem vK_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) {x : FractionRing R}
    (hx : x ≠ 0) : vK R' l (fracMap hinj x) = vK R l x := by
  have key : vK R l x = nval R l (IsLocalization.surj (nonZeroDivisors R) x).choose.1 -
      nval R l ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R) := rfl
  have hspec := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  rw [key]
  generalize (IsLocalization.surj (nonZeroDivisors R) x).choose = q at hspec ⊢
  rcases q with ⟨c, d, hd⟩
  dsimp only at hspec ⊢
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hfx : fracMap hinj x ≠ 0 := fun h0 => hx ((fracMap hinj).injective (by rw [h0, map_zero]))
  have hd' : algebraMap R R' d ≠ 0 := fun h0 => hd0 (hinj (by rw [h0, map_zero]))
  have hcomm : ∀ r : R, fracMap hinj (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (algebraMap R R' r) := fun r => IsLocalization.map_eq _ _
  have hmap : fracMap hinj x * algebraMap R' (FractionRing R') (algebraMap R R' d) =
      algebraMap R' (FractionRing R') (algebraMap R R' c) := by
    rw [← hcomm, ← hcomm, ← map_mul, hspec]
  rw [vK_eq_of_frac l hfx hd' hmap, nval_map hinj l c, nval_map hinj l d]

end Formalism.MainNotions.TwOe

end
