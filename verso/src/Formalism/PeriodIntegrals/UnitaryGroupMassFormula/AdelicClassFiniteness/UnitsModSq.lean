import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar

noncomputable section

namespace PIW.AdelClassFin

open NumberField NumberField.Units

/- English proof (translation)
Set `g : torsion F × (Fin (rank F) → Fin 2) → F` to `fun p => algebraMap (𝓞 F) F (((p.1 : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((p.2 i : ℕ) : ℤ)) : (𝓞 F)ˣ) : 𝓞 F)`. Use `⟨Set.range g, Set.finite_range g, fun c => ?_⟩` and prove the remaining obligations. Take `⟨⟨ζ, e⟩, he, -⟩` from `exist_unique_eq_mul_prod F c`. Simplify using `only at he`. Set `f : Fin (rank F) → Fin 2` to `fun i => ⟨(e i % 2).toNat, by omega⟩`.

Use `⟨g (ζ, f), Set.mem_range_self _, ∏ i, fundSystem F i ^ (e i / 2), ?_⟩` and prove the remaining obligations. Establish `key : c = ((ζ : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((f i : ℕ) : ℤ))) * (∏ i, fundSystem F i ^ (e i / 2)) ^ 2`. Rewrite using `[he, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[sq, ← zpow_add, ← zpow_add]`. Use `congr 1`. Establish `h2 : (((f i : ℕ) : ℤ)) = e i % 2` using `Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))`. Use linear arithmetic over natural numbers and integers. Rewrite using `[key, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]`.
-/
theorem units_mod_sq (F : Type) [Field F] [NumberField F] :
    ∃ U : Set F, U.Finite ∧ ∀ c : (𝓞 F)ˣ, ∃ w ∈ U, ∃ v : (𝓞 F)ˣ,
      algebraMap (𝓞 F) F (c : 𝓞 F) = w * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := by
  classical
  let g : torsion F × (Fin (rank F) → Fin 2) → F := fun p =>
    algebraMap (𝓞 F) F (((p.1 : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((p.2 i : ℕ) : ℤ)) : (𝓞 F)ˣ) : 𝓞 F)
  refine ⟨Set.range g, Set.finite_range g, fun c => ?_⟩
  obtain ⟨⟨ζ, e⟩, he, -⟩ := exist_unique_eq_mul_prod F c
  dsimp only at he
  let f : Fin (rank F) → Fin 2 := fun i => ⟨(e i % 2).toNat, by omega⟩
  refine ⟨g (ζ, f), Set.mem_range_self _, ∏ i, fundSystem F i ^ (e i / 2), ?_⟩
  have key : c = ((ζ : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((f i : ℕ) : ℤ))) *
      (∏ i, fundSystem F i ^ (e i / 2)) ^ 2 := by
    rw [he, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sq, ← zpow_add, ← zpow_add]
    congr 1
    have h2 : (((f i : ℕ) : ℤ)) = e i % 2 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    omega
  rw [key, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc C`. Take `⟨U, hUf, hU⟩` from `units_mod_sq F`. Set `S : Set (Ideal (𝓞 E))` to `{I | Ideal.absNorm I ≤ ⌊C⌋₊}`. Establish `hSf : S.Finite` using `Ideal.finite_setOfPred_absNorm_le _`. Set `P : Ideal (𝓞 E) → Prop` to `fun I => ∃ y : 𝓞 E, I = Ideal.span {y} ∧ star (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E y ∧ y ≠ 0`.

Set `rep : Ideal (𝓞 E) → E` to `fun I => if h : P I then algebraMap (𝓞 E) E h.choose else 1`. Use `⟨Set.image2 (fun w I => algebraMap F E w * rep I) U S \ {0}, (hUf.image2 _ hSf).sdiff, fun h => h.2 rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨x, rfl⟩ hstar ha hN`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) E)` using `RingOfIntegers.coe_injective`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact ha (map_zero _)`.

Establish `hxS : Ideal.span {x} ∈ S` using `by show Ideal.absNorm _ ≤ _`. Rewrite using `[Ideal.absNorm_span_singleton]`. Apply `Nat.le_floor` to reduce the goal to its premises. Establish `h1` using `Algebra.coe_norm_int x`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`.

Rewrite using `[h1]`. Conclude with `hN`. Establish `hP : P (Ideal.span {x})` using `⟨x, rfl, hstar, hx0⟩`. Take `⟨hyI, hys, hy0⟩` from `hP.choose_spec`. Establish `hrep : rep (Ideal.span {x}) = algebraMap (𝓞 E) E hP.choose` using `dif_pos hP`.

Take `⟨w, hw⟩ : Associated hP.choose x` from `Ideal.span_singleton_eq_span_singleton.mp hyI.symm`. Establish `hyE : algebraMap (𝓞 E) E hP.choose ≠ 0` using `fun h => hy0 (hinj (h.trans (map_zero _).symm))`. Establish `h1 : algebraMap (𝓞 E) E x = algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E)`. Rewrite using `[← map_mul]`. Conclude with `congrArg _ hw.symm`.

Establish `hWs : star (algebraMap (𝓞 E) E (w : 𝓞 E)) = algebraMap (𝓞 E) E (w : 𝓞 E)`. Use `mul_left_cancel₀ hyE ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hys]`. Use `_ = star (algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E)) := (star_mul' _ _).symm`.

Use `_ = _ := by rw [← h1, hstar, h1]`. Take `⟨c, hcW⟩` from `(hc.fixed _).1 hWs`. Establish `hWW' : algebraMap (𝓞 E) E (w : 𝓞 E) * algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1`. Rewrite using `[← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hWW'` using `[← hcW, map_zero, zero_mul]`. Conclude with `zero_ne_one hWW'`. Establish `hW' : algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = algebraMap F E c⁻¹`. Rewrite using `[map_inv₀, hcW]`.

Conclude with `eq_inv_of_mul_eq_one_right hWW'`. Establish `hci : IsIntegral ℤ c`. Use `(isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective).mp ?_` and prove the remaining obligations. Rewrite using `[hcW]`. Conclude with `(w : 𝓞 E).2`.

Establish `hci' : IsIntegral ℤ c⁻¹`. Use `(isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective).mp ?_` and prove the remaining obligations. Rewrite using `[← hW']`. Conclude with `((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2`. Set `cu : (𝓞 F)ˣ` to `{ val := ⟨c, hci⟩ inv := ⟨c⁻¹, hci'⟩ val_inv := RingOfIntegers.ext (show c * c⁻¹ = 1 from mul_inv_cancel₀ hc0) inv_val := RingOfIntegers.ext (show c⁻¹ * c = 1 from inv_mul_cancel₀ hc0) }`.

Take `⟨w0, hw0U, v, hv⟩` from `hU cu`. Establish `hcv : c = w0 * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2` using `hv`. Set `u : (𝓞 E)ˣ` to `Units.map (RingOfIntegers.mapRingHom (algebraMap F E)).toMonoidHom v`. Establish `hu : algebraMap (𝓞 E) E (u : 𝓞 E) = algebraMap F E (algebraMap (𝓞 F) F (v : 𝓞 F))` using `rfl`. Establish `hus : star (algebraMap (𝓞 E) E (u : 𝓞 E)) = algebraMap (𝓞 E) E (u : 𝓞 E)` using `(hc.fixed _).2 ⟨_, hu.symm⟩`.

Establish `main : algebraMap (𝓞 E) E x = star (algebraMap (𝓞 E) E (u : 𝓞 E)) * algebraMap (𝓞 E) E (u : 𝓞 E) * (algebraMap F E w0 * rep (Ideal.span {x}))`. Rewrite using `[hus, hrep, h1, ← hcW, hcv, map_mul, map_pow, hu]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨u, algebraMap F E w0 * rep (Ideal.span {x}), ⟨Set.mem_image2_of_mem hw0U hxS, fun h0 => ha ?_⟩, main⟩` and prove the remaining obligations. Rewrite using `[main]`.

Rewrite using `[Set.mem_singleton_iff.mp h0, mul_zero]`.
-/
theorem partUnits : PartUnits := by
  intro F E _ _ _ _ _ _ hc C
  classical
  obtain ⟨U, hUf, hU⟩ := units_mod_sq F
  let S : Set (Ideal (𝓞 E)) := {I | Ideal.absNorm I ≤ ⌊C⌋₊}
  have hSf : S.Finite := Ideal.finite_setOfPred_absNorm_le _
  let P : Ideal (𝓞 E) → Prop := fun I => ∃ y : 𝓞 E, I = Ideal.span {y} ∧
    star (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E y ∧ y ≠ 0
  let rep : Ideal (𝓞 E) → E := fun I => if h : P I then algebraMap (𝓞 E) E h.choose else 1
  refine ⟨Set.image2 (fun w I => algebraMap F E w * rep I) U S \ {0}, (hUf.image2 _ hSf).sdiff,
    fun h => h.2 rfl, ?_⟩
  rintro a ⟨x, rfl⟩ hstar ha hN
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  have hx0 : x ≠ 0 := by rintro rfl; exact ha (map_zero _)
  have hxS : Ideal.span {x} ∈ S := by
    show Ideal.absNorm _ ≤ _
    rw [Ideal.absNorm_span_singleton]
    apply Nat.le_floor
    have h1 := Algebra.coe_norm_int x
    rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1]
    exact hN
  have hP : P (Ideal.span {x}) := ⟨x, rfl, hstar, hx0⟩
  obtain ⟨hyI, hys, hy0⟩ := hP.choose_spec
  have hrep : rep (Ideal.span {x}) = algebraMap (𝓞 E) E hP.choose := dif_pos hP
  obtain ⟨w, hw⟩ : Associated hP.choose x := Ideal.span_singleton_eq_span_singleton.mp hyI.symm
  have hyE : algebraMap (𝓞 E) E hP.choose ≠ 0 := fun h => hy0 (hinj (h.trans (map_zero _).symm))
  have h1 : algebraMap (𝓞 E) E x =
      algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E) := by
    rw [← map_mul]
    exact congrArg _ hw.symm
  have hWs : star (algebraMap (𝓞 E) E (w : 𝓞 E)) = algebraMap (𝓞 E) E (w : 𝓞 E) := by
    refine mul_left_cancel₀ hyE ?_
    calc algebraMap (𝓞 E) E hP.choose * star (algebraMap (𝓞 E) E (w : 𝓞 E))
        = star (algebraMap (𝓞 E) E hP.choose) * star (algebraMap (𝓞 E) E (w : 𝓞 E)) := by
          rw [hys]
      _ = star (algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E)) :=
          (star_mul' _ _).symm
      _ = _ := by rw [← h1, hstar, h1]
  obtain ⟨c, hcW⟩ := (hc.fixed _).1 hWs
  have hWW' : algebraMap (𝓞 E) E (w : 𝓞 E) * algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hcW, map_zero, zero_mul] at hWW'
    exact zero_ne_one hWW'
  have hW' : algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = algebraMap F E c⁻¹ := by
    rw [map_inv₀, hcW]
    exact eq_inv_of_mul_eq_one_right hWW'
  have hci : IsIntegral ℤ c := by
    refine (isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective).mp ?_
    rw [hcW]
    exact (w : 𝓞 E).2
  have hci' : IsIntegral ℤ c⁻¹ := by
    refine (isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective).mp ?_
    rw [← hW']
    exact ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2
  let cu : (𝓞 F)ˣ :=
    { val := ⟨c, hci⟩
      inv := ⟨c⁻¹, hci'⟩
      val_inv := RingOfIntegers.ext (show c * c⁻¹ = 1 from mul_inv_cancel₀ hc0)
      inv_val := RingOfIntegers.ext (show c⁻¹ * c = 1 from inv_mul_cancel₀ hc0) }
  obtain ⟨w0, hw0U, v, hv⟩ := hU cu
  have hcv : c = w0 * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := hv
  let u : (𝓞 E)ˣ := Units.map (RingOfIntegers.mapRingHom (algebraMap F E)).toMonoidHom v
  have hu : algebraMap (𝓞 E) E (u : 𝓞 E) = algebraMap F E (algebraMap (𝓞 F) F (v : 𝓞 F)) := rfl
  have hus : star (algebraMap (𝓞 E) E (u : 𝓞 E)) = algebraMap (𝓞 E) E (u : 𝓞 E) :=
    (hc.fixed _).2 ⟨_, hu.symm⟩
  have main : algebraMap (𝓞 E) E x = star (algebraMap (𝓞 E) E (u : 𝓞 E)) *
      algebraMap (𝓞 E) E (u : 𝓞 E) * (algebraMap F E w0 * rep (Ideal.span {x})) := by
    rw [hus, hrep, h1, ← hcW, hcv, map_mul, map_pow, hu]
    ring
  refine ⟨u, algebraMap F E w0 * rep (Ideal.span {x}),
    ⟨Set.mem_image2_of_mem hw0U hxS, fun h0 => ha ?_⟩, main⟩
  rw [main]
  rw [Set.mem_singleton_iff.mp h0, mul_zero]

end PIW.AdelClassFin
