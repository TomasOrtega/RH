import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NormValuation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
/- English proof (translation)
Establish `hint : IsIntegral ℚ_[p] x` using `Algebra.IsIntegral.isIntegral x`. Establish `hc` using `minpoly.coeff_zero_ne_zero hint hx`. Use `⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩` and prove the remaining obligations. Rewrite using `[← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_rat_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ t : ℚ, ‖x‖ = (p : ℝ) ^ (t : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `p _ V _ _ _ _ hV ϖ hϖ`. Use `set π : PadicAlgCl p := algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ`. Establish `hinjV` using `IsFractionRing.injective V (FractionRing V)`. Establish `hπne : π ≠ 0`. Rewrite using `[hπ, map_ne_zero]`.

Conclude with `fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))`. Establish `hπle : ‖π‖ ≤ 1` using `(hV _).2 ⟨ϖ, rfl⟩`. Establish `hπlt : ‖π‖ < 1`. Use `lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_` and prove the remaining obligations. Establish `hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1`.

Rewrite using `[map_inv₀, norm_inv, ← hπ, h1, inv_one]`. Take `⟨a, ha⟩` from `(hV _).1 hle`. Use `isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ha, map_one]`. Conclude with `mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))`.

Establish `hb0 : 0 < ‖π‖` using `norm_pos_iff.2 hπne`. Establish `hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s` using `fun s t => Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt`. Establish `hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t` using `fun s t h => le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)`. Take `⟨s, hs⟩` from `exists_rat_norm_eq_rpow hπne`. Establish `hs0 : (s : ℝ) ≠ 0`.

Introduce `h0`. Rewrite `hs` using `[h0, Real.rpow_zero]`. Conclude with `hπlt.ne hs`. Choose the witnesses or unpack the hypotheses as in `⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by`. Use `⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [dif_neg hx]`. Rewrite using `[hs, ← Real.rpow_mul (Nat.cast_nonneg _)]`. Use `push_cast`. Rewrite using `[mul_div_cancel₀ _ hs0]`.

Conclude with `(exists_rat_norm_eq_rpow hx).choose_spec`. Establish `hr_one : r 1 = 0`. Establish `h` using `hexp 1 one_ne_zero`. Rewrite `h` using `[norm_one, ← Real.rpow_zero ‖π‖]`. Conclude with `(hinj _ _ h).symm` after adjusting the coercions.

Establish `hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y`. Introduce `x y hx hy`. Establish `h` using `hexp (x * y) (mul_ne_zero hx hy)`. Rewrite `h` using `[norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0]`. Conclude with `(hinj _ _ h).symm` after adjusting the coercions.

Establish `hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (r x) (r y) ≤ r (x + y)`. Introduce `x y hx hy hxy`. Establish `h` using `(PadicAlgCl.isNonarchimedean p) x y`. Rewrite `h` using `[hexp x hx, hexp y hy, hexp _ hxy]`. Break down `le_total (r x) (r y) with hxy' | hxy'` into its components or cases.

Rewrite using `[min_eq_left hxy']`. Establish `hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ)` using `max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))`. Rewrite `h` using `[hm, hle]`. Conclude with `h` after adjusting the coercions. Rewrite using `[min_eq_right hxy']`.

Establish `hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ)` using `max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))`. Rewrite `h` using `[hm, hle]`. Conclude with `h` after adjusting the coercions. Use `set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw`. Establish `hw0 : w 0 = ⊤` using `by simp [hw]`.

Establish `hw1 : w 1 = 0` using `by simp [hw, hr_one]`. Establish `hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y)`. Introduce `x y`. Distinguish the cases in `hx : x = 0`. Simplify using `[hw, hx]`.

Distinguish the cases in `hy : y = 0`. Simplify using `[hw, hy]`. Distinguish the cases in `hxy : x + y = 0`. Simplify using `[hw, hxy]`. Simplify using `only [hw, if_neg hx, if_neg hy, if_neg hxy]`.

Rewrite using `[← WithTop.coe_min, WithTop.coe_le_coe]`. Conclude with `hr_add x y hx hy hxy`. Establish `hwmul : ∀ x y, w (x * y) = w x + w y`. Introduce `x y`. Distinguish the cases in `hx : x = 0`.

Simplify using `[hw, hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hw, hy]`. Simplify using `only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]`. Rewrite using `[hr_mul x y hx hy, WithTop.coe_add]`.

Set `v : AddValuation (PadicAlgCl p) (WithTop ℚ)` to `AddValuation.of w hw0 hw1 hwadd hwmul`. Establish `hv : ∀ x, v x = w x` using `fun x => rfl`. Establish `hunit : ∀ u : Vˣ, ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1`. Introduce `u`. Establish `h1` using `(hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩`.

Establish `h2` using `(hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩`. Establish `h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ * ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]`. Use `⟨v, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver`. Introduce `c n hc`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc`. Take `⟨u, rfl⟩` from `hc`. Establish `hne : algebraMap (FractionRing V) (PadicAlgCl p) ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0`.

Rewrite using `[map_mul, map_zpow₀]`. Use `mul_ne_zero (zpow_ne_zero _ hπne) ?_` and prove the remaining obligations. Introduce `h`. Use `hunit u` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `zero_ne_one this`. Rewrite using `[hv]`. Simplify using `only [hw, if_neg hne]`. Establish `h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p) ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ = ‖π‖ ^ (n : ℝ)`. Rewrite using `[map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ, Real.rpow_intCast]`.

Use `hinj _ _ ((hexp _ hne).symm.trans h2)` as an intermediate fact. Rewrite using `[WithTop.coe_eq_coe]`. Conclude with `this` after adjusting the coercions. Unfold `_root_.GlobalTheory.ZH.NormVal`. Use `⟨hb0, hπlt, fun x q => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[hv, hw0, norm_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `absurd h WithTop.top_ne_coe`. Introduce `h`. Conclude with `absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'`. Rewrite using `[hv]`. Simplify using `only [hw, if_neg hx, WithTop.coe_eq_coe]`.

Rewrite using `[hexp x hx]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `hinj _ _ h` after adjusting the coercions. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[hv, hw0]`.

Rewrite using `[hv]`. Simplify using `only [hw, if_neg hx]`. Rewrite using `[hexp x hx]`. Establish `h1` using `hle (r x : ℝ) 0`. Rewrite `h1` using `[Real.rpow_zero]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, WithTop.coe_nonneg]`. Conclude with `Iff.rfl` after adjusting the coercions. Rewrite using `[WithTop.coe_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `h`. Use `hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)` as an intermediate fact.

Conclude with `this` after adjusting the coercions.
-/
theorem _root_.GlobalTheory.NormValuation.main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ ϖ : V, Irreducible ϖ → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (PadicAlgCl p) v ∧ _root_.GlobalTheory.ZH.NormVal (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)) v ∧ ∀ x : PadicAlgCl p, (0 ≤ v x ↔ ‖x‖ ≤ 1) ∧ (v x = 0 ↔ ‖x‖ = 1) := by
  intro p _ V _ _ _ _ hV ϖ hϖ
  set π : PadicAlgCl p :=
    algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ
  have hinjV := IsFractionRing.injective V (FractionRing V)
  have hπne : π ≠ 0 := by
    rw [hπ, map_ne_zero]
    exact fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hπle : ‖π‖ ≤ 1 := (hV _).2 ⟨ϖ, rfl⟩
  have hπlt : ‖π‖ < 1 := by
    refine lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_
    have hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, ← hπ, h1, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hle
    refine isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩
    rw [map_mul, ha, map_one]
    exact mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hb0 : 0 < ‖π‖ := norm_pos_iff.2 hπne
  have hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s := fun s t =>
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt
  have hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t := fun s t h =>
    le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)
  obtain ⟨s, hs⟩ := exists_rat_norm_eq_rpow hπne
  have hs0 : (s : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hs
    exact hπlt.ne hs
  obtain ⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by
    refine ⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩
    intro x hx
    simp only [dif_neg hx]
    rw [hs, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [mul_div_cancel₀ _ hs0]
    exact (exists_rat_norm_eq_rpow hx).choose_spec
  have hr_one : r 1 = 0 := by
    have h := hexp 1 one_ne_zero
    rw [norm_one, ← Real.rpow_zero ‖π‖] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y := by
    intro x y hx hy
    have h := hexp (x * y) (mul_ne_zero hx hy)
    rw [norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (r x) (r y) ≤ r (x + y) := by
    intro x y hx hy hxy
    have h := (PadicAlgCl.isNonarchimedean p) x y
    rw [hexp x hx, hexp y hy, hexp _ hxy] at h
    rcases le_total (r x) (r y) with hxy' | hxy'
    · rw [min_eq_left hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ) :=
        max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
    · rw [min_eq_right hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ) :=
        max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
  set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw
  have hw0 : w 0 = ⊤ := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hr_one]
  have hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    by_cases hxy : x + y = 0
    · simp [hw, hxy]
    simp only [hw, if_neg hx, if_neg hy, if_neg hxy]
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact hr_add x y hx hy hxy
  have hwmul : ∀ x y, w (x * y) = w x + w y := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    simp only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [hr_mul x y hx hy, WithTop.coe_add]
  let v : AddValuation (PadicAlgCl p) (WithTop ℚ) := AddValuation.of w hw0 hw1 hwadd hwmul
  have hv : ∀ x, v x = w x := fun x => rfl
  have hunit : ∀ u : Vˣ,
      ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1 := by
    intro u
    have h1 := (hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩
    have h2 := (hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ *
        ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖
          = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]
  refine ⟨v, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver
    intro c n hc
    unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc
    obtain ⟨u, rfl⟩ := hc
    have hne : algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0 := by
      rw [map_mul, map_zpow₀]
      refine mul_ne_zero (zpow_ne_zero _ hπne) ?_
      intro h
      have := hunit u
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [hv]
    simp only [hw, if_neg hne]
    have h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ =
          ‖π‖ ^ (n : ℝ) := by
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ,
        Real.rpow_intCast]
    have := hinj _ _ ((hexp _ hne).symm.trans h2)
    rw [WithTop.coe_eq_coe]
    exact_mod_cast this
  · unfold _root_.GlobalTheory.ZH.NormVal
    refine ⟨hb0, hπlt, fun x q => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [hv, hw0, norm_zero]
      constructor
      · intro h; exact absurd h WithTop.top_ne_coe
      · intro h; exact absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'
    rw [hv]
    simp only [hw, if_neg hx, WithTop.coe_eq_coe]
    rw [hexp x hx]
    constructor
    · rintro rfl; rfl
    · intro h; exact_mod_cast hinj _ _ h
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [hv, hw0]
    rw [hv]
    simp only [hw, if_neg hx]
    rw [hexp x hx]
    have h1 := hle (r x : ℝ) 0
    rw [Real.rpow_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [h1, WithTop.coe_nonneg]
      exact_mod_cast Iff.rfl
    · rw [WithTop.coe_eq_zero]
      constructor
      · rintro h; rw [h]; simp
      · intro h
        have := hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)
        exact_mod_cast this

end GlobalTheory.NormValuation
end
