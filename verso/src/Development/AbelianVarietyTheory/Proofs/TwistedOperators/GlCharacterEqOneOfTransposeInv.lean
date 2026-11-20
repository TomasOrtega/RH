import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory

/- English proof (translation)
Establish `hne : ∀ g : GL n k, χ g ≠ 0`. Introduce `g h0`. Establish `: χ (g * g⁻¹) = 1` using `by simp`. Rewrite `this` using `[map_mul, h0, zero_mul]`. Conclude with `zero_ne_one this`.

Establish `hdiag : ∀ (D : n → k) (g : GL n k), g.val = diagonal D → χ g = 1`. Introduce `D g hg`. Establish `h1 : χ g⁻¹ = χ g`. Apply `h` to reduce the goal to its premises. Rewrite using `[Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hg, diagonal_transpose]`.

Establish `h2 : χ g * χ g = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : χ g ^ 2 = 1` using `by rw [sq, h2]`. Conclude with `(pow_eq_one_iff_of_nonneg (zero_le) two_ne_zero).1 h3`. Take `⟨a, ha⟩` from `Infinite.exists_notMem_finset ({0, 1} : Finset k)`.

Establish `ha0 : a ≠ 0` using `by intro h0; apply ha; simp [h0]`. Establish `ha1 : 1 - a ≠ 0`. Introduce `h0; apply ha; have : a = 1 := by linear_combination -h0`. Simplify using `[this]`. Establish `htr : ∀ (t : TransvectionStruct n k) (g : GL n k), g.val = t.toMatrix → χ g = 1`.

Introduce and unpack `⟨i, j, hij, x⟩ g hg`. Set `T : k → GL n k` to `fun y => GeneralLinearGroup.mkOfDetNeZero (transvection i j y) (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)`. Establish `hT : ∀ y, (T y).val = transvection i j y` using `fun y => rfl`. Establish `hgT : g = T x` using `Units.ext (by rw [hg, hT]; rfl)`. Establish `hconj : ∀ b : k, b ≠ 0 → χ (T (b * x)) = χ (T x)`.

Introduce `b hb`. Set `D : GL n k` to `GeneralLinearGroup.mkOfDetNeZero (diagonal (Function.update 1 i b)) (by`. Rewrite using `[det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l = i`.

Substitute `hl` using the available equality. Simplify using `using hb`. Simplify using `[Function.update_of_ne hl])`. Establish `hD : D.val = diagonal (Function.update 1 i b)` using `rfl`. Establish `e : D * T x = T (b * x) * D`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, hD, hT, hT]`. Use extensionality with `p q`. Rewrite using `[diagonal_mul, mul_diagonal]`. Simplify using `only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`.

Distinguish the cases in `hp : i = p`. Substitute `hp` using the available equality. Distinguish the cases in `hq : j = q`. Substitute `hq` using the available equality. Simplify using `[hij, Function.update_of_ne hij.symm]`.

Distinguish the cases in `hpq : i = q`. Substitute `hpq` using the available equality. Simplify using `[hq]`. Simplify using `[hq, hpq]`. Distinguish the cases in `hpq : p = q`.

Substitute `hpq` using the available equality. Simplify using `[hp]`. Simplify using `[hp, hpq]`. Use `congrArg χ e` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, hdiag _ D hD, one_mul, mul_one]`.

Conclude with `this.symm`. Establish `e : T x = T (a * x) * T ((1 - a) * x)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, hT, hT, hT, transvection_mul_transvection_same i j hij]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `congrArg χ e`. Rewrite `e2` using `[map_mul, hconj a ha0, hconj _ ha1]`. Rewrite using `[hgT]`. Conclude with `(mul_eq_left₀ (hne _)).1 e2.symm`.

Use `Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => ∀ g : GL n k, g.val = M → χ g = 1) g.val g.det_ne_zero (fun D _ => hdiag D) htr ?_ g rfl` and prove the remaining obligations. Introduce `A B hA hB pA pB u hu`. Establish `: u = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB` using `Units.ext hu`. Rewrite using `[this, map_mul, pA _ rfl, pB _ rfl, one_mul]`.
-/
theorem gl_character_eq_one_of_transpose_inv (k : Type) [Field k] [Infinite k] (n : Type)
    [Fintype n] [DecidableEq n] (χ : GL n k →* NNReal)
    (h : ∀ g g' : GL n k, g'.val = (g⁻¹ : GL n k).valᵀ → χ g' = χ g) (g : GL n k) :
    χ g = 1 := by
  classical
  have hne : ∀ g : GL n k, χ g ≠ 0 := by
    intro g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  have hdiag : ∀ (D : n → k) (g : GL n k), g.val = diagonal D → χ g = 1 := by
    intro D g hg
    have h1 : χ g⁻¹ = χ g := by
      apply h
      rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hg, diagonal_transpose]
    have h2 : χ g * χ g = 1 := by
      calc χ g * χ g = χ g * χ g⁻¹ := by rw [h1]
        _ = 1 := by rw [← map_mul]; simp
    have h3 : χ g ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg (zero_le) two_ne_zero).1 h3
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := by intro h0; apply ha; simp [h0]
  have ha1 : 1 - a ≠ 0 := by
    intro h0; apply ha; have : a = 1 := by linear_combination -h0
    simp [this]
  have htr : ∀ (t : TransvectionStruct n k) (g : GL n k), g.val = t.toMatrix → χ g = 1 := by
    rintro ⟨i, j, hij, x⟩ g hg
    let T : k → GL n k := fun y => GeneralLinearGroup.mkOfDetNeZero (transvection i j y)
      (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)
    have hT : ∀ y, (T y).val = transvection i j y := fun y => rfl
    have hgT : g = T x := Units.ext (by rw [hg, hT]; rfl)
    have hconj : ∀ b : k, b ≠ 0 → χ (T (b * x)) = χ (T x) := by
      intro b hb
      let D : GL n k := GeneralLinearGroup.mkOfDetNeZero (diagonal (Function.update 1 i b))
        (by
          rw [det_diagonal]
          refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
          by_cases hl : l = i
          · subst hl; simpa using hb
          · simp [Function.update_of_ne hl])
      have hD : D.val = diagonal (Function.update 1 i b) := rfl
      have e : D * T x = T (b * x) * D := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hD, hT, hT]
        ext p q
        rw [diagonal_mul, mul_diagonal]
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        by_cases hp : i = p
        · subst hp
          by_cases hq : j = q
          · subst hq
            simp [hij, Function.update_of_ne hij.symm]
          · by_cases hpq : i = q
            · subst hpq; simp [hq]
            · simp [hq, hpq]
        · by_cases hpq : p = q
          · subst hpq; simp [hp]
          · simp [hp, hpq]
      have := congrArg χ e
      rw [map_mul, map_mul, hdiag _ D hD, one_mul, mul_one] at this
      exact this.symm
    have e : T x = T (a * x) * T ((1 - a) * x) := by
      apply Units.ext
      rw [Units.val_mul, hT, hT, hT, transvection_mul_transvection_same i j hij]
      congr 1
      ring
    have e2 := congrArg χ e
    rw [map_mul, hconj a ha0, hconj _ ha1] at e2
    rw [hgT]
    exact (mul_eq_left₀ (hne _)).1 e2.symm
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → χ g = 1) g.val g.det_ne_zero
    (fun D _ => hdiag D) htr ?_ g rfl
  intro A B hA hB pA pB u hu
  have : u = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB :=
    Units.ext hu
  rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]

end GlobalTheory
