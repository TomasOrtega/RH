import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

/- English proof (translation)
Introduce `C _ _ N q t hI ht0 ht1 hψ m hm`. Establish `htpos : 0 < ‖t‖` using `norm_pos_iff.2 ht0`. Use `set L : ℝ := -Real.log ‖t‖ with hL`. Establish `hLpos : 0 < L`. Use `Real.log_neg htpos ht1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `clear_value L`. Use `choose Q hQ using hψ`. Establish `hq : ∀ χ, q χ = (Q χ : ℝ) * L`. Introduce `χ`.

Establish `h1` using `hI.ψ χ`. Rewrite `h1` using `[hQ χ]`. Establish `h2 : Real.log (‖t‖ ^ Q χ) = -q χ` using `by rw [h1, Real.log_exp]`. Rewrite `h2` using `[Real.log_zpow]`. Rewrite using `[hL]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set Bf : N.X → N.X → ℤ := fun x y => Q (x + y) - Q x - Q y with hBf`. Establish `hB : ∀ x y, (Bf x y : ℝ) = QuadraticMap.polar q x y / L`. Introduce `x y`. Rewrite using `[eq_div_iff hLpos.ne']`.

Simplify using `only [hBf, QuadraticMap.polar, hq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `inj : ∀ a b : ℤ, (a : ℝ) = b → a = b` using `fun a b h => Int.cast_inj.1 h`. Set `Bm : LinearMap.BilinForm ℤ N.X` to `LinearMap.mk₂ ℤ Bf (fun x x' y => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_left, add_div])) (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_left, zsmul_eq_mul, mul_div_assoc])) (fun x y y' => inj _ _ (by rw [Int.cas …`.

Establish `hBm : ∀ x y, Bm x y = Bf x y` using `fun x y => rfl`. Establish `hdiag : ∀ x, Bf x x = 2 * Q x`. Introduce `x`. Apply `inj` to reduce the goal to its premises. Rewrite using `[hB, QuadraticMap.polar_self, hq, nsmul_eq_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Establish `hsymm : ∀ x y, Bf x y = Bf y x`. Introduce `x y`.

Simplify using `only [hBf, add_comm x y]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : ∀ y, y ≠ 0 → 0 < q y`. Introduce `y hy`. Assume the negation of the conclusion as `hn`.

Use `push_neg at hn`. Establish `hfin : {α | ¬ (0 < q α)}.Finite` using `Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop 0))`. Establish `hinf : (Set.range fun c : ℤ => c • y).Infinite` using `Set.infinite_range_of_injective (smul_left_injective ℤ hy)`. Use `hinf (hfin.subset ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`.

Simplify using `only [Set.mem_setOf_eq, not_lt]`. Rewrite using `[QuadraticMap.map_smul, zsmul_eq_mul]`. Use `push_cast`. Use polynomial arithmetic with `[mul_self_nonneg (c : ℝ)]`. Establish `hQnn : ∀ y, 0 ≤ Q y`.

Introduce `y`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Establish `: (Q 0 : ℝ) * L = 0` using `by rw [← hq, QuadraticMap.map_zero]`. Establish `: (Q 0 : ℝ) = 0`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hLpos.ne'`. Conclude with `this.ge` after adjusting the coercions. Use `hpos y hy` as an intermediate fact.

Rewrite `this` using `[hq]`. Establish `: (0 : ℝ) < Q y` using `pos_of_mul_pos_left this hLpos.le`. Conclude with `this.le` after adjusting the coercions. Establish `hQpos : ∀ y, y ≠ 0 → 0 < Q y`. Introduce `y hy`.

Use `hpos y hy` as an intermediate fact. Rewrite `this` using `[hq]`. Establish `: (0 : ℝ) < Q y` using `pos_of_mul_pos_left this hLpos.le`. Conclude with `this` after adjusting the coercions. Establish `hm0 : (2 * (m : ℤ) ^ 2) ≠ 0` using `by positivity`.

Set `β : N.Form (m ^ 2)` to `{ be := (2 * (m : ℤ) ^ 2) • Bm`. Use symmetry as in `:= fun y z => by`. Simplify using `only [LinearMap.smul_apply, hBm, hsymm y z]`. Use `pos := fun y hy => by`. Simplify using `only [LinearMap.smul_apply, hBm, hdiag, smul_eq_mul]`.

Use `hQpos y hy` as an intermediate fact. Check the signs of the components of the expression. Use `dvd := fun y z => ⟨Bf y z, by simp [LinearMap.smul_apply, hBm, smul_eq_mul]⟩ }`. Establish `hβ : ∀ α, β.be α α / (2 * m ^ 2) = 2 * Q α`. Introduce `α`.

Use `show ((2 * (m : ℤ) ^ 2) • Bm) α α / (2 * m ^ 2) = 2 * Q α`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hBm, hdiag, Int.mul_ediv_cancel_left _ hm0]`. Establish `hn : 0 < 2 * m ^ 2` using `by positivity`. Take `⟨π, hπ⟩` from `IsAlgClosed.exists_pow_nat_eq t hn`. Establish `hπ0 : π ≠ 0` using `by rintro rfl; exact ht0 (by rw [← hπ, zero_pow hn.ne'])`.

Establish `hπn : ‖π‖ ^ (2 * m ^ 2) = ‖t‖` using `by rw [← norm_pow, hπ]`. Establish `hπpos : 0 < ‖π‖` using `norm_pos_iff.2 hπ0`. Establish `hπ1 : ‖π‖ < 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `one_le_pow₀ (n := 2 * m ^ 2) h` as an intermediate fact. Rewrite `this` using `[hπn]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlp : Real.log ‖π‖ * (2 * (m : ℝ) ^ 2) = -L`. Rewrite using `[hL, ← hπn, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨β, π, hπ0, hπ1, fun n => ?_, fun α => ?_⟩` and prove the remaining obligations. Establish `hfin : {α | ¬ ((n : ℝ) * L < q α)}.Finite` using `Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop _))`. Use `hfin.subset fun α hα => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, hβ] at hα ⊢`. Rewrite using `[not_lt, hq]`. Establish `h1 : (2 * Q α) = (n : ℤ)`. Rewrite using `[← hα, Int.toNat_of_nonneg (by linarith [hQnn α])]`. Establish `h2 : (Q α : ℝ) ≤ n`.

Establish `: Q α ≤ (n : ℤ)` using `by linarith [hQnn α]`. Conclude with `this` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities. Establish `hc : ((2 * Q α).toNat : ℝ) = 2 * (Q α : ℝ)`. Use `Int.toNat_of_nonneg (show 0 ≤ 2 * Q α by linarith [hQnn α])` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Rewrite using `[hβ, ← Real.exp_log hπpos, ← Real.exp_nat_mul, hc, hq]`. Use `congr 1`. Establish `hm2 : (0 : ℝ) < (m : ℝ) ^ 2`. Establish `: (0 : ℝ) < m` using `by exact_mod_cast hm`.

Check the signs of the components of the expression. Establish `e : Real.log ‖π‖ = -L / (2 * (m : ℝ) ^ 2)`. Rewrite using `[eq_div_iff (by positivity)]; exact hlp`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_form_of_discrete_norms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  intro C _ _ N q t hI ht0 ht1 hψ m hm
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set L : ℝ := -Real.log ‖t‖ with hL
  have hLpos : 0 < L := by
    have := Real.log_neg htpos ht1
    linarith
  clear_value L
  choose Q hQ using hψ
  have hq : ∀ χ, q χ = (Q χ : ℝ) * L := by
    intro χ
    have h1 := hI.ψ χ
    rw [hQ χ] at h1
    have h2 : Real.log (‖t‖ ^ Q χ) = -q χ := by rw [h1, Real.log_exp]
    rw [Real.log_zpow] at h2
    rw [hL]; linarith
  set Bf : N.X → N.X → ℤ := fun x y => Q (x + y) - Q x - Q y with hBf
  have hB : ∀ x y, (Bf x y : ℝ) = QuadraticMap.polar q x y / L := by
    intro x y
    rw [eq_div_iff hLpos.ne']
    simp only [hBf, QuadraticMap.polar, hq]
    push_cast; ring
  have inj : ∀ a b : ℤ, (a : ℝ) = b → a = b := fun a b h => Int.cast_inj.1 h
  let Bm : LinearMap.BilinForm ℤ N.X := LinearMap.mk₂ ℤ Bf
    (fun x x' y => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_left, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_left, zsmul_eq_mul, mul_div_assoc]))
    (fun x y y' => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_right, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_right, zsmul_eq_mul, mul_div_assoc]))
  have hBm : ∀ x y, Bm x y = Bf x y := fun x y => rfl
  have hdiag : ∀ x, Bf x x = 2 * Q x := by
    intro x
    apply inj
    rw [hB, QuadraticMap.polar_self, hq, nsmul_eq_mul]
    push_cast
    field_simp
    try ring
  have hsymm : ∀ x y, Bf x y = Bf y x := by
    intro x y; simp only [hBf, add_comm x y]; ring
  have hpos : ∀ y, y ≠ 0 → 0 < q y := by
    intro y hy
    by_contra hn
    push_neg at hn
    have hfin : {α | ¬ (0 < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop 0))
    have hinf : (Set.range fun c : ℤ => c • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℤ hy)
    refine hinf (hfin.subset ?_)
    rintro _ ⟨c, rfl⟩
    simp only [Set.mem_setOf_eq, not_lt]
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    nlinarith [mul_self_nonneg (c : ℝ)]
  have hQnn : ∀ y, 0 ≤ Q y := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : (Q 0 : ℝ) * L = 0 := by rw [← hq, QuadraticMap.map_zero]
      have : (Q 0 : ℝ) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hLpos.ne'
      exact_mod_cast this.ge
    · have := hpos y hy
      rw [hq] at this
      have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
      exact_mod_cast this.le
  have hQpos : ∀ y, y ≠ 0 → 0 < Q y := by
    intro y hy
    have := hpos y hy
    rw [hq] at this
    have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
    exact_mod_cast this
  have hm0 : (2 * (m : ℤ) ^ 2) ≠ 0 := by positivity
  let β : N.Form (m ^ 2) :=
    { be := (2 * (m : ℤ) ^ 2) • Bm
      symm := fun y z => by
        simp only [LinearMap.smul_apply, hBm, hsymm y z]
      pos := fun y hy => by
        simp only [LinearMap.smul_apply, hBm, hdiag, smul_eq_mul]
        have := hQpos y hy
        positivity
      dvd := fun y z => ⟨Bf y z, by simp [LinearMap.smul_apply, hBm, smul_eq_mul]⟩ }
  have hβ : ∀ α, β.be α α / (2 * m ^ 2) = 2 * Q α := by
    intro α
    show ((2 * (m : ℤ) ^ 2) • Bm) α α / (2 * m ^ 2) = 2 * Q α
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hBm, hdiag, Int.mul_ediv_cancel_left _ hm0]
  have hn : 0 < 2 * m ^ 2 := by positivity
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq t hn
  have hπ0 : π ≠ 0 := by rintro rfl; exact ht0 (by rw [← hπ, zero_pow hn.ne'])
  have hπn : ‖π‖ ^ (2 * m ^ 2) = ‖t‖ := by rw [← norm_pow, hπ]
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hπ1 : ‖π‖ < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := 2 * m ^ 2) h
    rw [hπn] at this
    linarith
  have hlp : Real.log ‖π‖ * (2 * (m : ℝ) ^ 2) = -L := by
    rw [hL, ← hπn, Real.log_pow]; push_cast; ring
  refine ⟨β, π, hπ0, hπ1, fun n => ?_, fun α => ?_⟩
  · have hfin : {α | ¬ ((n : ℝ) * L < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop _))
    refine hfin.subset fun α hα => ?_
    simp only [Set.mem_setOf_eq, hβ] at hα ⊢
    rw [not_lt, hq]
    have h1 : (2 * Q α) = (n : ℤ) := by
      rw [← hα, Int.toNat_of_nonneg (by linarith [hQnn α])]
    have h2 : (Q α : ℝ) ≤ n := by
      have : Q α ≤ (n : ℤ) := by linarith [hQnn α]
      exact_mod_cast this
    nlinarith
  · have hc : ((2 * Q α).toNat : ℝ) = 2 * (Q α : ℝ) := by
      have := Int.toNat_of_nonneg (show 0 ≤ 2 * Q α by linarith [hQnn α])
      exact_mod_cast this
    rw [hβ, ← Real.exp_log hπpos, ← Real.exp_nat_mul, hc, hq]
    congr 1
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    have e : Real.log ‖π‖ = -L / (2 * (m : ℝ) ^ 2) := by
      rw [eq_div_iff (by positivity)]; exact hlp
    rw [e]
    field_simp

end GlobalTheory.MBLow
