import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

namespace UpperTheory.V.Z.Sym.Glob

open Loc

section

variable {F : Type} [Field F] {Δ τ : F}

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem re_mul_star (x : Lsq F Δ) : (x * star x).re = x.re ^ 2 - Δ * x.im ^ 2 := by
  simp
  ring

/- English proof (translation)
Rewrite using `[re_mul_star]`. Simplify using `only [map_sub, map_mul, map_pow]`. Use polynomial arithmetic with `[sq_nonneg (σ x.re), sq_nonneg (σ x.im)]`.
-/
private theorem nrm_nonneg (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) : 0 ≤ σ (x * star x).re := by
  rw [re_mul_star]
  simp only [map_sub, map_mul, map_pow]
  nlinarith [sq_nonneg (σ x.re), sq_nonneg (σ x.im)]

/- English proof (translation)
Rewrite using `[re_mul_star, map_sub, map_mul, map_pow, map_pow]`. Establish `hne : x.re ≠ 0 ∨ x.im ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (QuadraticAlgebra.ext (by simp [hc.1]) (by simp [hc.2]))`.

Establish `ha` using `mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ x.im))`. Establish `hb` using `sq_nonneg (σ x.re)`. Break down `hne with h1 | h1` into its components or cases. Establish `h2 : σ x.re ≠ 0` using `(map_ne_zero σ).mpr h1`. Establish `h3 : 0 < σ x.re ^ 2` using `lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : σ x.im ≠ 0` using `(map_ne_zero σ).mpr h1`. Establish `h3 : 0 < σ x.im ^ 2` using `lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))`. Establish `h4` using `mul_pos (neg_pos.mpr h) h3`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem nrm_pos (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) (hx : x ≠ 0) : 0 < σ (x * star x).re := by
  rw [re_mul_star, map_sub, map_mul, map_pow, map_pow]
  have hne : x.re ≠ 0 ∨ x.im ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (QuadraticAlgebra.ext (by simp [hc.1]) (by simp [hc.2]))
  have ha := mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ x.im))
  have hb := sq_nonneg (σ x.re)
  rcases hne with h1 | h1
  · have h2 : σ x.re ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.re ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    nlinarith
  · have h2 : σ x.im ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    have h4 := mul_pos (neg_pos.mpr h) h3
    nlinarith

/- English proof (translation)
Simplify using `[herm]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_re (c t : F) (m : EL Δ τ) (x : Sp Δ τ) :
    (herm c (t • m) x x).re = c * (x.1 * star x.1).re + t * (herm 1 m (0, x.2) (0, x.2)).re := by
  simp [herm]
  ring

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.mp hy`. Establish `h0` using `nrm_nonneg σ h (y 0)`. Establish `h1` using `nrm_nonneg σ h (y 1)`. Establish `h2` using `nrm_nonneg σ h (y 2)`. Establish `hp` using `nrm_pos σ h (y i) hi`.

Rewrite using `[Fin.sum_univ_three, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add, map_add, map_add]`. Use `fin_cases i`. Conclude with `add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hp h1) h2`. Conclude with `add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h0 hp) h2`. Conclude with `add_pos_of_nonneg_of_pos (add_nonneg h0 h1) hp`.
-/
private theorem sum_pos (σ : F →+* ℝ) (h : σ Δ < 0) (y : Fin 3 → Lsq F Δ) (hy : y ≠ 0) :
    0 < σ (∑ i, y i * star (y i)).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have h0 := nrm_nonneg σ h (y 0)
  have h1 := nrm_nonneg σ h (y 1)
  have h2 := nrm_nonneg σ h (y 2)
  have hp := nrm_pos σ h (y i) hi
  rw [Fin.sum_univ_three, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add, map_add, map_add]
  fin_cases i
  · exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hp h1) h2
  · exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h0 hp) h2
  · exact add_pos_of_nonneg_of_pos (add_nonneg h0 h1) hp

end

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob in
/- English proof (translation)
Introduce `F _ _ Δ D hD τ d m hm c t`. Establish `hneg` using `hD.neg`. Use `⟨fun hc ht x hx σ => ?_, fun δ ι P hM => ?_⟩` and prove the remaining obligations. Rewrite using `[herm_re, map_add, map_mul, map_mul]`. Establish `h1` using `nrm_nonneg σ (hneg σ) x.1`.

Distinguish the cases in `h2 : x.2 = 0`. Establish `hx1 : x.1 ≠ 0`. Introduce `h1'`. Conclude with `hx (Prod.ext h1' h2)`. Establish `h4` using `nrm_pos σ (hneg σ) x.1 hx1`.

Establish `h3 : (herm 1 m (0, x.2) (0, x.2)).re = 0`. Rewrite using `[h2]`. Simplify using `[herm]`. Rewrite using `[h3, map_zero, mul_zero, add_zero]`. Conclude with `mul_pos (hc σ) h4`.

Establish `hx2 : ((0 : Lsq F Δ), x.2) ≠ 0`. Introduce `h'`. Conclude with `h2 (congrArg Prod.snd h')`. Establish `h4` using `hm _ hx2 σ`. Use polynomial arithmetic with `[hc σ, ht σ, mul_nonneg (hc σ).le h1, mul_pos (ht σ) h4]`.

Establish `key : ∀ x : Sp Δ τ, x ≠ 0 → TPos (herm c (t • m) x x).re`. Introduce `x hx σ`. Rewrite using `[hM.form x x]`. Apply `sum_pos σ (hneg σ)` to reduce the goal to its premises. Introduce `h0`.

Conclude with `hx (P.injective (h0.trans (map_zero P).symm))`. Use `⟨fun σ => ?_, fun σ => ?_⟩` and prove the remaining obligations. Establish `h1` using `key ((1 : Lsq F Δ), 0) (by simp) σ`. Simplify `h1` using `[herm]`. Establish `hx : ((0 : Lsq F Δ), (1 : EL Δ τ)) ≠ 0` using `by simp`.

Establish `h1` using `key _ hx σ`. Establish `h2 : 0 < σ (herm 1 m (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2) (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2)).re` using `hm _ hx σ`. Establish `hz : ((0 : Lsq F Δ) * star (0 : Lsq F Δ)).re = 0` using `by simp`. Rewrite `h1` using `[herm_re, map_add, map_mul, map_mul]`. Simplify using `only [hz, map_zero, mul_zero, zero_add] at h1`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.Z.Sym.Glob.posLaw :
    UpperTheory.V.Z.Sym.Glob.PosLaw := by
  intro F _ _ Δ D hD τ d m hm c t
  have hneg := hD.neg
  refine ⟨fun hc ht x hx σ => ?_, fun δ ι P hM => ?_⟩
  · rw [herm_re, map_add, map_mul, map_mul]
    have h1 := nrm_nonneg σ (hneg σ) x.1
    by_cases h2 : x.2 = 0
    · have hx1 : x.1 ≠ 0 := by
        intro h1'
        exact hx (Prod.ext h1' h2)
      have h4 := nrm_pos σ (hneg σ) x.1 hx1
      have h3 : (herm 1 m (0, x.2) (0, x.2)).re = 0 := by
        rw [h2]
        simp [herm]
      rw [h3, map_zero, mul_zero, add_zero]
      exact mul_pos (hc σ) h4
    · have hx2 : ((0 : Lsq F Δ), x.2) ≠ 0 := by
        intro h'
        exact h2 (congrArg Prod.snd h')
      have h4 := hm _ hx2 σ
      nlinarith [hc σ, ht σ, mul_nonneg (hc σ).le h1, mul_pos (ht σ) h4]
  · have key : ∀ x : Sp Δ τ, x ≠ 0 → TPos (herm c (t • m) x x).re := by
      intro x hx σ
      rw [hM.form x x]
      apply sum_pos σ (hneg σ)
      intro h0
      exact hx (P.injective (h0.trans (map_zero P).symm))
    refine ⟨fun σ => ?_, fun σ => ?_⟩
    · have h1 := key ((1 : Lsq F Δ), 0) (by simp) σ
      simpa [herm] using h1
    · have hx : ((0 : Lsq F Δ), (1 : EL Δ τ)) ≠ 0 := by simp
      have h1 := key _ hx σ
      have h2 : 0 < σ (herm 1 m (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2) (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2)).re := hm _ hx σ
      have hz : ((0 : Lsq F Δ) * star (0 : Lsq F Δ)).re = 0 := by simp
      rw [herm_re, map_add, map_mul, map_mul] at h1
      simp only [hz, map_zero, mul_zero, zero_add] at h1
      nlinarith
