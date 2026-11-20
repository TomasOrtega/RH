import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.ExGLand
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.ExGModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

open NumberField Matrix QuadraticAlgebra

namespace UpperTheory.V.Z.Sym.Glob

open Loc

section Gram

variable {K : Type} [Field K] {Δ τ : K}

/- English proof (translation)
Apply the tactic sequence `ext <;> simp`.
-/
private theorem st_alg' (c : K) : star (algebraMap K (Lsq K Δ) c) = algebraMap K _ c := by
  ext <;> simp

/- English proof (translation)
Simplify using `only [QuadraticAlgebra.trace, LinearMap.coe_mk, AddHom.coe_mk, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tr_form (m x y : EL Δ τ) :
    QuadraticAlgebra.trace (m * x * star (sigL y)) =
      (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) * x.re * star y.re +
      (algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im) * x.re * star y.im +
      (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) * x.im * star y.re +
      (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) * x.im * star y.im := by
  simp only [QuadraticAlgebra.trace, LinearMap.coe_mk, AddHom.coe_mk, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]
  ring

/- English proof (translation)
Establish `h1` using `congrArg QuadraticAlgebra.re h`. Establish `h2` using `congrArg QuadraticAlgebra.im h`. Simplify using `only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL] at h1 h2`. Use `⟨by linear_combination -h2, by linear_combination h1 + algebraMap K (Lsq K Δ) τ * h2⟩` and prove the remaining obligations.
-/
private theorem star_parts {m : EL Δ τ} (h : star (sigL m) = m) :
    star m.im = -m.im ∧ star m.re = m.re + algebraMap K (Lsq K Δ) τ * m.im := by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL] at h1 h2
  refine ⟨by linear_combination -h2, by linear_combination h1 + algebraMap K (Lsq K Δ) τ * h2⟩

/- English proof (translation)
Establish `hij : ∀ i j, ∑ k, Pm k i * star (Pm k j) = diagonal g i j`. Introduce `i j`. Rewrite using `[e]`. Simplify using `[Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∑ i, ∑ j, (∑ k, Pm k i * star (Pm k j)) * (a i * star (a' j)) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_mul]`.

Use `_ = ∑ i, g i * a i * star (a' i) := by`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[hij]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[mul_assoc]`.

Introduce `j _ hj`. Rewrite using `[Matrix.diagonal_apply_ne _ (Ne.symm hj)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
private theorem diag_sum (Pm : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (g : Fin 3 → Lsq K Δ)
    (e : diagonal g = Pmᵀ * Pm.map star) (a a' : Fin 3 → Lsq K Δ) :
    ∑ k, (Pm *ᵥ a) k * star ((Pm *ᵥ a') k) = ∑ i, g i * a i * star (a' i) := by
  have hij : ∀ i j, ∑ k, Pm k i * star (Pm k j) = diagonal g i j := by
    intro i j
    rw [e]
    simp [Matrix.mul_apply]
  calc ∑ k, (Pm *ᵥ a) k * star ((Pm *ᵥ a') k)
      = ∑ k, ∑ i, ∑ j, Pm k i * star (Pm k j) * (a i * star (a' j)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, (∑ k, Pm k i * star (Pm k j)) * (a i * star (a' j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ = ∑ i, g i * a i * star (a' i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [hij]
        rw [Finset.sum_eq_single i]
        · simp [mul_assoc]
        · intro j _ hj
          rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
          ring
        · simp

/- English proof (translation)
Take `⟨hsi, hsr⟩` from `star_parts h.m_star`. Establish `fix : ∀ z : Lsq K Δ, star z = z → algebraMap K (Lsq K Δ) z.re = z`. Introduce `z hz`. Establish `h1` using `congrArg QuadraticAlgebra.im hz`. Rewrite `h1` using `[QuadraticAlgebra.im_star]`.

Establish `h2 : z.im = 0`. Establish `h3 : (2 : K) * z.im = 0` using `by linear_combination -h1`. Simplify using `using h3`. Use `ext`. Simplify using the standard rewrite rules.

Simplify using `[h2]`. Establish `hA : QuadraticAlgebra.trace m = 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im` using `rfl`. Establish `hAs : star (QuadraticAlgebra.trace m) = QuadraticAlgebra.trace m`. Rewrite using `[hA]`. Simplify using `only [star_add, star_mul', st_alg', star_ofNat, hsr, hsi]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(QuadraticAlgebra.trace m).re, fix _ hAs, fun hg0 => ?_⟩` and prove the remaining obligations. Establish `hG : algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re = 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im` using `(fix _ hAs).trans hA`. Take `⟨y, hy⟩` from `exG_norm h`. Establish `hGi : algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ * algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hg0, map_one]`. Establish `hG2 : algebraMap K (Lsq K Δ) ((2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re) * algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re = algebraMap K (Lsq K Δ) (2 - τ) * (y * star y)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hg0, map_mul, QuadraticAlgebra.algebraMap_norm_eq_mul_star]`. Use `⟨(2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re, algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ * (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im), y, ?_, ?_⟩` and prove the remaining obligations. Introduce `u v`.

Simplify using `only [herm]`. Rewrite using `[tr_form]`. Rewrite `hGi`, `hG2`, the goal using `[hG]`. Rewrite `hy` using `[QuadraticAlgebra.norm_def]`. Simplify using `only [map_sub, map_add, map_ofNat] at hG2 hy`.

Simplify using `only [star_add, star_mul', star_sub, star_pow, st_alg', star_ofNat, hsr, hsi]`. Take the linear combination `(-((algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im) * u.2.re * star v.2.im) - (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) * u.2.im * star v.2.re - u.2.im * star v.2.im * ((2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) - algebraMap K (Lsq K Δ) ((2 - τ …`. Rewrite using `[map_mul, mul_comm]`. Conclude with `hG2`.
-/
private theorem gram_diag [CharZero K] {c : K} {d m : EL Δ τ} (h : IsDat c d m) :
    ∃ g : K, algebraMap K (Lsq K Δ) g = QuadraticAlgebra.trace m ∧ (g ≠ 0 → ∃ (g2 : K) (b y : Lsq K Δ),
      (∀ u v : Sp Δ τ, herm c m u v = algebraMap K (Lsq K Δ) c * u.1 * star v.1 +
        algebraMap K (Lsq K Δ) g * (u.2.re + u.2.im * b) * star (v.2.re + v.2.im * b) +
        algebraMap K (Lsq K Δ) g2 * u.2.im * star v.2.im) ∧
      algebraMap K (Lsq K Δ) (g * g2) = algebraMap K (Lsq K Δ) (2 - τ) * (y * star y)) := by
  obtain ⟨hsi, hsr⟩ := star_parts h.m_star
  have fix : ∀ z : Lsq K Δ, star z = z → algebraMap K (Lsq K Δ) z.re = z := by
    intro z hz
    have h1 := congrArg QuadraticAlgebra.im hz
    rw [QuadraticAlgebra.im_star] at h1
    have h2 : z.im = 0 := by
      have h3 : (2 : K) * z.im = 0 := by linear_combination -h1
      simpa using h3
    ext
    · simp
    · simp [h2]
  have hA : QuadraticAlgebra.trace m = 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im := rfl
  have hAs : star (QuadraticAlgebra.trace m) = QuadraticAlgebra.trace m := by
    rw [hA]
    simp only [star_add, star_mul', st_alg', star_ofNat, hsr, hsi]
    ring
  refine ⟨(QuadraticAlgebra.trace m).re, fix _ hAs, fun hg0 => ?_⟩
  have hG : algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re =
      2 * m.re + algebraMap K (Lsq K Δ) τ * m.im := (fix _ hAs).trans hA
  obtain ⟨y, hy⟩ := exG_norm h
  have hGi : algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
      algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hg0, map_one]
  have hG2 : algebraMap K (Lsq K Δ) ((2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re) *
      algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re =
      algebraMap K (Lsq K Δ) (2 - τ) * (y * star y) := by
    rw [← map_mul, div_mul_cancel₀ _ hg0, map_mul, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  refine ⟨(2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re,
    algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
      (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im), y, ?_, ?_⟩
  · intro u v
    simp only [herm]
    rw [tr_form]
    rw [hG] at hGi hG2 ⊢
    rw [QuadraticAlgebra.norm_def] at hy
    simp only [map_sub, map_add, map_ofNat] at hG2 hy
    simp only [star_add, star_mul', star_sub, star_pow, st_alg', star_ofNat, hsr, hsi]
    linear_combination
      (-((algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im) * u.2.re * star v.2.im) -
        (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) * u.2.im * star v.2.re -
        u.2.im * star v.2.im * ((2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) -
          algebraMap K (Lsq K Δ) ((2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re)) -
        u.2.im * star v.2.im * algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
          (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) *
          (algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im)) * hGi +
      (-(u.2.im * star v.2.im * algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹)) * hG2 +
      (u.2.im * star v.2.im * algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
        (2 - algebraMap K (Lsq K Δ) τ)) * hy
  · rw [map_mul, mul_comm]
    exact hG2

end Gram

section Main

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨r, rfl⟩` from `h`. Establish `hr : r ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h0`. Unfold `hs`.

Rewrite using `[if_pos]`. Use `⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hs_sq {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h0
  unfold hs
  rw [if_pos]
  refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

/- English proof (translation)
Establish `harch : ∀ σ : F →+* ℝ, hs (σ Δ) (σ w) = 1`. Introduce `σ`. Unfold `hs`. Rewrite using `[if_pos]`. Conclude with `⟨Real.sqrt (σ w), 0, by simp [Real.sq_sqrt (hw σ).le]⟩`.

Establish `hloc : ∀ v : Pl F, hs (cv v Δ) (cv v w) = 1`. Introduce `v`. Distinguish the cases in `hv : v ∈ D.Sg`. Use `haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective`. Conclude with `hs_sq ((map_ne_zero (cv v)).mpr hΔ0) (hok.split v hv) _`.

Establish `hl` using `hok.off v hv`. Conclude with `(hsLaw (Ov v) (Kv v) _ hl).2.1 _ _ hl.even (hev v hv)`. Establish `hH` using `hsHasse F Δ w hΔ0 hw0 harch hloc`. Unfold `hs at hH`. Use `split_ifs at hH with hab`.

Take `⟨a, b, hab⟩` from `hab`. Use `⟨⟨a, b⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuadraticAlgebra.algebraMap_norm_eq_mul_star]`. Use `congr 1`. Rewrite using `[QuadraticAlgebra.norm_def]`.

Simplify using `only`. Take the linear combination `-hab`. Evaluate the numerical expressions using `at hH`.
-/
private theorem disc_norm {Δ : F} (D : Dat Δ) (hok : D.Ok) (hΔ0 : Δ ≠ 0) {w : F} (hw : TPos w) (hw0 : w ≠ 0) (hev : D.Ev w) :
    ∃ u : Lsq F Δ, algebraMap F (Lsq F Δ) w = u * star u := by
  have harch : ∀ σ : F →+* ℝ, hs (σ Δ) (σ w) = 1 := by
    intro σ
    unfold hs
    rw [if_pos]
    exact ⟨Real.sqrt (σ w), 0, by simp [Real.sq_sqrt (hw σ).le]⟩
  have hloc : ∀ v : Pl F, hs (cv v Δ) (cv v w) = 1 := by
    intro v
    by_cases hv : v ∈ D.Sg
    · haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
      exact hs_sq ((map_ne_zero (cv v)).mpr hΔ0) (hok.split v hv) _
    · have hl := hok.off v hv
      exact (hsLaw (Ov v) (Kv v) _ hl).2.1 _ _ hl.even (hev v hv)
  have hH := hsHasse F Δ w hΔ0 hw0 harch hloc
  unfold hs at hH
  split_ifs at hH with hab
  · obtain ⟨a, b, hab⟩ := hab
    refine ⟨⟨a, b⟩, ?_⟩
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    congr 1
    rw [QuadraticAlgebra.norm_def]
    simp only
    linear_combination -hab
  · norm_num at hH

/- English proof (translation)
Establish `h` using `hneg σ`. Rewrite using `[QuadraticAlgebra.norm_def]`. Simplify using `only [map_add, map_sub, map_mul, map_zero, zero_mul, add_zero]`. Use polynomial arithmetic with `[sq_nonneg (σ y.re), sq_nonneg (σ y.im), mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ y.im))]`.
-/
private theorem norm_pos_part {Δ : F} (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (y : Lsq F Δ) (σ : F →+* ℝ) :
    0 ≤ σ (QuadraticAlgebra.norm y) := by
  have h := hneg σ
  rw [QuadraticAlgebra.norm_def]
  simp only [map_add, map_sub, map_mul, map_zero, zero_mul, add_zero]
  nlinarith [sq_nonneg (σ y.re), sq_nonneg (σ y.im), mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ y.im))]

end Main

/- English proof (translation)
Introduce `F _ _ Δ D hok τ c d m hdat hpos hev`. Use `haveI : IsTotallyReal F := hok.real`. Establish `hΔ0 : Δ ≠ 0`. Introduce `h0`. Conclude with `exG_nonsq hok.neg 0 (by rw [h0]; ring)`.

Take `⟨g, hg, hg2⟩` from `gram_diag hdat`. Establish `hcpos : TPos c`. Establish `hne : ((1, 0) : Sp Δ τ) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Prod.fst h0`.

Simplify using `at h1`. Establish `h1` using `hpos _ hne`. Simplify `h1` using `[herm, sigL]`. Establish `hx1ne : ((0, ⟨1, 0⟩) : Sp Δ τ) ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg (fun p : Sp Δ τ => p.2.re) h0`. Simplify using `at h1`. Establish `hx1 : herm c m (0, ⟨1, 0⟩) (0, ⟨1, 0⟩) = algebraMap F (Lsq F Δ) g`. Rewrite using `[hg, herm, tr_form]`. Simplify using `only [star_zero, star_one, mul_zero, zero_mul, mul_one, add_zero, zero_add, map_zero]`.

Both sides reduce to the same expression. Establish `hgpos : TPos g`. Establish `h1` using `hpos _ hx1ne`. Rewrite `h1` using `[hx1]`. Simplify using `using h1`.

Establish `hg0 : g ≠ 0` using `exG_ne hgpos`. Take `⟨g2, b, y, hform, hprod⟩` from `hg2 hg0`. Establish `hx2ne : ((0, ⟨-b, 1⟩) : Sp Δ τ) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg (fun p : Sp Δ τ => p.2.im) h0`.

Simplify using `at h1`. Establish `hx2 : herm c m (0, ⟨-b, 1⟩) (0, ⟨-b, 1⟩) = algebraMap F (Lsq F Δ) g2`. Rewrite using `[hform]`. Simplify using the standard rewrite rules. Establish `hg2pos : TPos g2`.

Establish `h1` using `hpos _ hx2ne`. Rewrite `h1` using `[hx2]`. Simplify using `using h1`. Establish `hmain : g * g2 = (2 - τ) * QuadraticAlgebra.norm y`. Establish `h1` using `congrArg QuadraticAlgebra.re hprod`.

Rewrite `h1` using `[← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_mul]`. Simplify using `using h1`. Establish `h2τ : TPos (2 - τ)`. Introduce `σ`. Establish `h1` using `hgpos σ`.

Establish `h2` using `hg2pos σ`. Establish `h3` using `norm_pos_part hok.neg y σ`. Establish `h4` using `congrArg σ hmain`. Rewrite `h4` using `[map_mul, map_mul]`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Use polynomial arithmetic with `[mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hle) h3]`. Establish `hw : TPos (c * (2 - τ))` using `fun σ => by`. Rewrite using `[map_mul]`. Conclude with `mul_pos (hcpos σ) (h2τ σ)`.

Take `⟨u, hu⟩` from `disc_norm D hok hΔ0 hw (exG_ne hw) hev`. Set `gi : Fin 3 → F` to `![c, g, g2]`. Establish `hgi : ∀ i, TPos (gi i)`. Introduce `i`. Use `fin_cases i`.

Conclude with `hcpos`. Conclude with `hgpos`. Conclude with `hg2pos`. Establish `hprod3 : algebraMap F (Lsq F Δ) (∏ i, gi i) = (u * y) * star (u * y)`. Establish `hp : ∏ i, gi i = c * (g * g2)`.

Simplify using `[gi, Fin.prod_univ_three, mul_assoc]`. Establish `hu' : algebraMap F (Lsq F Δ) c * algebraMap F (Lsq F Δ) (2 - τ) = u * star u`. Rewrite using `[← map_mul]`. Conclude with `hu`. Rewrite using `[hp, map_mul, hprod, star_mul']`.

Take the linear combination `(y * star y) * hu'`. Take `⟨P, hPdet, hPe⟩` from `exG_land hok.neg gi hgi (u * y) hprod3`. Set `Co : Sp Δ τ ≃ₗ[Lsq F Δ] (Fin 3 → Lsq F Δ)` to `{ toFun := fun x => ![x.1, x.2.re + x.2.im * b, x.2.im] invFun := fun a => (a 0, (⟨a 1 - a 2 * b, a 2⟩ : EL Δ τ)) map_add' := by`. Introduce `x x'`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> simp <;> ring`. Use the proof step `map_smul' := by`. Introduce `r x`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul] <;> ring`.

Use `left_inv := by`. Introduce `x`. Apply the tactic sequence `ext <;> simp`. Use `right_inv := by`. Introduce `a`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp }`. Set `Pe` to `Co.trans (P.toLinearEquiv' (P.invertibleOfIsUnitDet hPdet))`. Establish `hherm : ∀ x x' : Sp Δ τ, herm c m x x' = ∑ i, Pe x i * star (Pe x' i)`. Introduce `x x'`.

Establish `e1 : ∀ z, Pe z = P *ᵥ Co z` using `fun z => by first`. Consider the case `rfl`. Consider the case `(simp only [Pe, LinearEquiv.trans_apply]; rw [← Matrix.toLin'_apply]; rfl)`. Consider the case `(simp only [Pe, LinearEquiv.trans_apply, ← LinearEquiv.coe_toLinearMap, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply])`. Rewrite using `[e1, e1, diag_sum P (fun i => algebraMap F (Lsq F Δ) (gi i)) hPe, Fin.sum_univ_three, hform]`.

Simplify using `[Co, gi]`. Take `⟨δ, ι', hM⟩` from `exG_models hdat Pe hherm`. Conclude with `⟨δ, ι', Pe, hM⟩`.
-/
theorem exG : ExG := by
  intro F _ _ Δ D hok τ c d m hdat hpos hev
  haveI : IsTotallyReal F := hok.real
  have hΔ0 : Δ ≠ 0 := by
    intro h0
    exact exG_nonsq hok.neg 0 (by rw [h0]; ring)
  obtain ⟨g, hg, hg2⟩ := gram_diag hdat
  have hcpos : TPos c := by
    have hne : ((1, 0) : Sp Δ τ) ≠ 0 := by
      intro h0
      have h1 := congrArg Prod.fst h0
      simp at h1
    have h1 := hpos _ hne
    simpa [herm, sigL] using h1
  have hx1ne : ((0, ⟨1, 0⟩) : Sp Δ τ) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun p : Sp Δ τ => p.2.re) h0
    simp at h1
  have hx1 : herm c m (0, ⟨1, 0⟩) (0, ⟨1, 0⟩) = algebraMap F (Lsq F Δ) g := by
    rw [hg, herm, tr_form]
    simp only [star_zero, star_one, mul_zero, zero_mul, mul_one, add_zero, zero_add, map_zero]
    rfl
  have hgpos : TPos g := by
    have h1 := hpos _ hx1ne
    rw [hx1] at h1
    simpa using h1
  have hg0 : g ≠ 0 := exG_ne hgpos
  obtain ⟨g2, b, y, hform, hprod⟩ := hg2 hg0
  have hx2ne : ((0, ⟨-b, 1⟩) : Sp Δ τ) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun p : Sp Δ τ => p.2.im) h0
    simp at h1
  have hx2 : herm c m (0, ⟨-b, 1⟩) (0, ⟨-b, 1⟩) = algebraMap F (Lsq F Δ) g2 := by
    rw [hform]
    simp
  have hg2pos : TPos g2 := by
    have h1 := hpos _ hx2ne
    rw [hx2] at h1
    simpa using h1
  have hmain : g * g2 = (2 - τ) * QuadraticAlgebra.norm y := by
    have h1 := congrArg QuadraticAlgebra.re hprod
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_mul] at h1
    simpa using h1
  have h2τ : TPos (2 - τ) := by
    intro σ
    have h1 := hgpos σ
    have h2 := hg2pos σ
    have h3 := norm_pos_part hok.neg y σ
    have h4 := congrArg σ hmain
    rw [map_mul, map_mul] at h4
    by_contra hle
    push_neg at hle
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hle) h3]
  have hw : TPos (c * (2 - τ)) := fun σ => by
    rw [map_mul]
    exact mul_pos (hcpos σ) (h2τ σ)
  obtain ⟨u, hu⟩ := disc_norm D hok hΔ0 hw (exG_ne hw) hev
  let gi : Fin 3 → F := ![c, g, g2]
  have hgi : ∀ i, TPos (gi i) := by
    intro i
    fin_cases i
    · exact hcpos
    · exact hgpos
    · exact hg2pos
  have hprod3 : algebraMap F (Lsq F Δ) (∏ i, gi i) = (u * y) * star (u * y) := by
    have hp : ∏ i, gi i = c * (g * g2) := by
      simp [gi, Fin.prod_univ_three, mul_assoc]
    have hu' : algebraMap F (Lsq F Δ) c * algebraMap F (Lsq F Δ) (2 - τ) = u * star u := by
      rw [← map_mul]
      exact hu
    rw [hp, map_mul, hprod, star_mul']
    linear_combination (y * star y) * hu'
  obtain ⟨P, hPdet, hPe⟩ := exG_land hok.neg gi hgi (u * y) hprod3
  let Co : Sp Δ τ ≃ₗ[Lsq F Δ] (Fin 3 → Lsq F Δ) :=
    { toFun := fun x => ![x.1, x.2.re + x.2.im * b, x.2.im]
      invFun := fun a => (a 0, (⟨a 1 - a 2 * b, a 2⟩ : EL Δ τ))
      map_add' := by
        intro x x'
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro r x
        funext i
        fin_cases i <;> simp [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul] <;> ring
      left_inv := by
        intro x
        ext <;> simp
      right_inv := by
        intro a
        funext i
        fin_cases i <;> simp }
  let Pe := Co.trans (P.toLinearEquiv' (P.invertibleOfIsUnitDet hPdet))
  have hherm : ∀ x x' : Sp Δ τ, herm c m x x' = ∑ i, Pe x i * star (Pe x' i) := by
    intro x x'
    have e1 : ∀ z, Pe z = P *ᵥ Co z := fun z => by
      first
        | rfl
        | (simp only [Pe, LinearEquiv.trans_apply]; rw [← Matrix.toLin'_apply]; rfl)
        | (simp only [Pe, LinearEquiv.trans_apply, ← LinearEquiv.coe_toLinearMap, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply])
    rw [e1, e1, diag_sum P (fun i => algebraMap F (Lsq F Δ) (gi i)) hPe, Fin.sum_univ_three, hform]
    simp [Co, gi]
  obtain ⟨δ, ι', hM⟩ := exG_models hdat Pe hherm
  exact ⟨δ, ι', Pe, hM⟩

end UpperTheory.V.Z.Sym.Glob
