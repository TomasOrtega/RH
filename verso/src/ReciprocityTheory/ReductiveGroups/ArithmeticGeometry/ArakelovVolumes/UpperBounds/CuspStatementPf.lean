import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms

noncomputable section

namespace FactorialDivisibilityBounds

/- English proof (translation)
Introduce `n hn1 hnr`. Proceed by induction on `n with`. Consider the case `zero => omega`. Consider the case `succ n ih`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases.

Substitute `h0` using the available equality. Simplify using `only [zero_add, Finset.sum_range_one, Nat.sub_self, sub_self, zero_mul, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ih'` using `ih hpos (by omega)`. Rewrite using `[Finset.sum_range_succ]`.

Establish `hLn` using `hL n (by omega)`. Establish `key : (a (n - 1) - a n) * (L n - L p) ≤ 0`. Distinguish the cases in `hnp : n = p`. Rewrite using `[hnp, sub_self, mul_zero]`. Establish `h1` using `hgap n hpos (by omega) hnp`.

Conclude with `mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)`. Simplify using `only [Nat.add_sub_cancel]`. Use polynomial arithmetic with `[ih', key]`.
-/
theorem abel_bound (a L : ℕ → ℝ) (p r : ℕ) (hL : ∀ k ≤ r, L k ≤ L p)
    (hgap : ∀ k, 1 ≤ k → k < r → k ≠ p → a k ≤ a (k - 1)) :
    ∀ n, 1 ≤ n → n ≤ r → ∑ k ∈ Finset.range n, a k * (L (k + 1) - L k) ≤
      a (n - 1) * L n - a 0 * L 0 + (a 0 - a (n - 1)) * L p := by
  intro n hn1 hnr
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [zero_add, Finset.sum_range_one, Nat.sub_self, sub_self, zero_mul, add_zero]
      linarith
    · have ih' := ih hpos (by omega)
      rw [Finset.sum_range_succ]
      have hLn := hL n (by omega)
      have key : (a (n - 1) - a n) * (L n - L p) ≤ 0 := by
        by_cases hnp : n = p
        · rw [hnp, sub_self, mul_zero]
        · have h1 := hgap n hpos (by omega) hnp
          exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      simp only [Nat.add_sub_cancel]
      nlinarith [ih', key]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

def rfac (la : Wt X.Ψ r) (x y : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
    ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

/- English proof (translation)
Rewrite using `[Data.nfac, Data.nfac, ← Finset.prod_div_distrib]`. Conclude with `Finset.prod_congr rfl fun τ _ => (Finset.prod_div_distrib _ _).symm`.
-/
theorem nfac_div (la : Wt X.Ψ r) (x y : Frame X.Ψ r) :
    X.nfac la x / X.nfac la y = ∏ τ, rfac X la x y τ := by
  rw [Data.nfac, Data.nfac, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun τ _ => (Finset.prod_div_distrib _ _).symm

def rho (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ) : ℝ :=
  1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i

section Flow

variable (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
  (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ)
include he hx

/- English proof (translation)
Rewrite using `[dmin_eq, dmin_eq]`. Conclude with `dmin_flow X hx e τ (he τ).1 s j _`.
-/
theorem dmin_flow' (j : Fin (r + 1)) :
    dmin X.Gm (X.flowV e s x) τ j = dmin X.Gm x τ j * ((rho X e s x τ j : ℝ) : ℂ) := by
  rw [dmin_eq, dmin_eq]
  exact dmin_flow X hx e τ (he τ).1 s j _

/- English proof (translation)
Introduce `h0` and use `by have := (hx τ).2 j rw [h0, Complex.zero_re, mul_zero] at this exact lt_irrefl _ this`.
-/
theorem dmin_ne' (j : Fin (r + 1)) : dmin X.Gm x τ j ≠ 0 := fun h0 => by
  have := (hx τ).2 j
  rw [h0, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

include hT in
/- English proof (translation)
Introduce `i hi` and use `by have h1 := (hT τ).2 ⟨i, Nat.lt_succ_of_le hi⟩ rw [dmin_flow' X e he hx s τ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← mul_assoc] at h1 exact (mul_pos_iff_of_pos_left ((hx τ).2 ⟨i, Nat.lt_succ_of_le hi⟩)).mp h1`.
-/
theorem rho_pos : ∀ i ≤ r, 0 < rho X e s x τ i := fun i hi => by
  have h1 := (hT τ).2 ⟨i, Nat.lt_succ_of_le hi⟩
  rw [dmin_flow' X e he hx s τ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, ← mul_assoc] at h1
  exact (mul_pos_iff_of_pos_left ((hx τ).2 ⟨i, Nat.lt_succ_of_le hi⟩)).mp h1

include hT in
/- English proof (translation)
Establish `hρ` using `rho_pos X e he hx s hT τ`. Establish `hfac : ∀ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) / ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) = Real.exp ((la τ i : ℝ) / 2 * (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho …`. Introduce `i`. Establish `hρ1` using `hρ ((i : ℕ) + 1) i.2`. Establish `hρ0` using `hρ i i.2.le`.

Establish `hN : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖` using `norm_pos_iff.mpr (div_ne_zero (dmin_ne' X e he hx τ _) (dmin_ne' X e he hx τ _))`. Rewrite using `[dmin_flow' X e he hx s τ, dmin_flow' X e he hx s τ, Fin.val_succ, Fin.val_castSucc]`. Establish `hn : ‖dmin X.Gm x τ i.succ * ((rho X e s x τ ((i : ℕ) + 1) : ℝ) : ℂ) / (dmin X.Gm x τ i.castSucc * ((rho X e s x τ i : ℝ) : ℂ))‖ = ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ * (rho X e s x τ ((i : ℕ) + 1) / rho X e s x τ i)`. Rewrite using `[norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hρ1.le, Real.norm_of_nonneg hρ0.le, norm_div]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hn, Real.mul_rpow hN.le (div_pos hρ1 hρ0).le, div_mul_cancel_left₀ (Real.rpow_pos_of_pos hN _).ne', ← Real.rpow_neg (div_pos hρ1 hρ0).le, Real.rpow_def_of_pos (div_pos hρ1 hρ0), Real.log_div hρ1.ne' hρ0.ne']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[rfac, Finset.prod_congr rfl fun i _ => hfac i, ← Real.exp_sum]`.
-/
theorem rfac_eq (la : Wt X.Ψ r) :
    rfac X la x (X.flowV e s x) τ = Real.exp (∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i))) := by
  have hρ := rho_pos X e he hx s hT τ
  have hfac : ∀ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
      ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2) =
      Real.exp ((la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i))) := by
    intro i
    have hρ1 := hρ ((i : ℕ) + 1) i.2
    have hρ0 := hρ i i.2.le
    have hN : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
      norm_pos_iff.mpr (div_ne_zero (dmin_ne' X e he hx τ _) (dmin_ne' X e he hx τ _))
    rw [dmin_flow' X e he hx s τ, dmin_flow' X e he hx s τ, Fin.val_succ, Fin.val_castSucc]
    have hn : ‖dmin X.Gm x τ i.succ * ((rho X e s x τ ((i : ℕ) + 1) : ℝ) : ℂ) /
        (dmin X.Gm x τ i.castSucc * ((rho X e s x τ i : ℝ) : ℂ))‖ =
        ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ *
          (rho X e s x τ ((i : ℕ) + 1) / rho X e s x τ i) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hρ1.le, Real.norm_of_nonneg hρ0.le, norm_div]
      field_simp
    rw [hn, Real.mul_rpow hN.le (div_pos hρ1 hρ0).le,
      div_mul_cancel_left₀ (Real.rpow_pos_of_pos hN _).ne', ← Real.rpow_neg (div_pos hρ1 hρ0).le,
      Real.rpow_def_of_pos (div_pos hρ1 hρ0), Real.log_div hρ1.ne' hρ0.ne']
    congr 1
    ring
  rw [rfac, Finset.prod_congr rfl fun i _ => hfac i, ← Real.exp_sum]

include hT in
/- English proof (translation)
Rewrite using `[rfac_eq X e he hx s hT τ la]`. Establish `h1 : ∀ i, rho X e s x τ i = 1` using `fun i => by simp [rho, hs]`. Simplify using `[h1]`.
-/
theorem rfac_of_zero (la : Wt X.Ψ r) (hs : s τ = 0) : rfac X la x (X.flowV e s x) τ = 1 := by
  rw [rfac_eq X e he hx s hT τ la]
  have h1 : ∀ i, rho X e s x τ i = 1 := fun i => by simp [rho, hs]
  simp [h1]

include hT in
/- English proof (translation)
Rewrite using `[rfac_eq X e he hx s hT τ la]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hρ` using `rho_pos X e he hx s hT τ`. Establish `hsg` using `hsg_of X hx τ`. Establish `hb : 0 ≤ 2 * X.c τ * (s τ).im` using `by have := c_pos X τ; positivity`.

Establish `hmb : ∀ i ≤ r, 0 ≤ mN τ.1 X.Gm (mat x τ) (e τ) i ∧ mN τ.1 X.Gm (mat x τ) (e τ) i ≤ mN τ.1 X.Gm (mat x τ) (e τ) X.p0` using `fun i hi => mN_bounds (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 hsg (e τ) (he τ).1 i hi`. Use `set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef`. Establish `hL0 : L 0 = 0` using `by simp [L, rho, mN_zero]`. Establish `hLr : L r = 0`. Simplify using `[L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]`.

Establish `hLle : ∀ k ≤ r, L k ≤ L X.p0` using `fun k hk => by`. Apply `Real.log_le_log (hρ k hk)` to reduce the goal to its premises. Simplify using `only [rho]`. Use polynomial arithmetic with `[(hmb k hk).2]`. Establish `hLp : 0 ≤ L X.p0`.

Apply `Real.log_nonneg` to reduce the goal to its premises. Simplify using `only [rho]`. Use polynomial arithmetic with `[(hmb X.p0 X.p0_le).1]`. Use `set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha`. Establish `hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 * (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) = ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k)`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]`. Establish `hgap' : ∀ k, 1 ≤ k → k < r → k ≠ X.p0 → a k ≤ a (k - 1)`. Introduce `k hk1 hkr hkp`. Simplify using `only [a, dif_pos hkr, dif_pos (show k - 1 < r by omega)]`.

Use `hgap ⟨k - 1, by omega⟩ ⟨k, hkr⟩ (by simp; omega) hkp` as an intermediate fact. Establish `: (la τ ⟨k, hkr⟩ : ℝ) ≤ la τ ⟨k - 1, by omega⟩` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hab` using `abel_bound a L X.p0 r hLle hgap' r (by omega) le_rfl`. Rewrite `hab` using `[hL0, hLr]`.

Establish `hpa : a 0 - a (r - 1) ≤ -(1 / 2)`. Simplify using `only [a, dif_pos (show 0 < r by omega), dif_pos (show r - 1 < r by omega)]`. Use `hpair ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl` as an intermediate fact. Establish `: (la τ ⟨0, by omega⟩ : ℝ) + 1 ≤ la τ ⟨r - 1, by omega⟩` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0`. Rewrite using `[Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]`. Simplify using `only [rho]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, hq]`.

Establish `: (a 0 - a (r - 1)) * L X.p0 ≤ -(1 / 2) * L X.p0` using `mul_le_mul_of_nonneg_right hpa hLp`. Use `show _ ≤ -(1 / 2) * L X.p0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rfac_le (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im) (hp0 : 0 < X.p0) (hp0r : X.p0 < r)
    (hgap : ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i)
    (hpair : ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ i0 < la τ i1) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by
  rw [rfac_eq X e he hx s hT τ la]
  apply Real.exp_le_exp.mpr
  have hρ := rho_pos X e he hx s hT τ
  have hsg := hsg_of X hx τ
  have hb : 0 ≤ 2 * X.c τ * (s τ).im := by have := c_pos X τ; positivity
  have hmb : ∀ i ≤ r, 0 ≤ mN τ.1 X.Gm (mat x τ) (e τ) i ∧
      mN τ.1 X.Gm (mat x τ) (e τ) i ≤ mN τ.1 X.Gm (mat x τ) (e τ) X.p0 :=
    fun i hi => mN_bounds (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 hsg (e τ) (he τ).1 i hi
  set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
  have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
  have hLr : L r = 0 := by
    simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
  have hLle : ∀ k ≤ r, L k ≤ L X.p0 := fun k hk => by
    apply Real.log_le_log (hρ k hk)
    simp only [rho]
    nlinarith [(hmb k hk).2]
  have hLp : 0 ≤ L X.p0 := by
    apply Real.log_nonneg
    simp only [rho]
    nlinarith [(hmb X.p0 X.p0_le).1]
  set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha
  have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
      ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]
    exact Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]
  have hgap' : ∀ k, 1 ≤ k → k < r → k ≠ X.p0 → a k ≤ a (k - 1) := by
    intro k hk1 hkr hkp
    simp only [a, dif_pos hkr, dif_pos (show k - 1 < r by omega)]
    have := hgap ⟨k - 1, by omega⟩ ⟨k, hkr⟩ (by simp; omega) hkp
    have : (la τ ⟨k, hkr⟩ : ℝ) ≤ la τ ⟨k - 1, by omega⟩ := by exact_mod_cast this
    linarith
  have hab := abel_bound a L X.p0 r hLle hgap' r (by omega) le_rfl
  rw [hL0, hLr] at hab
  have hpa : a 0 - a (r - 1) ≤ -(1 / 2) := by
    simp only [a, dif_pos (show 0 < r by omega), dif_pos (show r - 1 < r by omega)]
    have := hpair ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have : (la τ ⟨0, by omega⟩ : ℝ) + 1 ≤ la τ ⟨r - 1, by omega⟩ := by exact_mod_cast this
    linarith
  have hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0 := by
    rw [Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]
    simp only [rho]
    ring
  rw [hsum, hq]
  have : (a 0 - a (r - 1)) * L X.p0 ≤ -(1 / 2) * L X.p0 :=
    mul_le_mul_of_nonneg_right hpa hLp
  show _ ≤ -(1 / 2) * L X.p0
  linarith

end Flow

end FactorialDivisibilityBounds

open FactorialDivisibilityBounds

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la τ0 hp0 hp0r hgap hpair P hP`. Use `⟨hP, fun ξ hξ x hx => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hP.2`. Establish `hiso : X.IsIsoV (X.embV ξ)` using `fun τ => ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero], emb_ne_zero τ.1 hξ.2.2⟩`. Use `set G := X.fj la ξ 0 P with hG`.

Establish `hGb : ∀ y ∈ X.dom, ‖G y‖ * X.nfac la y ≤ C` using `fun y hy => FlowCoefficientBounds.fj_bound X la P C hC hξ 0 hy`. Establish `hGd : DifferentiableOn ℂ G X.dom` using `CuspCoefficientFlow.fj_diffOn X la P hP hξ 0`. Establish `hreal : ∀ s : X.Ψ → ℝ, G (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) = cexp (4 * Real.pi * I * ∑ τ, (0 : X.Ψ → ℂ) τ * s τ) * G x`. Introduce `s`. Use `X.fj_flow_real la ξ hξ 0 P hP.1 ⟨C, hC⟩ x hx s` as an intermediate fact.

Simplify using `only [Pi.zero_apply, Complex.ofReal_zero, zero_mul] at this ⊢`. Conclude with `this`. Establish `hcx` using `holomorphic_periodicity_extension r X (X.embV ξ) hiso G hGd 0 x hx hreal`. Assume the negation of the conclusion as `hne`. Establish `hN` using `FlowCoefficientBounds.nfac_pos X hx la`.

Establish `hA : 0 < ‖G x‖ * X.nfac la x` using `mul_pos (norm_pos_iff.mpr hne) hN`. Establish `hmaj` using `maj_eq X hx (X.embV ξ) τ0 (hiso τ0).1`. Establish `hmpos` using `mN_pos (hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1 (hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2`. Establish `htt : 0 < X.ttV (X.embV ξ) x τ0`. Rewrite using `[Data.ttV, hmaj]`.

Use `c_pos X τ0` as an intermediate fact. Check the signs of the components of the expression. Use `set M : ℝ := |Real.log (C / (‖G x‖ * X.nfac la x))| + 1 with hM`. Establish `hM0 : 0 < M` using `by positivity`. Use `set t : ℝ := X.ttV (X.embV ξ) x τ0 * (Real.exp (2 * M) - 1) with ht`.

Establish `ht0 : 0 < t` using `mul_pos htt (by linarith [Real.add_one_lt_exp (show (2 * M) ≠ 0 by positivity)])`. Set `s : X.Ψ → ℂ` to `fun τ => if τ = τ0 then I * t else 0`. Establish `hs0 : (s τ0).im = t` using `by simp [s]`. Establish `hdom : X.flowV (X.embV ξ) s x ∈ X.dom`. Use `(flowDomainCriterion_holds r X _ hiso x hx s).1.mpr fun τ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : τ = τ0`. Substitute `h` using the available equality. Rewrite using `[hs0]`. Establish `: 0 < t / X.ttV (X.embV ξ) x τ` using `div_pos ht0 htt`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[s, h]`. Establish `hq : 1 + (s τ0).im / X.ttV (X.embV ξ) x τ0 = Real.exp (2 * M)`. Rewrite using `[hs0, ht, mul_div_cancel_left₀ _ htt.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `hratio : X.nfac la x / X.nfac la (X.flowV (X.embV ξ) s x) ≤ Real.exp (-M)`.

Rewrite using `[nfac_div, Finset.prod_eq_single τ0 (fun τ _ hτ => rfac_of_zero X _ hiso hx s hdom τ la (by simp [s, hτ])) (fun h => absurd (Finset.mem_univ τ0) h)]`. Use `(rfac_le X _ hiso hx s hdom τ0 la (by rw [hs0]; exact ht0.le) hp0 hp0r (hgap) hpair).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hq, Real.log_exp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hNT` using `FlowCoefficientBounds.nfac_pos X hdom la`. Establish `hGT : G (X.flowV (X.embV ξ) s x) = G x`. Rewrite using `[hcx s hdom]`. Simplify using the standard rewrite rules. Establish `h1 : X.nfac la x ≤ X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M)`.

Rewrite `hratio` using `[div_le_iff₀ hNT]`. Rewrite using `[mul_comm]`. Conclude with `hratio`. Establish `h2 : ‖G x‖ * X.nfac la x ≤ C * Real.exp (-M)`. Combine the equalities or inequalities in the displayed calculation.

Break down `le_or_gt C 0 with hC0 | hC0` into its components or cases. Establish `: C * Real.exp (-M) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlt : Real.log (C / (‖G x‖ * X.nfac la x)) < M`. Use `le_abs_self (Real.log (C / (‖G x‖ * X.nfac la x)))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : C / (‖G x‖ * X.nfac la x) < Real.exp M`. Rewrite using `[← Real.exp_log (div_pos hC0 hA)]`. Conclude with `Real.exp_lt_exp.mpr hlt`. Establish `h4 : C * Real.exp (-M) < ‖G x‖ * X.nfac la x`.

Rewrite using `[Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]`. Rewrite `h3` using `[div_lt_iff₀ hA]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cuspStatement_holds : CuspStatement (E := E) := by
  intro r X la τ0 hp0 hp0r hgap hpair P hP
  classical
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  obtain ⟨C, hC⟩ := hP.2
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  set G := X.fj la ξ 0 P with hG
  have hGb : ∀ y ∈ X.dom, ‖G y‖ * X.nfac la y ≤ C := fun y hy =>
    FlowCoefficientBounds.fj_bound X la P C hC hξ 0 hy
  have hGd : DifferentiableOn ℂ G X.dom := CuspCoefficientFlow.fj_diffOn X la P hP hξ 0
  have hreal : ∀ s : X.Ψ → ℝ, G (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (0 : X.Ψ → ℂ) τ * s τ) * G x := by
    intro s
    have := X.fj_flow_real la ξ hξ 0 P hP.1 ⟨C, hC⟩ x hx s
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul] at this ⊢
    exact this
  have hcx := holomorphic_periodicity_extension r X (X.embV ξ) hiso G hGd 0 x hx hreal
  by_contra hne
  have hN := FlowCoefficientBounds.nfac_pos X hx la
  have hA : 0 < ‖G x‖ * X.nfac la x := mul_pos (norm_pos_iff.mpr hne) hN
  have hmaj := maj_eq X hx (X.embV ξ) τ0 (hiso τ0).1
  have hmpos := mN_pos (hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1 (hsg_of X hx τ0)
    (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htt : 0 < X.ttV (X.embV ξ) x τ0 := by
    rw [Data.ttV, hmaj]
    have := c_pos X τ0
    positivity
  set M : ℝ := |Real.log (C / (‖G x‖ * X.nfac la x))| + 1 with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := X.ttV (X.embV ξ) x τ0 * (Real.exp (2 * M) - 1) with ht
  have ht0 : 0 < t := mul_pos htt (by linarith [Real.add_one_lt_exp (show (2 * M) ≠ 0 by positivity)])
  let s : X.Ψ → ℂ := fun τ => if τ = τ0 then I * t else 0
  have hs0 : (s τ0).im = t := by simp [s]
  have hdom : X.flowV (X.embV ξ) s x ∈ X.dom := by
    refine (flowDomainCriterion_holds r X _ hiso x hx s).1.mpr fun τ => ?_
    by_cases h : τ = τ0
    · subst h
      rw [hs0]
      have : 0 < t / X.ttV (X.embV ξ) x τ := div_pos ht0 htt
      linarith
    · simp [s, h]
  have hq : 1 + (s τ0).im / X.ttV (X.embV ξ) x τ0 = Real.exp (2 * M) := by
    rw [hs0, ht, mul_div_cancel_left₀ _ htt.ne']
    ring
  have hratio : X.nfac la x / X.nfac la (X.flowV (X.embV ξ) s x) ≤ Real.exp (-M) := by
    rw [nfac_div, Finset.prod_eq_single τ0 (fun τ _ hτ => rfac_of_zero X _ hiso hx s hdom τ la
      (by simp [s, hτ])) (fun h => absurd (Finset.mem_univ τ0) h)]
    refine (rfac_le X _ hiso hx s hdom τ0 la (by rw [hs0]; exact ht0.le) hp0 hp0r (hgap) hpair).trans
      (le_of_eq ?_)
    rw [hq, Real.log_exp]
    congr 1
    ring
  have hNT := FlowCoefficientBounds.nfac_pos X hdom la
  have hGT : G (X.flowV (X.embV ξ) s x) = G x := by
    rw [hcx s hdom]
    simp
  have h1 : X.nfac la x ≤ X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M) := by
    rw [div_le_iff₀ hNT] at hratio
    rw [mul_comm]
    exact hratio
  have h2 : ‖G x‖ * X.nfac la x ≤ C * Real.exp (-M) := by
    calc ‖G x‖ * X.nfac la x ≤ ‖G x‖ * (X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖G (X.flowV (X.embV ξ) s x)‖ * X.nfac la (X.flowV (X.embV ξ) s x)) *
          Real.exp (-M) := by rw [hGT]; ring
      _ ≤ C * Real.exp (-M) := mul_le_mul_of_nonneg_right (hGb _ hdom) (Real.exp_pos _).le
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * Real.exp (-M) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le
    linarith
  · have hlt : Real.log (C / (‖G x‖ * X.nfac la x)) < M := by
      have := le_abs_self (Real.log (C / (‖G x‖ * X.nfac la x)))
      linarith
    have h3 : C / (‖G x‖ * X.nfac la x) < Real.exp M := by
      rw [← Real.exp_log (div_pos hC0 hA)]
      exact Real.exp_lt_exp.mpr hlt
    have h4 : C * Real.exp (-M) < ‖G x‖ * X.nfac la x := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ hA] at h3
      linarith
    linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
