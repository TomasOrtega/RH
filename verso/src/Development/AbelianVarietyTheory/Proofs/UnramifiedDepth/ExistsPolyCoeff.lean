import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

namespace GlobalTheory.IntegralEndLimit

/- English proof (translation)
Consider the cases of `x with`. Consider the case `top => exact ⟨0, le_top⟩`. Consider the case `coe t => exact ⟨t, le_rfl⟩`.
-/
theorem exists_real_le (x : WithTop ℝ) : ∃ t : ℝ, (t : WithTop ℝ) ≤ x := by
  cases x with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

/- English proof (translation)
Rewrite using `[v.map_mul]`. Use `le_trans ?_ (add_le_add hx hy)` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add]`. Conclude with `WithTop.coe_le_coe.2 h`.
-/
theorem le_val_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x y : C} {s t u : ℝ}
    (hx : (s : WithTop ℝ) ≤ v x) (hy : (t : WithTop ℝ) ≤ v y) (h : u ≤ s + t) :
    (u : WithTop ℝ) ≤ v (x * y) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add hx hy)
  rw [← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 h

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on generalizing s with`. Consider the case `C a => exact ⟨0, fun x' _ => by simp⟩`. Consider the case `add p q hp hq`. Take `⟨r₁, h₁⟩` from `hp s`. Take `⟨r₂, h₂⟩` from `hq s`.

Use `⟨max r₁ r₂, fun x' hx' => ?_⟩` and prove the remaining obligations. Establish `e : MvPolynomial.eval x (p + q) - MvPolynomial.eval x' (p + q) = (MvPolynomial.eval x p - MvPolynomial.eval x' p) + (MvPolynomial.eval x q - MvPolynomial.eval x' q)`. Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `le_trans (le_min (h₁ x' fun i => le_trans ?_ (hx' i)) (h₂ x' fun i => le_trans ?_ (hx' i))) (v.map_add _ _)` and prove the remaining obligations. Conclude with `WithTop.coe_le_coe.2 (le_max_left _ _)`. Conclude with `WithTop.coe_le_coe.2 (le_max_right _ _)`. Consider the case `mul_X p i hp`. Take `⟨a, ha⟩` from `exists_real_le (v (MvPolynomial.eval x p))`.

Take `⟨b, hb⟩` from `exists_real_le (v (x i))`. Take `⟨r, hr⟩` from `hp (s - b)`. Use `⟨max r (max (s - a) b), fun x' hx' => ?_⟩` and prove the remaining obligations. Establish `h1` using `hr x' fun j => le_trans (WithTop.coe_le_coe.2 (le_max_left _ _)) (hx' j)`. Establish `h2` using `hx' i`.

Establish `e : MvPolynomial.eval x (p * MvPolynomial.X i) - MvPolynomial.eval x' (p * MvPolynomial.X i) = MvPolynomial.eval x p * (x i - x' i) + ((MvPolynomial.eval x p - MvPolynomial.eval x' p) * x i + -((MvPolynomial.eval x p - MvPolynomial.eval x' p) * (x i - x' i)))`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `m1 : s - a ≤ max r (max (s - a) b)` using `le_trans (le_max_left _ _) (le_max_right _ _)`. Establish `m2 : b ≤ max r (max (s - a) b)` using `le_trans (le_max_right _ _) (le_max_right _ _)`.

Rewrite using `[e]`. Use `le_trans (le_min (le_val_mul v ha h2 (by linarith)) (le_trans (le_min (le_val_mul v h1 hb (by linarith)) ?_) (v.map_add _ _))) (v.map_add _ _)` and prove the remaining obligations. Rewrite using `[v.map_neg]`. Conclude with `le_val_mul v h1 h2 (by linarith)`.
-/
theorem eval_close {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (x : ι → C) (Q : MvPolynomial ι C) (s : ℝ) :
    ∃ r : ℝ, ∀ x' : ι → C, (∀ i, (r : WithTop ℝ) ≤ v (x i - x' i)) →
      (s : WithTop ℝ) ≤ v (MvPolynomial.eval x Q - MvPolynomial.eval x' Q) := by
  induction Q using MvPolynomial.induction_on generalizing s with
  | C a => exact ⟨0, fun x' _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨r₁, h₁⟩ := hp s
    obtain ⟨r₂, h₂⟩ := hq s
    refine ⟨max r₁ r₂, fun x' hx' => ?_⟩
    have e : MvPolynomial.eval x (p + q) - MvPolynomial.eval x' (p + q) =
        (MvPolynomial.eval x p - MvPolynomial.eval x' p) +
          (MvPolynomial.eval x q - MvPolynomial.eval x' q) := by
      simp only [map_add]; ring
    rw [e]
    refine le_trans (le_min (h₁ x' fun i => le_trans ?_ (hx' i))
      (h₂ x' fun i => le_trans ?_ (hx' i))) (v.map_add _ _)
    · exact WithTop.coe_le_coe.2 (le_max_left _ _)
    · exact WithTop.coe_le_coe.2 (le_max_right _ _)
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := exists_real_le (v (MvPolynomial.eval x p))
    obtain ⟨b, hb⟩ := exists_real_le (v (x i))
    obtain ⟨r, hr⟩ := hp (s - b)
    refine ⟨max r (max (s - a) b), fun x' hx' => ?_⟩
    have h1 := hr x' fun j => le_trans (WithTop.coe_le_coe.2 (le_max_left _ _)) (hx' j)
    have h2 := hx' i
    have e : MvPolynomial.eval x (p * MvPolynomial.X i) - MvPolynomial.eval x' (p * MvPolynomial.X i)
        = MvPolynomial.eval x p * (x i - x' i) +
          ((MvPolynomial.eval x p - MvPolynomial.eval x' p) * x i +
            -((MvPolynomial.eval x p - MvPolynomial.eval x' p) * (x i - x' i))) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    have m1 : s - a ≤ max r (max (s - a) b) := le_trans (le_max_left _ _) (le_max_right _ _)
    have m2 : b ≤ max r (max (s - a) b) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [e]
    refine le_trans (le_min (le_val_mul v ha h2 (by linarith))
      (le_trans (le_min (le_val_mul v h1 hb (by linarith)) ?_) (v.map_add _ _))) (v.map_add _ _)
    rw [v.map_neg]
    exact le_val_mul v h1 h2 (by linarith)

/- English proof (translation)
Set `ι : C →+* MvPolynomial (Fin d × Fin d) C` to `MvPolynomial.C`. Set `L : Fin d → MvPowerSeries (Fin d) (MvPolynomial (Fin d × Fin d) C)` to `fun a => ∑ b, MvPowerSeries.C (MvPolynomial.X (a, b)) * map ι (l b)`. Establish `hL : HasSubst L` using `hasSubst_of_constantCoeff_zero fun a => by`. Simplify using `[L, hl]`. Use `⟨coeff α (subst L (map ι f)), fun A => ?_⟩` and prove the remaining obligations.

Establish `hm : ∀ g : MvPowerSeries (Fin d) C, map (MvPolynomial.eval fun p : Fin d × Fin d => A p.1 p.2) (map ι g) = g`. Introduce `g`. Use extensionality with `β`. Simplify using `[ι]`. Rewrite using `[← coeff_map, map_subst hL, hm]`.

Use `congr 2`. Use function extensionality and compare the values at `a`. Simplify using `only [L, map_sum, map_mul, hm, map_C, MvPolynomial.eval_X, smul_eq_C_mul]`.
-/
theorem exists_poly_coeff {C : Type} [Field C] {d : ℕ} (l : Fin d → MvPowerSeries (Fin d) C)
    (hl : ∀ a, constantCoeff (l a) = 0) (f : MvPowerSeries (Fin d) C) (α : Fin d →₀ ℕ) :
    ∃ Q : MvPolynomial (Fin d × Fin d) C, ∀ A : Matrix (Fin d) (Fin d) C,
      coeff α (subst (fun a => ∑ b, A a b • l b) f) =
        MvPolynomial.eval (fun p => A p.1 p.2) Q := by
  let ι : C →+* MvPolynomial (Fin d × Fin d) C := MvPolynomial.C
  let L : Fin d → MvPowerSeries (Fin d) (MvPolynomial (Fin d × Fin d) C) :=
    fun a => ∑ b, MvPowerSeries.C (MvPolynomial.X (a, b)) * map ι (l b)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero fun a => by
    simp [L, hl]
  refine ⟨coeff α (subst L (map ι f)), fun A => ?_⟩
  have hm : ∀ g : MvPowerSeries (Fin d) C,
      map (MvPolynomial.eval fun p : Fin d × Fin d => A p.1 p.2) (map ι g) = g := by
    intro g; ext β; simp [ι]
  rw [← coeff_map, map_subst hL, hm]
  congr 2
  funext a
  simp only [L, map_sum, map_mul, hm, map_C, MvPolynomial.eval_X, smul_eq_C_mul]

/- English proof (translation)
Introduce `C _ _ v d G A hA`. Take `⟨ex, ⟨hex0, hr, hl⟩, -⟩` from `GlobalTheory.FormalInv.formal_inverse_function_theorem.1 C d G.lg G.lg_const (by`. Establish `: (Matrix.of fun i j => coeff (Finsupp.single j 1) (G.lg i) : Matrix (Fin d) (Fin d) C) = 1`. Use extensionality with `i j`. Simplify using `[G.lg_lin, Matrix.one_apply]`.

Rewrite using `[this]`. Conclude with `isUnit_one)`. Establish `hex : HasSubst ex` using `hasSubst_of_constantCoeff_zero hex0`. Establish `hlg : HasSubst G.lg` using `hasSubst_of_constantCoeff_zero G.lg_const`. Establish `h0 : ∀ a, constantCoeff (∑ b, A a b • G.lg b) = 0` using `fun a => by`.

Simplify using `[G.lg_const]`. Establish `hs : HasSubst fun a => ∑ b, A a b • G.lg b` using `hasSubst_of_constantCoeff_zero h0`. Use `⟨fun a => subst (fun a => ∑ b, A a b • G.lg b) (ex a), fun a α => ?_, fun a => constantCoeff_subst_eq_zero hs h0 (hex0 a), fun a => ?_⟩` and prove the remaining obligations. Take `⟨Q, hQ⟩` from `exists_poly_coeff G.lg G.lg_const (ex a) α`. Take `⟨r, hr'⟩` from `eval_close v (fun p : Fin d × Fin d => A p.1 p.2) Q 0`.

Take `⟨A', hA', φ, hφi, hφ0, hφ⟩` from `hA r`. Establish `hφs : HasSubst φ` using `hasSubst_of_constantCoeff_zero hφ0`. Establish `e : subst (fun a => ∑ b, A' a b • G.lg b) (ex a) = φ a`. Rewrite using `[← funext hφ, ← subst_comp_subst_apply hlg hφs, hl, subst_X hφs]`. Establish `h1` using `hr' (fun p => A' p.1 p.2) fun p => hA' p.1 p.2`.

Establish `h2 : (0 : WithTop ℝ) ≤ v (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)`. Rewrite using `[← hQ, e]`. Conclude with `hφi a α`. Use `show 0 ≤ v _`. Rewrite using `[hQ, ← sub_add_cancel (MvPolynomial.eval (fun p : Fin d × Fin d => A p.1 p.2) Q) (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)]`.

Conclude with `le_trans (le_min h1 h2) (v.map_add _ _)`. Rewrite using `[← subst_comp_subst_apply hex hs, hr, subst_X hs]`.
-/
theorem integral_of_limit :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d) (A : Matrix (Fin d) (Fin d) C),
    (∀ r : ℝ, ∃ A' : Matrix (Fin d) (Fin d) C, (∀ a b, (r : WithTop ℝ) ≤ v (A a b - A' a b)) ∧ ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A' a b • G.lg b) →
    ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A a b • G.lg b) := by
  intro C _ _ v d G A hA
  obtain ⟨ex, ⟨hex0, hr, hl⟩, -⟩ := GlobalTheory.FormalInv.formal_inverse_function_theorem.1 C d G.lg
    G.lg_const (by
      have : (Matrix.of fun i j => coeff (Finsupp.single j 1) (G.lg i) :
          Matrix (Fin d) (Fin d) C) = 1 := by
        ext i j; simp [G.lg_lin, Matrix.one_apply]
      rw [this]; exact isUnit_one)
  have hex : HasSubst ex := hasSubst_of_constantCoeff_zero hex0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have h0 : ∀ a, constantCoeff (∑ b, A a b • G.lg b) = 0 := fun a => by
    simp [G.lg_const]
  have hs : HasSubst fun a => ∑ b, A a b • G.lg b := hasSubst_of_constantCoeff_zero h0
  refine ⟨fun a => subst (fun a => ∑ b, A a b • G.lg b) (ex a), fun a α => ?_,
    fun a => constantCoeff_subst_eq_zero hs h0 (hex0 a), fun a => ?_⟩
  · obtain ⟨Q, hQ⟩ := exists_poly_coeff G.lg G.lg_const (ex a) α
    obtain ⟨r, hr'⟩ := eval_close v (fun p : Fin d × Fin d => A p.1 p.2) Q 0
    obtain ⟨A', hA', φ, hφi, hφ0, hφ⟩ := hA r
    have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
    have e : subst (fun a => ∑ b, A' a b • G.lg b) (ex a) = φ a := by
      rw [← funext hφ, ← subst_comp_subst_apply hlg hφs, hl, subst_X hφs]
    have h1 := hr' (fun p => A' p.1 p.2) fun p => hA' p.1 p.2
    have h2 : (0 : WithTop ℝ) ≤ v (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q) := by
      rw [← hQ, e]; exact hφi a α
    show 0 ≤ v _
    rw [hQ, ← sub_add_cancel (MvPolynomial.eval (fun p : Fin d × Fin d => A p.1 p.2) Q)
      (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)]
    exact le_trans (le_min h1 h2) (v.map_add _ _)
  · rw [← subst_comp_subst_apply hex hs, hr, subst_X hs]

end GlobalTheory.IntegralEndLimit
