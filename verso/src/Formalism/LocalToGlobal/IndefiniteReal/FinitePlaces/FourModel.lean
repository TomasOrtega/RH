import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulSubMulLe

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

def IsSB (L X : AddSubgroup W) (Φ : W → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → t ∈ X) ∧ ∃ k : ℕ, 0 < k ∧ (∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → k • t ∈ L

section Defs

variable (ρ : W → Module.End ℂ V) (χ : W → W → ℂ) (L X Y : AddSubgroup W) (f₀ : V)

def coef (Φ : W → ℂ) (a y : W) : ℂ := integ (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)

def term (Φ : W → ℂ) (a y : W) : V := coef χ L X Φ a y • ρ (-a) (ρ y f₀)

abbrev QX : Type _ := W ⧸ (L ⊓ X)

abbrev QY : Type _ := W ⧸ (L ⊓ Y)

open Classical in

def tfun (Φ : W → ℂ) : V :=
  ∑ᶠ q : QX L X × QY L Y, if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0

end Defs

section Chi

variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)

include hχl hχ0 in
/- English proof (translation)
Establish `h` using `hχl 0 0 y`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 0 y) (by rw [mul_one, ← h])`.
-/
theorem chi_zero_left (y : W) : χ 0 y = 1 := by
  have h := hχl 0 0 y
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 0 y) (by rw [mul_one, ← h])

include hχr hχ0 in
/- English proof (translation)
Establish `h` using `hχr t 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 t 0) (by rw [mul_one, ← h])`.
-/
theorem chi_zero_right (t : W) : χ t 0 = 1 := by
  have h := hχr t 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 t 0) (by rw [mul_one, ← h])

include hχl hχ0 in
/- English proof (translation)
Establish `h : χ t y * χ (-t) y = 1`. Rewrite using `[← hχl, add_neg_cancel, chi_zero_left hχl hχ0]`. Conclude with `eq_inv_of_mul_eq_one_right h`.
-/
theorem chi_neg_left (t y : W) : χ (-t) y = (χ t y)⁻¹ := by
  have h : χ t y * χ (-t) y = 1 := by
    rw [← hχl, add_neg_cancel, chi_zero_left hχl hχ0]
  exact eq_inv_of_mul_eq_one_right h

include hχl hχ0 in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_smul, chi_zero_left hχl hχ0, pow_zero]`. Consider the case `succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]`.
-/
theorem chi_nsmul_left (k : ℕ) (t y : W) : χ (k • t) y = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_left hχl hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]

include hχr hχ0 in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_smul, chi_zero_right hχr hχ0, pow_zero]`. Consider the case `succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]`.
-/
theorem chi_nsmul_right (k : ℕ) (t y : W) : χ t (k • y) = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_right hχr hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]

end Chi

section Rep

variable {L X Y : AddSubgroup W}

/- English proof (translation)
Use `⟨-a + (QuotientAddGroup.mk a : QX L X).out, ?_, (add_neg_cancel_left a _).symm⟩` and prove the remaining obligations. Establish `h : (QuotientAddGroup.mk (QuotientAddGroup.mk a : QX L X).out : QX L X) = QuotientAddGroup.mk a` using `QuotientAddGroup.out_eq' _`. Conclude with `QuotientAddGroup.eq.mp h.symm`.
-/
theorem QX_out (a : W) : ∃ l ∈ L ⊓ X, (QuotientAddGroup.mk a : QX L X).out = a + l := by
  refine ⟨-a + (QuotientAddGroup.mk a : QX L X).out, ?_, (add_neg_cancel_left a _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk a : QX L X).out : QX L X) = QuotientAddGroup.mk a :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm

/- English proof (translation)
Use `⟨-y + (QuotientAddGroup.mk y : QY L Y).out, ?_, (add_neg_cancel_left y _).symm⟩` and prove the remaining obligations. Establish `h : (QuotientAddGroup.mk (QuotientAddGroup.mk y : QY L Y).out : QY L Y) = QuotientAddGroup.mk y` using `QuotientAddGroup.out_eq' _`. Conclude with `QuotientAddGroup.eq.mp h.symm`.
-/
theorem QY_out (y : W) : ∃ μ ∈ L ⊓ Y, (QuotientAddGroup.mk y : QY L Y).out = y + μ := by
  refine ⟨-y + (QuotientAddGroup.mk y : QY L Y).out, ?_, (add_neg_cancel_left y _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk y : QY L Y).out : QY L Y) = QuotientAddGroup.mk y :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm

end Rep

section Coef

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y) (hχ0 : ∀ t y, χ t y ≠ 0)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X)))

include hχl hχ0 hfinX in
/- English proof (translation)
Establish `hc` using `hχ0 l y`. Establish `hH : ∀ t, Φ (a + l + t) * (χ t y)⁻¹ = χ l y * (Φ (a + (t + l)) * (χ (t + l) y)⁻¹)`. Introduce `t`. Establish `e : (χ t y)⁻¹ = χ l y * (χ (t + l) y)⁻¹`. Rewrite using `[hχl, mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]`.

Rewrite using `[e, add_comm t l, ← add_assoc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hiff : ∀ k, IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) ↔ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)`. Introduce `k`. Unfold `IsInv`.

Simplify using `only [hH]`. Prove the components needed by the constructor for the conclusion. Introduce `h t ht u hu`. Use `h (t - l) (sub_mem ht hl) u hu` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, show t - l + k • u + l = t + k • u by abel]`.

Conclude with `mul_left_cancel₀ hc this`. Introduce `h t ht u hu`. Rewrite using `[show t + k • u + l = (t + l) + k • u by abel, h (t + l) (add_mem ht hl) u hu]`. Unfold `coef`. Distinguish the cases in `h0 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)`.

Take `⟨k, hk, hinv⟩` from `h0`. Establish `hinv1` using `(hiff k).mpr hinv`. Establish `hinvs : IsInv k (L ⊓ X) (fun t => Φ (a + (t + l)) * (χ (t + l) y)⁻¹)`. Introduce `t ht u hu`. Use `beta_reduce`.

Rewrite using `[show t + k • u + l = (t + l) + k • u by abel]`. Conclude with `hinv (t + l) (add_mem ht hl) u hu`. Rewrite using `[integ_eq hfinX hk hinv1, ← integ_shift hfinX hk hinv hl, integ_eq hfinX hk hinvs]`. Unfold `avg`. Use `haveI := hfinX k hk`.

Simplify using `only [hH]`. Rewrite using `[← mul_finsum]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹)` using `fun ⟨k, hk, hi⟩ => h0 ⟨k, hk, (hiff k).mp hi⟩`. Unfold `integ`.

Rewrite using `[dif_neg h1, dif_neg h0, mul_zero]`.
-/
theorem coef_add_left (Φ : W → ℂ) (a y : W) {l : W} (hl : l ∈ L ⊓ X) :
    coef χ L X Φ (a + l) y = χ l y * coef χ L X Φ a y := by
  have hc := hχ0 l y
  have hH : ∀ t, Φ (a + l + t) * (χ t y)⁻¹ = χ l y * (Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
    intro t
    have e : (χ t y)⁻¹ = χ l y * (χ (t + l) y)⁻¹ := by
      rw [hχl, mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]
    rw [e, add_comm t l, ← add_assoc]
    ring
  have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) ↔
      IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
    intro k
    unfold IsInv
    simp only [hH]
    constructor
    · intro h t ht u hu
      have := h (t - l) (sub_mem ht hl) u hu
      rw [sub_add_cancel, show t - l + k • u + l = t + k • u by abel] at this
      exact mul_left_cancel₀ hc this
    · intro h t ht u hu
      rw [show t + k • u + l = (t + l) + k • u by abel, h (t + l) (add_mem ht hl) u hu]
  unfold coef
  by_cases h0 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)
  · obtain ⟨k, hk, hinv⟩ := h0
    have hinv1 := (hiff k).mpr hinv
    have hinvs : IsInv k (L ⊓ X) (fun t => Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
      intro t ht u hu
      beta_reduce
      rw [show t + k • u + l = (t + l) + k • u by abel]
      exact hinv (t + l) (add_mem ht hl) u hu
    rw [integ_eq hfinX hk hinv1, ← integ_shift hfinX hk hinv hl, integ_eq hfinX hk hinvs]
    unfold avg
    haveI := hfinX k hk
    simp only [hH]
    rw [← mul_finsum]
    ring
  · have h1 : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) :=
      fun ⟨k, hk, hi⟩ => h0 ⟨k, hk, (hiff k).mp hi⟩
    unfold integ
    rw [dif_neg h1, dif_neg h0, mul_zero]

include hfinX in
/- English proof (translation)
Unfold `coef`. Apply `integ_congr hfinX` to reduce the goal to its premises. Introduce `t ht`. Rewrite using `[hχr, hLL t ht μ hμ, mul_one]`.
-/
theorem coef_add_right (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (Φ : W → ℂ) (a y : W) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    coef χ L X Φ a (y + μ) = coef χ L X Φ a y := by
  unfold coef
  apply integ_congr hfinX
  intro t ht
  rw [hχr, hLL t ht μ hμ, mul_one]

include hfinX in
/- English proof (translation)
Establish `h0 : ∀ t ∈ L ⊓ X, Φ (a + t) * (χ t y)⁻¹ = (fun _ : W => (0 : ℂ)) t`. Introduce `t ht`. Establish `hz : Φ (a + t) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `ha (by simpa using X.sub_mem (hΦ _ hne) (AddSubgroup.mem_inf.mp ht).2)`.

Simplify using `[hz]`. Unfold `coef`. Rewrite using `[integ_congr hfinX h0]`. Unfold `integ`. Use `split_ifs with h`.

Simplify using `[avg]`. Both sides reduce to the same expression.
-/
theorem coef_eq_zero (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) {a : W} (ha : a ∉ X) (y : W) :
    coef χ L X Φ a y = 0 := by
  have h0 : ∀ t ∈ L ⊓ X, Φ (a + t) * (χ t y)⁻¹ = (fun _ : W => (0 : ℂ)) t := by
    intro t ht
    have hz : Φ (a + t) = 0 := by
      by_contra hne
      exact ha (by simpa using X.sub_mem (hΦ _ hne) (AddSubgroup.mem_inf.mp ht).2)
    simp [hz]
  unfold coef
  rw [integ_congr hfinX h0]
  unfold integ
  split_ifs with h
  · simp [avg]
  · rfl

include hχl hχ0 hfinX in
/- English proof (translation)
Distinguish the cases in `ha : a ∈ X`. Establish `hl'` using `AddSubgroup.mem_inf.mp hl`. Establish `hnl : -l ∈ L ⊓ X` using `neg_mem hl`. Establish `key : ρ (-l) (ρ y f₀) = (χ l y)⁻¹ • ρ y f₀`. Establish `h1` using `congrArg (fun T => T f₀) (hXY (-l) (neg_mem hl'.2) y hy)`.

Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at h1`. Rewrite using `[h1, hfX (-l) hnl, chi_neg_left hχl hχ0]`. Unfold `term`. Rewrite using `[coef_add_left hχl hχ0 hfinX Φ a y hl, neg_add, hX (-a) (neg_mem ha) (-l) (neg_mem hl'.2), Module.End.mul_apply, key, map_smul, smul_smul, mul_comm (χ l y), mul_assoc, mul_inv_cancel₀ (hχ0 l y), mul_one]`. Establish `hal : a + l ∉ X` using `fun h => ha (by simpa using X.sub_mem h (AddSubgroup.mem_inf.mp hl).2)`.

Unfold `term`. Rewrite using `[coef_eq_zero hfinX Φ hΦ ha, coef_eq_zero hfinX Φ hΦ hal, zero_smul, zero_smul]`.
-/
theorem term_add_left (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x)) (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀)
    (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) (a : W) {y : W} (hy : y ∈ Y) {l : W} (hl : l ∈ L ⊓ X) :
    term ρ χ L X f₀ Φ (a + l) y = term ρ χ L X f₀ Φ a y := by
  by_cases ha : a ∈ X
  · have hl' := AddSubgroup.mem_inf.mp hl
    have hnl : -l ∈ L ⊓ X := neg_mem hl
    have key : ρ (-l) (ρ y f₀) = (χ l y)⁻¹ • ρ y f₀ := by
      have h1 := congrArg (fun T => T f₀) (hXY (-l) (neg_mem hl'.2) y hy)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1
      rw [h1, hfX (-l) hnl, chi_neg_left hχl hχ0]
    unfold term
    rw [coef_add_left hχl hχ0 hfinX Φ a y hl, neg_add, hX (-a) (neg_mem ha) (-l) (neg_mem hl'.2),
      Module.End.mul_apply, key, map_smul, smul_smul, mul_comm (χ l y), mul_assoc, mul_inv_cancel₀ (hχ0 l y), mul_one]
  · have hal : a + l ∉ X := fun h => ha (by simpa using X.sub_mem h (AddSubgroup.mem_inf.mp hl).2)
    unfold term
    rw [coef_eq_zero hfinX Φ hΦ ha, coef_eq_zero hfinX Φ hΦ hal, zero_smul, zero_smul]

include hfinX in
/- English proof (translation)
Unfold `term`. Rewrite using `[coef_add_right hfinX hχr hLL Φ a y hμ, hY y hy μ (AddSubgroup.mem_inf.mp hμ).2, Module.End.mul_apply, hfY μ hμ]`.
-/
theorem term_add_right (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
    (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀) (Φ : W → ℂ) (a : W) {y : W} (hy : y ∈ Y) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    term ρ χ L X f₀ Φ a (y + μ) = term ρ χ L X f₀ Φ a y := by
  unfold term
  rw [coef_add_right hfinX hχr hLL Φ a y hμ, hY y hy μ (AddSubgroup.mem_inf.mp hμ).2, Module.End.mul_apply,
    hfY μ hμ]

end Coef

end Formalism.IndefR.Fin.Four

end
