import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriShear

open MeasureTheory Matrix

noncomputable section

namespace PI.AmpRootJacW

variable {n : ℕ}

def SUp (V : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j : Fin n, j.val ≤ i.val → V i j = 0

/- English proof (translation)
Introduce `i j h`. Simplify using `[hV i j h]`.
-/
theorem sUp_neg {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : SUp (-V) := by
  intro i j h
  simp [hV i j h]

/- English proof (translation)
The claim follows from `| 0, i, j, h => by rw [pow_zero, Matrix.one_apply, if_neg] rintro rfl; omega | m + 1, i, j, h => by rw [pow_succ, Matrix.mul_apply] refine Finset.sum_eq_zero fun l _ => ?_ by_cases hl : l.val < i.val + m · rw [sUp_pow hV m i l hl, zero_mul] · rw [hV l j (by omega), mul_zero]`.
-/
theorem sUp_pow {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) :
    ∀ (m : ℕ) (i j : Fin n), j.val < i.val + m → (V ^ m) i j = 0
  | 0, i, j, h => by
    rw [pow_zero, Matrix.one_apply, if_neg]
    rintro rfl; omega
  | m + 1, i, j, h => by
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < i.val + m
    · rw [sUp_pow hV m i l hl, zero_mul]
    · rw [hV l j (by omega), mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Establish `hj` using `j.2`. Simplify using `only [Matrix.zero_apply]`. Conclude with `sUp_pow hV m i j (by omega)`.
-/
theorem sUp_pow_eq_zero {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (m : ℕ) (hm : n ≤ m) : V ^ m = 0 := by
  ext i j
  have hj := j.2
  simp only [Matrix.zero_apply]
  exact sUp_pow hV m i j (by omega)

def gInv (V : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ m ∈ Finset.range (n + 2), (-V) ^ m

/- English proof (translation)
Unfold `gInv`. Establish `h` using `mul_neg_geom_sum (-V) (n + 2)`. Rewrite `h` using `[sub_neg_eq_add]`. Rewrite using `[h, sUp_pow_eq_zero (sUp_neg hV) (n + 2) (by omega), sub_zero]`.
-/
theorem mul_gInv {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : (1 + V) * gInv V = 1 := by
  unfold gInv
  have h := mul_neg_geom_sum (-V) (n + 2)
  rw [sub_neg_eq_add] at h
  rw [h, sUp_pow_eq_zero (sUp_neg hV) (n + 2) (by omega), sub_zero]

/- English proof (translation)
The claim follows from `| 0, i, j, hij => by rw [pow_one, pow_one]; exact h i j hij | m + 1, i, j, hij => by rw [pow_succ' V (m + 1), pow_succ' V' (m + 1), Matrix.mul_apply, Matrix.mul_apply] refine Finset.sum_congr rfl fun l _ => ?_ by_cases h1 : l.val ≤ i.val · rw [hV i l h1, hV' i l h1, zero_mul, zer …`.
-/
theorem pow_agree {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (d : ℕ)
    (h : ∀ a b : Fin n, b.val ≤ a.val + d → V a b = V' a b) :
    ∀ (m : ℕ) (i j : Fin n), j.val ≤ i.val + d → (V ^ (m + 1)) i j = (V' ^ (m + 1)) i j
  | 0, i, j, hij => by rw [pow_one, pow_one]; exact h i j hij
  | m + 1, i, j, hij => by
    rw [pow_succ' V (m + 1), pow_succ' V' (m + 1), Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : l.val ≤ i.val
    · rw [hV i l h1, hV' i l h1, zero_mul, zero_mul]
    by_cases h2 : j.val ≤ l.val
    · rw [sUp_pow hV (m + 1) l j (by omega), sUp_pow hV' (m + 1) l j (by omega), mul_zero, mul_zero]
    rw [h i l (by omega), pow_agree hV hV' d h m l j (by omega)]

/- English proof (translation)
Rewrite using `[pow_succ, pow_succ V', Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hk : k.val < i.val + (m + 1)`. Rewrite using `[sUp_pow hV (m + 1) i k hk, sUp_pow hV' (m + 1) i k hk, zero_mul, zero_mul]`. Distinguish the cases in `hjk : j.val ≤ k.val`.

Rewrite using `[hV k j hjk, hV' k j hjk, mul_zero, mul_zero]`. Establish `h' : ∀ a b : Fin n, b.val ≤ a.val + (g - 1) → V a b = V' a b` using `fun a b hab => h a b (by omega)`. Rewrite using `[pow_agree hV hV' (g - 1) h' m i k (by omega), h k j (by omega)]`.
-/
theorem pow_apply_eq_of_agree {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (g : ℕ)
    (h : ∀ a b : Fin n, b.val < a.val + g → V a b = V' a b) (m : ℕ) (i j : Fin n)
    (hij : j.val ≤ i.val + g) : (V ^ (m + 1 + 1)) i j = (V' ^ (m + 1 + 1)) i j := by
  rw [pow_succ, pow_succ V', Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k.val < i.val + (m + 1)
  · rw [sUp_pow hV (m + 1) i k hk, sUp_pow hV' (m + 1) i k hk, zero_mul, zero_mul]
  · by_cases hjk : j.val ≤ k.val
    · rw [hV k j hjk, hV' k j hjk, mul_zero, mul_zero]
    · have h' : ∀ a b : Fin n, b.val ≤ a.val + (g - 1) → V a b = V' a b := fun a b hab => h a b (by omega)
      rw [pow_agree hV hV' (g - 1) h' m i k (by omega), h k j (by omega)]

section Pat

variable (S : Finset (Fin n × Fin n))

def vM (v : S → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => if h : (i, j) ∈ S then v ⟨(i, j), h⟩ else 0

/- English proof (translation)
Unfold `vM`. Rewrite using `[dif_pos q.2]`.
-/
theorem vM_at (v : S → ℂ) (q : S) : vM S v q.1.1 q.1.2 = v q := by
  unfold vM
  rw [dif_pos q.2]

/- English proof (translation)
Introduce `i j hji`. Unfold `vM`. Rewrite using `[dif_neg]`. Introduce `hm`. Establish `h1 : i < j` using `hS _ hm`.

Rewrite `h1` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sUp_vM (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) : SUp (vM S v) := by
  intro i j hji
  unfold vM
  rw [dif_neg]
  intro hm
  have h1 : i < j := hS _ hm
  rw [Fin.lt_def] at h1
  omega

/- English proof (translation)
Unfold `vM`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `continuous_apply _`. Conclude with `continuous_const`.
-/
theorem continuous_vM : Continuous (vM S) := by
  unfold vM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

def invC (v : S → ℂ) : S → ℂ := fun q => gInv (vM S v) q.1.1 q.1.2

def rk (q : S) : ℕ := q.1.2.val - q.1.1.val

def hSh (q : S) (v : S → ℂ) : ℂ :=
  -(∑ m ∈ Finset.range n, ((-vM S v) ^ (m + 1 + 1)) q.1.1 q.1.2)

/- English proof (translation)
Unfold `invC gInv hSh`. Rewrite using `[Matrix.sum_apply, Finset.sum_range_succ', Finset.sum_range_succ']`. Establish `hq : q.1.1 ≠ q.1.2` using `ne_of_lt (hS q.1 q.2)`. Simplify using `only [pow_zero, zero_add, pow_one, add_zero, Matrix.one_apply_ne hq, Matrix.neg_apply, vM_at]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem invC_eq (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) (q : S) : invC S v q = -(v q + hSh S q v) := by
  unfold invC gInv hSh
  rw [Matrix.sum_apply, Finset.sum_range_succ', Finset.sum_range_succ']
  have hq : q.1.1 ≠ q.1.2 := ne_of_lt (hS q.1 q.2)
  simp only [pow_zero, zero_add, pow_one, add_zero, Matrix.one_apply_ne hq, Matrix.neg_apply, vM_at]
  ring

/- English proof (translation)
Unfold `hSh`. Use `congr 1`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Establish `hq : q.1.1 < q.1.2` using `hS q.1 q.2`. Rewrite `hq` using `[Fin.lt_def]`.

Establish `hr : rk S q = q.1.2.val - q.1.1.val` using `rfl`. Use `pow_apply_eq_of_agree (sUp_neg (sUp_vM S hS v)) (sUp_neg (sUp_vM S hS w)) (rk S q) ?_ m q.1.1 q.1.2 ?_` and prove the remaining obligations. Introduce `a b hab`. Simplify using `only [Matrix.neg_apply, vM]`. Use `split_ifs with hm`.

Rewrite using `[h ⟨(a, b), hm⟩ ?_] show b.val - a.val < rk S q`. Rewrite `hab`, the goal using `[hr]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Rewrite using `[hr]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem hSh_dep (hS : ∀ q ∈ S, q.1 < q.2) (q : S) (v w : S → ℂ) (h : ∀ p, rk S p < rk S q → v p = w p) :
    hSh S q v = hSh S q w := by
  unfold hSh
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hq : q.1.1 < q.1.2 := hS q.1 q.2
  rw [Fin.lt_def] at hq
  have hr : rk S q = q.1.2.val - q.1.1.val := rfl
  refine pow_apply_eq_of_agree (sUp_neg (sUp_vM S hS v)) (sUp_neg (sUp_vM S hS w)) (rk S q) ?_ m q.1.1 q.1.2 ?_
  · intro a b hab
    simp only [Matrix.neg_apply, vM]
    split_ifs with hm
    · rw [h ⟨(a, b), hm⟩ ?_]
      show b.val - a.val < rk S q
      rw [hr] at hab ⊢
      omega
    · rfl
  · rw [hr]
    omega

/- English proof (translation)
Unfold `hSh`. Use `Continuous.neg (continuous_finset_sum _ (fun m _ => ?_))` and prove the remaining obligations. Establish `h1 : Continuous (fun v : S → ℂ => (-vM S v) ^ (m + 1 + 1))` using `((continuous_vM S).neg).pow _`. Conclude with `h1.matrix_elem q.1.1 q.1.2`.
-/
theorem continuous_hSh (q : S) : Continuous (hSh S q) := by
  unfold hSh
  refine Continuous.neg (continuous_finset_sum _ (fun m _ => ?_))
  have h1 : Continuous (fun v : S → ℂ => (-vM S v) ^ (m + 1 + 1)) := ((continuous_vM S).neg).pow _
  exact h1.matrix_elem q.1.1 q.1.2

/- English proof (translation)
Conclude with `PI.AmpRootCommon.Tri.measurePreserving_of_card (Fintype.card S) S rfl (rk S) (fun q v => hSh S q v) (fun q => (continuous_hSh S q).measurable) (fun q x y hxy => hSh_dep S hS q x y hxy)`.
-/
theorem shear_mp (hS : ∀ q ∈ S, q.1 < q.2) :
    MeasurePreserving (fun v : S → ℂ => fun q => v q + hSh S q v) volume volume := by
  exact PI.AmpRootCommon.Tri.measurePreserving_of_card (Fintype.card S) S rfl (rk S) (fun q v => hSh S q v)
    (fun q => (continuous_hSh S q).measurable) (fun q x y hxy => hSh_dep S hS q x y hxy)

end Pat

/- English proof (translation)
Establish `h` using `MeasureTheory.volume_preserving_arrowCongr' τ.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `(funext w i; simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr'])`.
-/
theorem mp_reindex {ι : Type} [Fintype ι] (τ : ι ≃ ι) :
    MeasurePreserving (fun (w : ι → ℂ) i => w (τ i)) volume volume := by
  have h := MeasureTheory.volume_preserving_arrowCongr' τ.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)
  convert h using 1
  all_goals first
    | rfl
    | (funext w i; simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr'])

/- English proof (translation)
Set `u : Circle` to `⟨c, by simp [Submonoid.unitSphere, hc]⟩`. Establish `h` using `((Complex.conjLIE).trans (rotation u)).measurePreserving`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`.

Consider the case `(funext x; simp only [LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply]; rfl)`.
-/
theorem mp_unitConj1 (c : ℂ) (hc : ‖c‖ = 1) : MeasurePreserving (fun x : ℂ => c * star x) volume volume := by
  let u : Circle := ⟨c, by simp [Submonoid.unitSphere, hc]⟩
  have h := ((Complex.conjLIE).trans (rotation u)).measurePreserving
  convert h using 1
  all_goals first
    | rfl
    | (funext x; simp only [LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply]; rfl)

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun (x : ι → ℂ) i => c i * star (x i)) volume volume` using `MeasureTheory.volume_preserving_pi (fun i => mp_unitConj1 (c i) (hc i))`. Conclude with `h1.comp (mp_reindex τ)`.
-/
theorem mp_unitConj {ι : Type} [Fintype ι] (τ : ι ≃ ι) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    MeasurePreserving (fun (w : ι → ℂ) i => c i * star (w (τ i))) volume volume := by
  have h1 : MeasurePreserving (fun (x : ι → ℂ) i => c i * star (x i)) volume volume :=
    MeasureTheory.volume_preserving_pi (fun i => mp_unitConj1 (c i) (hc i))
  exact h1.comp (mp_reindex τ)

/- English proof (translation)
Establish `h1` using `mp_unitConj τ (fun q => -c q) (fun q => by rw [norm_neg]; exact hc q)`. Establish `h2` using `shear_mp S hS`. Use `h1.comp h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v q`. Simplify using `only [Function.comp_apply, invC_eq S hS v (τ q), star_neg, star_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_mp (S : Finset (Fin n × Fin n)) (hS : ∀ q ∈ S, q.1 < q.2) (τ : S ≃ S) (c : S → ℂ)
    (hc : ∀ q, ‖c q‖ = 1) :
    MeasurePreserving (fun (v : S → ℂ) q => c q * star (invC S v (τ q))) volume volume := by
  have h1 := mp_unitConj τ (fun q => -c q) (fun q => by rw [norm_neg]; exact hc q)
  have h2 := shear_mp S hS
  convert h1.comp h2 using 1
  funext v q
  simp only [Function.comp_apply, invC_eq S hS v (τ q), star_neg, star_add]
  ring

end PI.AmpRootJacW
