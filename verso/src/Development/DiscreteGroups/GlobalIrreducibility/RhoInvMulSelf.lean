import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.IsRowFixConj

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

/- English proof (translation)
Use `set z : Gn g (m + 1) := (cyc g (m + 1))⁻¹ * y with hzdef`. Establish `hz : ∀ l k, (z : Mt g (m + 1)) l k = (y : Mt g (m + 1)) (finRotate (m + 1) l) k` using `fun l k => by`. Rewrite using `[hzdef, Units.val_mul, cycinv_mul_apply]`. Use `set N : SIdx m → ZMod g := fun q => (z : Mt g (m + 1)) q.1.1 q.1.2 with hNdef`. Establish `hzU : ∀ l, l ≠ Fin.last m → ∀ k, (z : Mt g (m + 1)) l k = Um N l k`.

Introduce `l hl k`. Establish `hσ : ((finRotate (m + 1) l : Fin (m + 1)) : ℕ) = l + 1` using `coe_finRotate_of_ne_last hl`. Distinguish the cases in `hkl : k ≤ l`. Establish `hkl' : (k : ℕ) ≤ l` using `hkl`. Rewrite using `[hz, hy.2 k (finRotate (m + 1) l) (by rw [Fin.lt_def, hσ]; omega)]`.

Simplify using `only [Um, Matrix.of_apply]`. Distinguish the cases in `e : k = l`. Substitute `e` using the available equality. Rewrite using `[if_pos hσ, if_pos rfl]`. Establish `e' : l ≠ k` using `Ne.symm e`.

Establish `hlk : ¬ l < k` using `not_lt.2 hkl`. Establish `e2 : ¬ ((finRotate (m + 1) l : Fin (m + 1)) : ℕ) = (k : ℕ) + 1`. Rewrite using `[hσ]`. Introduce `h'`. Conclude with `e (Fin.ext (by omega))`.

Rewrite using `[if_neg e2, if_neg e', dif_neg hlk]`. Establish `hlk : l < k` using `not_le.1 hkl`. Simplify using `only [Um, Matrix.of_apply, if_neg (ne_of_lt hlk), dif_pos hlk, hNdef]`. Use `set U : Gn g (m + 1) := umGL N with hUdef`. Use `set h : Gn g (m + 1) := z * U⁻¹ with hhdef`.

Establish `hrow : ∀ l, l ≠ Fin.last m → ∀ k, (h : Mt g (m + 1)) l k = (1 : Mt g (m + 1)) l k`. Introduce `l hl k`. Rewrite using `[hhdef, Units.val_mul, Matrix.mul_apply]`. Repeatedly rewrite using `[hzU l hl]`. Rewrite using `[← Matrix.mul_apply, ← umGL_val, ← hUdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hUinv : (((U⁻¹ : Gn g (m + 1)) : Mt g (m + 1))).BlockTriangular id`. Rewrite using `[Matrix.coe_units_inv]`. Set `_` to `U.invertible`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular (um_upper N)`. Establish `hlast : ∀ k : Fin (m + 1), (k : ℕ) ≤ j → (h : Mt g (m + 1)) (Fin.last m) k = 0`.

Introduce `k hk`. Rewrite using `[hhdef, Units.val_mul, Matrix.mul_apply]`. Use `Finset.sum_eq_zero (fun a _ => ?_)` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) ≤ j`. Rewrite using `[hz, finRotate_last, hy.1 a ha, zero_mul]`.

Rewrite using `[hUinv (show k < a by rw [Fin.lt_def]; omega), mul_zero]`. Establish `hdet : (h : Mt g (m + 1)) (Fin.last m) (Fin.last m) ≠ 0`. Establish `hl : (h : Mt g (m + 1)).BlockTriangular OrderDual.toDual`. Introduce `a b hab`. Establish `hab' : a < b` using `hab`.

Establish `ha : a ≠ Fin.last m` using `ne_of_lt (lt_of_lt_of_le hab' (Fin.le_last b))`. Rewrite using `[hrow a ha, Matrix.one_apply_ne (ne_of_lt hab')]`. Establish `hd : (h : Mt g (m + 1)).det = (h : Mt g (m + 1)) (Fin.last m) (Fin.last m)`. Rewrite using `[Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_castSucc]`. Simplify using `[hrow _ (Fin.castSucc_lt_last _).ne]`.

Rewrite using `[← hd]`. Conclude with `IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit)`. Use `set t : (ZMod g)ˣ := Units.mk0 _ hdet with htdef`. Use `set w : WIdx m j → ZMod g := fun q => (h : Mt g (m + 1)) (Fin.last m) q.1 with hwdef`. Use `⟨(N, t, w), ?_⟩` and prove the remaining obligations.

Establish `hH : hpGL (rvec j t w) (by rw [rvec_last]; exact t.ne_zero) = h`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[hpGL_val]`. Simplify using `only [Hp, Matrix.of_apply]`.

Distinguish the cases in `ha : a = Fin.last m`. Substitute `ha` using the available equality. Rewrite using `[if_pos rfl]`. Simplify using `only [rvec]`. Distinguish the cases in `hb : b = Fin.last m`.

Substitute `hb` using the available equality. Simplify using `[htdef]`. Rewrite using `[if_neg hb] split_ifs with hb2`. Both sides reduce to the same expression. Establish `hbm : (b : ℕ) ≠ m` using `fun e => hb (Fin.ext (by simp [e]))`.

Use `b.2` as an intermediate fact. Establish `hbj : (b : ℕ) ≤ j`. Assume the negation of the conclusion as `hc`. Conclude with `hb2 ⟨by omega, by omega⟩`. Conclude with `(hlast b hbj).symm`.

Rewrite using `[if_neg ha, hrow a ha]`. Use `show cyc g (m + 1) * hpGL (rvec j t w) _ * umGL N = y`. Rewrite using `[hH, hhdef, hzdef, ← hUdef]`. Use `group`.
-/
theorem phi_surj {j : ℕ} (_hj : j < m) (y : Gn g (m + 1)) (hy : IsY j (y : Mt g (m + 1))) :
    ∃ p, phi j p = y := by
  set z : Gn g (m + 1) := (cyc g (m + 1))⁻¹ * y with hzdef
  have hz : ∀ l k, (z : Mt g (m + 1)) l k = (y : Mt g (m + 1)) (finRotate (m + 1) l) k := fun l k => by
    rw [hzdef, Units.val_mul, cycinv_mul_apply]
  set N : SIdx m → ZMod g := fun q => (z : Mt g (m + 1)) q.1.1 q.1.2 with hNdef
  have hzU : ∀ l, l ≠ Fin.last m → ∀ k, (z : Mt g (m + 1)) l k = Um N l k := by
    intro l hl k
    have hσ : ((finRotate (m + 1) l : Fin (m + 1)) : ℕ) = l + 1 := coe_finRotate_of_ne_last hl
    by_cases hkl : k ≤ l
    · have hkl' : (k : ℕ) ≤ l := hkl
      rw [hz, hy.2 k (finRotate (m + 1) l) (by rw [Fin.lt_def, hσ]; omega)]
      simp only [Um, Matrix.of_apply]
      by_cases e : k = l
      · subst e
        rw [if_pos hσ, if_pos rfl]
      · have e' : l ≠ k := Ne.symm e
        have hlk : ¬ l < k := not_lt.2 hkl
        have e2 : ¬ ((finRotate (m + 1) l : Fin (m + 1)) : ℕ) = (k : ℕ) + 1 := by
          rw [hσ]
          intro h'
          exact e (Fin.ext (by omega))
        rw [if_neg e2, if_neg e', dif_neg hlk]
    · have hlk : l < k := not_le.1 hkl
      simp only [Um, Matrix.of_apply, if_neg (ne_of_lt hlk), dif_pos hlk, hNdef]
  set U : Gn g (m + 1) := umGL N with hUdef
  set h : Gn g (m + 1) := z * U⁻¹ with hhdef
  have hrow : ∀ l, l ≠ Fin.last m → ∀ k, (h : Mt g (m + 1)) l k = (1 : Mt g (m + 1)) l k := by
    intro l hl k
    rw [hhdef, Units.val_mul, Matrix.mul_apply]
    simp_rw [hzU l hl]
    rw [← Matrix.mul_apply, ← umGL_val, ← hUdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hUinv : (((U⁻¹ : Gn g (m + 1)) : Mt g (m + 1))).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    let _ := U.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular (um_upper N)
  have hlast : ∀ k : Fin (m + 1), (k : ℕ) ≤ j → (h : Mt g (m + 1)) (Fin.last m) k = 0 := by
    intro k hk
    rw [hhdef, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    by_cases ha : (a : ℕ) ≤ j
    · rw [hz, finRotate_last, hy.1 a ha, zero_mul]
    · rw [hUinv (show k < a by rw [Fin.lt_def]; omega), mul_zero]
  have hdet : (h : Mt g (m + 1)) (Fin.last m) (Fin.last m) ≠ 0 := by
    have hl : (h : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := hab
      have ha : a ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hab' (Fin.le_last b))
      rw [hrow a ha, Matrix.one_apply_ne (ne_of_lt hab')]
    have hd : (h : Mt g (m + 1)).det = (h : Mt g (m + 1)) (Fin.last m) (Fin.last m) := by
      rw [Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_castSucc]
      simp [hrow _ (Fin.castSucc_lt_last _).ne]
    rw [← hd]
    exact IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit)
  set t : (ZMod g)ˣ := Units.mk0 _ hdet with htdef
  set w : WIdx m j → ZMod g := fun q => (h : Mt g (m + 1)) (Fin.last m) q.1 with hwdef
  refine ⟨(N, t, w), ?_⟩
  have hH : hpGL (rvec j t w) (by rw [rvec_last]; exact t.ne_zero) = h := by
    apply Units.ext
    ext a b
    rw [hpGL_val]
    simp only [Hp, Matrix.of_apply]
    by_cases ha : a = Fin.last m
    · subst ha
      rw [if_pos rfl]
      simp only [rvec]
      by_cases hb : b = Fin.last m
      · subst hb
        simp [htdef]
      · rw [if_neg hb]
        split_ifs with hb2
        · rfl
        · have hbm : (b : ℕ) ≠ m := fun e => hb (Fin.ext (by simp [e]))
          have := b.2
          have hbj : (b : ℕ) ≤ j := by
            by_contra hc
            exact hb2 ⟨by omega, by omega⟩
          exact (hlast b hbj).symm
    · rw [if_neg ha, hrow a ha]
  show cyc g (m + 1) * hpGL (rvec j t w) _ * umGL N = y
  rw [hH, hhdef, hzdef, ← hUdef]
  group

/- English proof (translation)
Rewrite using `[Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card_units]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_P (j : ℕ) :
    Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) =
      g ^ Fintype.card (SIdx m) * (g - 1) * g ^ Fintype.card (WIdx m j) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card_units]
  ring

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem rho_mul_inv_self (a : Gn g (m + 1)) (x : τ) : τ.ρ a (τ.ρ a⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
theorem rho_inv_mul_self (a : Gn g (m + 1)) (x : τ) : τ.ρ a⁻¹ (τ.ρ a x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Establish `key` using `Finset.sum_bij (s := (Finset.univ : Finset ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)))) (t := Finset.univ.filter (fun y : Gn g (m + 1) => IsY j (y : Mt g (m + 1)))) (f := fun _ => l (τ.ρ (cyc g (m + 1))⁻¹ v)) (g := fun y => (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m …`. Take `⟨p, hp⟩` from `phi_surj hj y (Finset.mem_filter.1 hy).2`. Conclude with `⟨p, Finset.mem_univ _, hp⟩)`. Use the proof step `(fun p _ => by`.

Take `⟨N, t, w⟩` from `p`. Use `show _ = (ψ₀ (trace ((phi j (N, t, w) : Gn g (m + 1)) : Mt g (m + 1)) - ((phi j (N, t, w) : Gn g (m + 1)) : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ (phi j (N, t, w))⁻¹ v)`. Rewrite using `[trace_phi]`. Establish `hr0 : rvec j t w (Fin.last m) ≠ 0` using `by rw [rvec_last]; exact t.ne_zero`. Use `set H := hpGL (rvec j t w) hr0`.

Establish `hinv : (phi j (N, t, w))⁻¹ = (umGL N)⁻¹ * (cyc g (m + 1))⁻¹ * (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹)⁻¹`. Simplify using `only [phi]`. Use `group`. Both sides reduce to the same expression. Establish `hX : τ.ρ (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹) v = v` using `hB _ (isRowFix_conj _ (fun l hl => rvec_low hj t w l hl) hr0)`.

Establish `hX' : τ.ρ (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹)⁻¹ v = v` using `by conv_lhs => rw [← hX]`. Conclude with `rho_inv_mul_self τ _ v`. Rewrite using `[hinv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hX']`. Use `hl (umGL N) (umGL_mem N) (τ.ρ (umGL N)⁻¹ (τ.ρ (cyc g (m + 1))⁻¹ v))` as an intermediate fact. Rewrite `this` using `[rho_mul_inv_self]`.

Conclude with `this)`. Rewrite using `[← key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
theorem rhs_sum {j : ℕ} (hj : j < m) (l : Module.Dual ℂ τ) (hl : IsFunctional ψ₀ τ.ρ l) (v : τ)
    (hB : ∀ h, IsRowFix j h → τ.ρ h v = v) :
    ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
        (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v) else 0) =
      (Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : ℂ) *
        l (τ.ρ (cyc g (m + 1))⁻¹ v) := by
  rw [← Finset.sum_filter]
  have key := Finset.sum_bij (s := (Finset.univ : Finset ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g))))
    (t := Finset.univ.filter (fun y : Gn g (m + 1) => IsY j (y : Mt g (m + 1))))
    (f := fun _ => l (τ.ρ (cyc g (m + 1))⁻¹ v))
    (g := fun y => (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v))
    (fun p _ => phi j p)
    (fun p _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, isY_phi hj p⟩)
    (fun p _ q _ h => phi_inj h)
    (fun y hy => by
      obtain ⟨p, hp⟩ := phi_surj hj y (Finset.mem_filter.1 hy).2
      exact ⟨p, Finset.mem_univ _, hp⟩)
    (fun p _ => by
      obtain ⟨N, t, w⟩ := p
      show _ = (ψ₀ (trace ((phi j (N, t, w) : Gn g (m + 1)) : Mt g (m + 1)) -
        ((phi j (N, t, w) : Gn g (m + 1)) : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ (phi j (N, t, w))⁻¹ v)
      rw [trace_phi]
      have hr0 : rvec j t w (Fin.last m) ≠ 0 := by rw [rvec_last]; exact t.ne_zero
      set H := hpGL (rvec j t w) hr0
      have hinv : (phi j (N, t, w))⁻¹ =
          (umGL N)⁻¹ * (cyc g (m + 1))⁻¹ * (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹)⁻¹ := by
        simp only [phi]
        group
        rfl
      have hX : τ.ρ (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹) v = v :=
        hB _ (isRowFix_conj _ (fun l hl => rvec_low hj t w l hl) hr0)
      have hX' : τ.ρ (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹)⁻¹ v = v := by
        conv_lhs => rw [← hX]
        exact rho_inv_mul_self τ _ v
      rw [hinv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hX']
      have := hl (umGL N) (umGL_mem N) (τ.ρ (umGL N)⁻¹ (τ.ρ (cyc g (m + 1))⁻¹ v))
      rw [rho_mul_inv_self] at this
      exact this)
  rw [← key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end DiscreteGroups.sglob.DzFe
