import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LongEltCornerEqCyc

noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

/- English proof (translation)
Apply `exists_corner` to reduce the goal to its premises. Introduce `l`. Rewrite using `[conj_apply]`. Establish `ha` using `rot_inv_val hk.le (Fin.last m)`. Establish `hb` using `rot_inv_val hk.le l`.

Establish `hal` using `((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt`. Establish `hll` using `l.isLt`. Rewrite `ha` using `[Fin.val_last]`. Distinguish the cases in `hb0 : (((finRotate (m + 1) ^ k)⁻¹ l : Fin (m + 1)) : ℕ) = 0`. Rewrite using `[hh.2 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) hb0 (by omega), if_neg]`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Rewrite `this` using `[Fin.val_last]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hh.1 _ _ hb0]`.

Distinguish the cases in `e : l = Fin.last m`. Substitute `e` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Rewrite using `[if_neg e, if_neg]`. Introduce `e2`.

Conclude with `e (Equiv.injective _ e2).symm`. Introduce `i`. Rewrite using `[conj_apply]`. Establish `hb` using `rot_inv_val hk.le (Fin.last m)`. Establish `hbl` using `((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt`.

Rewrite `hb` using `[Fin.val_last]`. Rewrite using `[hh.1 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) (by omega)]`. Distinguish the cases in `e : i = Fin.last m`. Substitute `e` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[if_neg e, if_neg]`. Introduce `e2`. Conclude with `e (Equiv.injective _ e2)`. Introduce `i l hil`. Rewrite using `[conj_apply]`.

Establish `ha` using `rot_inv_val hk.le i.castSucc`. Establish `hb` using `rot_inv_val hk.le l.castSucc`. Establish `hal` using `((finRotate (m + 1) ^ k)⁻¹ i.castSucc).isLt`. Establish `hil' : (i : ℕ) < l` using `hil`. Establish `hll` using `l.isLt`.

Rewrite `ha`, `hb` using `[Fin.coe_castSucc]`. Distinguish the cases in `hb0 : (((finRotate (m + 1) ^ k)⁻¹ l.castSucc : Fin (m + 1)) : ℕ) = 0`. Conclude with `hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) hb0 (by omega)`. Rewrite using `[hh.1 _ _ hb0, if_neg]`. Introduce `e2`.

Use `congrArg Fin.val (Equiv.injective _ e2)` as an intermediate fact. Rewrite `this` using `[Fin.coe_castSucc, Fin.coe_castSucc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem colFix_conj [Fact g.Prime] {m k : ℕ} (hk : k < m) (h : GL (Fin (m + 1)) (ZMod g))
    (hh : IsColFix (m - 1 - k) h) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹ := by
  apply exists_corner
  · intro l
    rw [conj_apply]
    have ha := rot_inv_val hk.le (Fin.last m)
    have hb := rot_inv_val hk.le l
    have hal := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    have hll := l.isLt
    rw [Fin.val_last] at ha
    by_cases hb0 : (((finRotate (m + 1) ^ k)⁻¹ l : Fin (m + 1)) : ℕ) = 0
    · rw [hh.2 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) hb0 (by omega), if_neg]
      intro e
      have := congrArg Fin.val e
      rw [Fin.val_last] at this
      omega
    · rw [hh.1 _ _ hb0]
      by_cases e : l = Fin.last m
      · subst e; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg e, if_neg]
        intro e2; exact e (Equiv.injective _ e2).symm
  · intro i
    rw [conj_apply]
    have hb := rot_inv_val hk.le (Fin.last m)
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    rw [Fin.val_last] at hb
    rw [hh.1 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) (by omega)]
    by_cases e : i = Fin.last m
    · subst e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2; exact e (Equiv.injective _ e2)
  · intro i l hil
    rw [conj_apply]
    have ha := rot_inv_val hk.le i.castSucc
    have hb := rot_inv_val hk.le l.castSucc
    have hal := ((finRotate (m + 1) ^ k)⁻¹ i.castSucc).isLt
    have hil' : (i : ℕ) < l := hil
    have hll := l.isLt
    rw [Fin.coe_castSucc] at ha hb
    by_cases hb0 : (((finRotate (m + 1) ^ k)⁻¹ l.castSucc : Fin (m + 1)) : ℕ) = 0
    · exact hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) hb0 (by omega)
    · rw [hh.1 _ _ hb0, if_neg]
      intro e2
      have := congrArg Fin.val (Equiv.injective _ e2)
      rw [Fin.coe_castSucc, Fin.coe_castSucc] at this
      omega

/- English proof (translation)
Apply `exists_corner` to reduce the goal to its premises. Introduce `l`. Rewrite using `[conj_apply]`. Establish `ha` using `rot_inv_val hk.le (Fin.last m)`. Establish `hal` using `((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt`.

Rewrite `ha` using `[Fin.val_last]`. Rewrite using `[hh.1 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) (by omega)]`. Distinguish the cases in `e : l = Fin.last m`. Substitute `e` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[if_neg e, if_neg]`. Introduce `e2`. Conclude with `e (Equiv.injective _ e2).symm`. Introduce `i`. Rewrite using `[conj_apply]`.

Establish `ha` using `rot_inv_val hk.le i`. Establish `hb` using `rot_inv_val hk.le (Fin.last m)`. Establish `hbl` using `((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt`. Establish `hil` using `i.isLt`. Rewrite `hb` using `[Fin.val_last]`.

Distinguish the cases in `ha0 : (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) = 0`. Rewrite using `[hh.2 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ha0 (by omega) (by omega), if_neg]`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Rewrite `this` using `[Fin.val_last]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hh.1 _ _ ha0]`. Distinguish the cases in `e : i = Fin.last m`. Substitute `e` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[if_neg e, if_neg]`. Introduce `e2`. Conclude with `e (Equiv.injective _ e2)`. Introduce `i l hil`. Rewrite using `[conj_apply]`.

Establish `ha` using `rot_inv_val hk.le i.castSucc`. Establish `hb` using `rot_inv_val hk.le l.castSucc`. Establish `hbl` using `((finRotate (m + 1) ^ k)⁻¹ l.castSucc).isLt`. Establish `hil' : (i : ℕ) < l` using `hil`. Establish `hll` using `l.isLt`.

Rewrite `ha`, `hb` using `[Fin.coe_castSucc]`. Distinguish the cases in `ha0 : (((finRotate (m + 1) ^ k)⁻¹ i.castSucc : Fin (m + 1)) : ℕ) = 0`. Conclude with `hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) ha0 (by omega) (by omega)`. Rewrite using `[hh.1 _ _ ha0, if_neg]`. Introduce `e2`.

Use `congrArg Fin.val (Equiv.injective _ e2)` as an intermediate fact. Rewrite `this` using `[Fin.coe_castSucc, Fin.coe_castSucc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rowFix_conj [Fact g.Prime] {m k : ℕ} (hk : k < m) (h : GL (Fin (m + 1)) (ZMod g))
    (hh : IsRowFix (m - 1 - k) h) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹ := by
  apply exists_corner
  · intro l
    rw [conj_apply]
    have ha := rot_inv_val hk.le (Fin.last m)
    have hal := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    rw [Fin.val_last] at ha
    rw [hh.1 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) (by omega)]
    by_cases e : l = Fin.last m
    · subst e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2; exact e (Equiv.injective _ e2).symm
  · intro i
    rw [conj_apply]
    have ha := rot_inv_val hk.le i
    have hb := rot_inv_val hk.le (Fin.last m)
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    have hil := i.isLt
    rw [Fin.val_last] at hb
    by_cases ha0 : (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) = 0
    · rw [hh.2 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ha0 (by omega)
        (by omega), if_neg]
      intro e
      have := congrArg Fin.val e
      rw [Fin.val_last] at this
      omega
    · rw [hh.1 _ _ ha0]
      by_cases e : i = Fin.last m
      · subst e; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg e, if_neg]
        intro e2; exact e (Equiv.injective _ e2)
  · intro i l hil
    rw [conj_apply]
    have ha := rot_inv_val hk.le i.castSucc
    have hb := rot_inv_val hk.le l.castSucc
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ l.castSucc).isLt
    have hil' : (i : ℕ) < l := hil
    have hll := l.isLt
    rw [Fin.coe_castSucc] at ha hb
    by_cases ha0 : (((finRotate (m + 1) ^ k)⁻¹ i.castSucc : Fin (m + 1)) : ℕ) = 0
    · exact hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) ha0
        (by omega) (by omega)
    · rw [hh.1 _ _ ha0, if_neg]
      intro e2
      have := congrArg Fin.val (Equiv.injective _ e2)
      rw [Fin.coe_castSucc, Fin.coe_castSucc] at this
      omega

end DiscreteGroups.sglob.DzFe
