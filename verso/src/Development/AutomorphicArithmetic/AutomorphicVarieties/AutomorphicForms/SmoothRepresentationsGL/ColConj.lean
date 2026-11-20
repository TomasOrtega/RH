import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Establish `h1 : ∀ j, j < k → (p⁻¹).val k j = 0`. Establish `hb : p.val.BlockTriangular (fun i : Fin n => if i.val ≤ m then 0 else i.val)`. Introduce `i j hij`. Simplify using `only at hij`. Apply the tactic sequence `have hi : m + 1 ≤ i.val := by split_ifs at hij <;> omega`.

Use `(hp i hi).2 j ?_` and prove the remaining obligations. Rewrite using `[Fin.lt_def]`. Apply the tactic sequence `split_ifs at hij <;> omega`. Use `haveI : Invertible p.val := p.invertible`. Establish `hq` using `Matrix.blockTriangular_inv_of_blockTriangular hb`.

Introduce `j hj`. Rewrite using `[Matrix.coe_units_inv]`. Use `hq ?_` and prove the remaining obligations. Rewrite `hj` using `[Fin.lt_def]`. Simplify using `only`.

Apply the tactic sequence `split_ifs <;> omega`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2 : ((p⁻¹).val * p.val) k k = 1` using `by rw [Units.inv_mul, Matrix.one_apply_eq]`. Rewrite `h2` using `[Matrix.mul_apply, Finset.sum_eq_single k, (hp k hk.ge).1, mul_one]`. Conclude with `h2`.

Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[h1 j h, zero_mul]`. Rewrite using `[(hp j (by rw [Fin.lt_def] at h; omega)).2 k h, mul_zero]`. Simplify using the standard rewrite rules.
-/
private theorem inv_row {R : Type} [CommRing R] {n : ℕ} (m : ℕ) (k : Fin n) (hk : k.val = m + 1) (p : GL (Fin n) R)
    (hp : IsY (m + 1) p.val) : (∀ j, j < k → (p⁻¹).val k j = 0) ∧ (p⁻¹).val k k = 1 := by
  have h1 : ∀ j, j < k → (p⁻¹).val k j = 0 := by
    have hb : p.val.BlockTriangular (fun i : Fin n => if i.val ≤ m then 0 else i.val) := by
      intro i j hij
      dsimp only at hij
      have hi : m + 1 ≤ i.val := by split_ifs at hij <;> omega
      refine (hp i hi).2 j ?_
      rw [Fin.lt_def]
      split_ifs at hij <;> omega
    haveI : Invertible p.val := p.invertible
    have hq := Matrix.blockTriangular_inv_of_blockTriangular hb
    intro j hj
    rw [Matrix.coe_units_inv]
    refine hq ?_
    rw [Fin.lt_def] at hj
    dsimp only
    split_ifs <;> omega
  refine ⟨h1, ?_⟩
  have h2 : ((p⁻¹).val * p.val) k k = 1 := by rw [Units.inv_mul, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k, (hp k hk.ge).1, mul_one] at h2
  · exact h2
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h1 j h, zero_mul]
    · rw [(hp j (by rw [Fin.lt_def] at h; omega)).2 k h, mul_zero]
  · simp

/- English proof (translation)
Introduce `R _ n m hm p hp u`. Use `set k : Fin n := ⟨m.val + 1, hm⟩ with hkdef`. Establish `hk : k.val = m.val + 1` using `rfl`. Take `⟨hb0, hb1⟩` from `inv_row m.val k hk p hp`. Use `set c : Fin n → R := fun i => if i ≤ m then u i else 0 with hc`.

Use `set a : Fin n → R := p.val *ᵥ c with ha`. Use `set b : Fin n → R := (p⁻¹).val k with hb`. Establish `ha0 : ∀ i, m < i → a i = 0`. Introduce `i hi`. Express the relevant statement in the definitionally equal form `∑ j, p.val i j * c j = 0`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j ≤ m`. Rewrite using `[(hp i hi).2 j (lt_of_le_of_lt hj hi), zero_mul]`. Simplify using `[hc, hj]`. Establish `hab : ∀ i j, j ≤ i → a i * b j = 0`.

Introduce `i j hij`. Distinguish the cases in `hi : m < i`. Rewrite using `[ha0 i hi, zero_mul]`. Rewrite using `[hb0 j (by rw [Fin.lt_def] at hi ⊢; rw [Fin.le_def] at hij; omega), mul_zero]`. Establish `hdot : b ⬝ᵥ a = 0` using `Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact hab i i le_rfl`.

Establish `hsq : vecMulVec a b * vecMulVec a b = 0`. Rewrite using `[vecMulVec_mul_vecMulVec, hdot, zero_smul, vecMulVec_zero]`. Use `⟨⟨1 + vecMulVec a b, 1 - vecMulVec a b, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, mul_sub, mul_sub, hsq]`. Simplify using the standard rewrite rules.

Rewrite using `[sub_mul, mul_add, mul_add, hsq]`. Simplify using the standard rewrite rules. Introduce `i _`. Use `⟨?_, fun j hj => ?_⟩` and prove the remaining obligations. Simplify using `[vecMulVec_apply, hab i i le_rfl]`.

Simplify using `[vecMulVec_apply, hab i j hj.le, Matrix.one_apply_ne hj.ne']`. Establish `: dotLe m (p.val m) u = a m`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[hc]`. Rewrite using `[this]`.

Unfold `supN`. Rewrite using `[Finset.sum_eq_single m, Finset.sum_eq_single k]`. Establish `: m ≠ k` using `fun h => by have := congrArg Fin.val h; omega`. Simplify using `[hk, vecMulVec_apply, hb1, Matrix.one_apply_ne this]`. Introduce `j _ hj`.

Rewrite using `[if_neg fun h => hj (Fin.ext (by omega))]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Establish `hne : i ≠ j` using `fun e => by have := congrArg Fin.val e; omega`. Establish `: a i * b j = 0`. Break down `lt_or_gt_of_ne hi with h' | h'` into its components or cases. Rewrite using `[hb0 j (by rw [Fin.lt_def] at h' ⊢; omega), mul_zero]`. Rewrite using `[ha0 i h', zero_mul]`.

Simplify using `[vecMulVec_apply, this, Matrix.one_apply_ne hne]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Establish `h1 : colM m u = 1 + vecMulVec c (Pi.single k 1)`. Unfold `colM`.

Use `congr 1`. Use extensionality with `i j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using `[vecMulVec_apply, hc, hk]`.

Establish `: j.val ≠ m.val + 1` using `fun h => hj (Fin.ext h)`. Simplify using `[vecMulVec_apply, hj, this]`. Establish `h2 : b ᵥ* p.val = Pi.single k 1`. Use extensionality with `j`. Establish `: ((p⁻¹).val * p.val) k j = (1 : Matrix (Fin n) (Fin n) R) k j` using `by rw [Units.inv_mul]`.

Rewrite `this` using `[Matrix.one_apply]`. Rewrite using `[Pi.single_apply, ← if_congr eq_comm rfl rfl, ← this]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `p.val * colM m u = (1 + vecMulVec a b) * p.val`. Rewrite using `[h1, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, h2]`.
-/
theorem UpperTheory.V.Af.Smo.colConj :
    UpperTheory.V.Af.Smo.ColConj := by
  intro R _ n m hm p hp u
  set k : Fin n := ⟨m.val + 1, hm⟩ with hkdef
  have hk : k.val = m.val + 1 := rfl
  obtain ⟨hb0, hb1⟩ := inv_row m.val k hk p hp
  set c : Fin n → R := fun i => if i ≤ m then u i else 0 with hc
  set a : Fin n → R := p.val *ᵥ c with ha
  set b : Fin n → R := (p⁻¹).val k with hb
  have ha0 : ∀ i, m < i → a i = 0 := by
    intro i hi
    change ∑ j, p.val i j * c j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ≤ m
    · rw [(hp i hi).2 j (lt_of_le_of_lt hj hi), zero_mul]
    · simp [hc, hj]
  have hab : ∀ i j, j ≤ i → a i * b j = 0 := by
    intro i j hij
    by_cases hi : m < i
    · rw [ha0 i hi, zero_mul]
    · rw [hb0 j (by rw [Fin.lt_def] at hi ⊢; rw [Fin.le_def] at hij; omega), mul_zero]
  have hdot : b ⬝ᵥ a = 0 := Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact hab i i le_rfl
  have hsq : vecMulVec a b * vecMulVec a b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hdot, zero_smul, vecMulVec_zero]
  refine ⟨⟨1 + vecMulVec a b, 1 - vecMulVec a b, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub, hsq]; simp
  · rw [sub_mul, mul_add, mul_add, hsq]; simp
  · intro i _
    refine ⟨?_, fun j hj => ?_⟩
    · simp [vecMulVec_apply, hab i i le_rfl]
    · simp [vecMulVec_apply, hab i j hj.le, Matrix.one_apply_ne hj.ne']
  · have : dotLe m (p.val m) u = a m := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hc]
    rw [this]
    unfold supN
    rw [Finset.sum_eq_single m, Finset.sum_eq_single k]
    · have : m ≠ k := fun h => by have := congrArg Fin.val h; omega
      simp [hk, vecMulVec_apply, hb1, Matrix.one_apply_ne this]
    · intro j _ hj
      rw [if_neg fun h => hj (Fin.ext (by omega))]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hne : i ≠ j := fun e => by have := congrArg Fin.val e; omega
        have : a i * b j = 0 := by
          rcases lt_or_gt_of_ne hi with h' | h'
          · rw [hb0 j (by rw [Fin.lt_def] at h' ⊢; omega), mul_zero]
          · rw [ha0 i h', zero_mul]
        simp [vecMulVec_apply, this, Matrix.one_apply_ne hne]
      · rfl
    · simp
  · have h1 : colM m u = 1 + vecMulVec c (Pi.single k 1) := by
      unfold colM
      congr 1
      ext i j
      by_cases hj : j = k
      · subst hj
        simp [vecMulVec_apply, hc, hk]
      · have : j.val ≠ m.val + 1 := fun h => hj (Fin.ext h)
        simp [vecMulVec_apply, hj, this]
    have h2 : b ᵥ* p.val = Pi.single k 1 := by
      ext j
      have : ((p⁻¹).val * p.val) k j = (1 : Matrix (Fin n) (Fin n) R) k j := by rw [Units.inv_mul]
      rw [Matrix.one_apply] at this
      rw [Pi.single_apply, ← if_congr eq_comm rfl rfl, ← this]
      rfl
    change p.val * colM m u = (1 + vecMulVec a b) * p.val
    rw [h1, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, h2]
