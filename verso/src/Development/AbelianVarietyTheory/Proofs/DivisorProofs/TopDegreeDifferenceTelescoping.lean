import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyRegularityCauchyEstimate
open GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

/- English proof (translation)
Use `set a := v + K.ar φ`. Use `set b := v + K.ar φ'`. Set `w : ℕ → Fin (e + 1) → K.V` to `fun i k => if (k : ℕ) < i then a else b`. Set `g : ℕ → ℝ` to `fun i => K.num (w i)`. Establish `hs : M.Smooth (φ - φ')` using `fun σ => GlobalTheory.Mean4O.Cauchy.smooth_sub (hφ σ) (hφ' σ)`.

Establish `h0 : g 0 = K.top b`. Simplify using `only [g, w, Calc.top]`. Use `congr 1`. Establish `hN : g (e + 1) = K.top a`. Simplify using `only [g, w, Calc.top]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[k.isLt]`. Establish `hab : a - b = K.ar (φ - φ')` using `by simp [a, b, map_sub]`. Establish `step : ∀ i ∈ Finset.range (e + 1), g (i + 1) - g i = M.int (fun k : Fin e => K.c1 (if (k : ℕ) < i then a else b)) (φ - φ')`.

Introduce `i hi`. Establish `hi' : i < e + 1` using `Finset.mem_range.1 hi`. Set `j : Fin (e + 1)` to `⟨i, hi'⟩`. Set `p : Fin e → K.V` to `fun k => if (k : ℕ) < i then a else b`. Establish `hw : ∀ x, Function.update (w i) j x = j.insertNth x p`.

Introduce `x`. Use function extensionality and compare the values at `k`. Break down `eq_or_ne k j with rfl | hk` into its components or cases. Simplify using the standard rewrite rules. Take `⟨m, rfl⟩` from `Fin.exists_succAbove_eq hk`.

Rewrite using `[Function.update_of_ne hk, Fin.insertNth_apply_succAbove]`. Simplify using `only [w, p]`. Break down `Nat.lt_or_ge (m : ℕ) i with hm | hm` into its components or cases. Establish `: j.succAbove m = m.castSucc` using `Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, j, hm])`. Rewrite using `[this]`.

Simplify using `[hm]`. Establish `: j.succAbove m = m.succ` using `Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, j, hm])`. Rewrite using `[this]; simp only [Fin.val_succ]; rw [if_neg (by omega), if_neg (by omega)]`. Establish `e1 : w (i + 1) = Function.update (w i) j a`. Use function extensionality and compare the values at `k`.

Break down `eq_or_ne k j with rfl | hk` into its components or cases. Simplify using `[w, j]`. Rewrite using `[Function.update_of_ne hk]`. Establish `: (k : ℕ) ≠ i` using `fun h => hk (Fin.ext h)`. Simplify using `only [w]`.

Break down `lt_or_gt_of_ne this with h | h` into its components or cases. Rewrite using `[if_pos (by omega), if_pos h]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Establish `e2 : w i = Function.update (w i) j b` using `by symm; rw [Function.update_eq_self_iff]; simp [w, j]`. Establish `: g (i + 1) - g i = K.num (Function.update (w i) j (a - b))`.

Simplify using `only [g]`. Rewrite using `[e1, MultilinearMap.map_update_sub]`. Use `congr 1`. Rewrite using `[← e2]`. Rewrite using `[this, hab, hw, ← K.symm _ j.cycleRange.symm, Fin.insertNth_comp_cycleRange_symm, K.num_ar _ hs]`.

Rewrite using `[← h0, ← hN, ← Finset.sum_range_sub g (e + 1)]`. Conclude with `Finset.sum_congr rfl step`.
-/
theorem Calc.top_add_ar_sub {e : ℕ} (M : Man e) (K : Calc M) (v : K.V) (φ φ' : M.Fun) (hφ : M.Smooth φ)
    (hφ' : M.Smooth φ') :
    K.top (v + K.ar φ) - K.top (v + K.ar φ') = ∑ i ∈ Finset.range (e + 1),
      M.int (fun k : Fin e => K.c1 (if (k : ℕ) < i then v + K.ar φ else v + K.ar φ')) (φ - φ') := by
  set a := v + K.ar φ
  set b := v + K.ar φ'
  let w : ℕ → Fin (e + 1) → K.V := fun i k => if (k : ℕ) < i then a else b
  let g : ℕ → ℝ := fun i => K.num (w i)
  have hs : M.Smooth (φ - φ') := fun σ => GlobalTheory.Mean4O.Cauchy.smooth_sub (hφ σ) (hφ' σ)
  have h0 : g 0 = K.top b := by
    simp only [g, w, Calc.top]; congr 1
  have hN : g (e + 1) = K.top a := by
    simp only [g, w, Calc.top]; congr 1; funext k; simp [k.isLt]
  have hab : a - b = K.ar (φ - φ') := by simp [a, b, map_sub]
  have step : ∀ i ∈ Finset.range (e + 1), g (i + 1) - g i =
      M.int (fun k : Fin e => K.c1 (if (k : ℕ) < i then a else b)) (φ - φ') := by
    intro i hi
    have hi' : i < e + 1 := Finset.mem_range.1 hi
    let j : Fin (e + 1) := ⟨i, hi'⟩
    let p : Fin e → K.V := fun k => if (k : ℕ) < i then a else b
    have hw : ∀ x, Function.update (w i) j x = j.insertNth x p := by
      intro x; funext k
      rcases eq_or_ne k j with rfl | hk
      · simp
      · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hk
        rw [Function.update_of_ne hk, Fin.insertNth_apply_succAbove]
        simp only [w, p]
        rcases Nat.lt_or_ge (m : ℕ) i with hm | hm
        · have : j.succAbove m = m.castSucc := Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, j, hm])
          rw [this]; simp [hm]
        · have : j.succAbove m = m.succ := Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, j, hm])
          rw [this]; simp only [Fin.val_succ]; rw [if_neg (by omega), if_neg (by omega)]
    have e1 : w (i + 1) = Function.update (w i) j a := by
      funext k
      rcases eq_or_ne k j with rfl | hk
      · simp [w, j]
      · rw [Function.update_of_ne hk]
        have : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
        simp only [w]
        rcases lt_or_gt_of_ne this with h | h
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg (by omega)]
    have e2 : w i = Function.update (w i) j b := by
      symm; rw [Function.update_eq_self_iff]; simp [w, j]
    have : g (i + 1) - g i = K.num (Function.update (w i) j (a - b)) := by
      simp only [g]; rw [e1, MultilinearMap.map_update_sub]; congr 1; rw [← e2]
    rw [this, hab, hw, ← K.symm _ j.cycleRange.symm, Fin.insertNth_comp_cycleRange_symm, K.num_ar _ hs]
  rw [← h0, ← hN, ← Finset.sum_range_sub g (e + 1)]
  exact Finset.sum_congr rfl step

end GlobalTheory.Mean4O
