import Formalism.LocalToGlobal.Columns.LevGSym
import Formalism.LocalToGlobal.HermitianForms.DefsSym
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
import Formalism.LocalToGlobal.Columns.LevGCount
open Formalism.L2.Col

namespace GlobalTheory.MemXSym

open Formalism.L2.Forms

/- English proof (translation)
Break down `Nat.lt_or_ge x r with h1 | h1` into its components or cases. Use `Or.inl ⟨h1, coarse_of_lt h1, ?_, ?_⟩` and prove the remaining obligations. Establish `: x < rSym k rS` using `by unfold rSym; omega`. Apply the tactic sequence `rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega`. Apply the tactic sequence `unfold symIdx; split_ifs <;> omega`.

Use `Or.inr ⟨h1, ?_, by rw [coarse_of_le h1]; omega⟩` and prove the remaining obligations. Establish `hx' : ¬ x < rSym k rS` using `by unfold rSym; omega`. Establish `hs : rSym k rS = r` using `by unfold rSym; omega`. Unfold `lvSym`. Rewrite using `[if_neg hx', hs]`.

Break down `Nat.lt_or_ge x (r + m * t) with h2 | h2` into its components or cases. Rewrite using `[GlobalTheory.TopLawSym.coarse_eq ht h1 h2, Nat.add_assoc]`. Establish `hx2 : x = r + m * t` using `by omega`. Substitute `hx2` using the available equality. Rewrite using `[coarse_of_le h1, blkIdx_replicate_of_le t m (r + m * t - r) (by omega), Nat.add_sub_cancel_left, Nat.mul_div_cancel _ ht, Nat.add_assoc]`.
-/
theorem facts {n k r t m rS : ℕ} (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1) (x : ℕ) (hx : x < n) :
    (x < r ∧ coarse r (List.replicate m t) x = 0 ∧ lvSym k rS t x = symIdx k rS x ∧ symIdx k rS x < r) ∨
    (r ≤ x ∧ lvSym k rS t x + 1 = r + coarse r (List.replicate m t) x ∧ 1 ≤ coarse r (List.replicate m t) x) := by
  rcases Nat.lt_or_ge x r with h1 | h1
  · refine Or.inl ⟨h1, coarse_of_lt h1, ?_, ?_⟩
    · have : x < rSym k rS := by unfold rSym; omega
      rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega
    · unfold symIdx; split_ifs <;> omega
  · refine Or.inr ⟨h1, ?_, by rw [coarse_of_le h1]; omega⟩
    have hx' : ¬ x < rSym k rS := by unfold rSym; omega
    have hs : rSym k rS = r := by unfold rSym; omega
    unfold lvSym; rw [if_neg hx', hs]
    rcases Nat.lt_or_ge x (r + m * t) with h2 | h2
    · rw [GlobalTheory.TopLawSym.coarse_eq ht h1 h2, Nat.add_assoc]
    · have hx2 : x = r + m * t := by omega
      subst hx2
      rw [coarse_of_le h1, blkIdx_replicate_of_le t m (r + m * t - r) (by omega), Nat.add_sub_cancel_left,
        Nat.mul_div_cancel _ ht, Nat.add_assoc]

/- English proof (translation)
Establish `: x < rSym k rS` using `by unfold rSym; omega`. Apply the tactic sequence `rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega`.
-/
theorem facts_lt {k r t rS x : ℕ} (hr : r = k + 2 * rS + 1) (hx : x < r) :
    lvSym k rS t x = symIdx k rS x := by
  have : x < rSym k rS := by unfold rSym; omega
  rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega

/- English proof (translation)
Establish `cN : coarse r (List.replicate m t) (r + m * t) = m + 1`. Rewrite using `[coarse_of_le (by omega), blkIdx_replicate_of_le t m (r + m * t - r) (by omega)]`. Rewrite using `[cN]`. Break down `Nat.lt_or_ge x r with h1 | h1` into its components or cases. Rewrite using `[coarse_of_lt h1]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[coarse_of_le h1]; have := blkIdx_replicate_lt t m (x - r) (by omega); omega`.
-/
theorem coarse_last {r t m x : ℕ} (hx : x < r + m * t) :
    coarse r (List.replicate m t) x < coarse r (List.replicate m t) (r + m * t) := by
  have cN : coarse r (List.replicate m t) (r + m * t) = m + 1 := by
    rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m (r + m * t - r) (by omega)]
  rw [cN]
  rcases Nat.lt_or_ge x r with h1 | h1
  · rw [coarse_of_lt h1]; omega
  · rw [coarse_of_le h1]; have := blkIdx_replicate_lt t m (x - r) (by omega); omega

variable {κ : Type} [Field κ]

/- English proof (translation)
Take `⟨hJ, hF⟩` from `Subgroup.mem_inf.mp hM`. Establish `hF' : ∀ i j : Fin n, j.val = r + m * t → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j` using `hF`. Take `⟨hB, h0⟩` from `mem_HPar.mp hJ`. Establish `hkr : k + rS ≤ r` using `by omega`. Rewrite `h0` using `[mem_HPsymF_iff hkr]`.

Take `⟨p1, p2, p3⟩` from `h0`. Use `⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>`. Break down `facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩` into its components or cases. Rewrite `hxy` using `[lx, ly]`.

Conclude with `p1 ⟨x, hx⟩ ⟨y, hy⟩ hxy`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Conclude with `(mem_btG.mp hB) x y (by omega)`. Conclude with `(mem_btG.mp hB) x y (by omega)`.

Conclude with `p2 ⟨x, by unfold rSym at hx; omega⟩`. Conclude with `p3 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy`. Establish `hy' : y.val = r + m * t` using `by omega`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hF' x y hy', Matrix.one_apply]`.

Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Rewrite using `[hF' x x hy', Matrix.one_apply]`. Rewrite using `[if_neg hxy]`. Apply `(mem_btG.mp hB) y x` to reduce the goal to its premises.

Establish `hx1 : x.val < r + m * t`. Use `x.2` as an intermediate fact. Establish `: x.val ≠ y.val` using `fun e => hxy (Fin.ext e)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hy']`.

Conclude with `coarse_last hx1`.
-/
theorem inJ_of_mem {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : M ∈ HXmsym κ n k r t m rS h) : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ) := by
  obtain ⟨hJ, hF⟩ := Subgroup.mem_inf.mp hM
  have hF' : ∀ i j : Fin n, j.val = r + m * t → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := hF
  obtain ⟨hB, h0⟩ := mem_HPar.mp hJ
  have hkr : k + rS ≤ r := by omega
  rw [mem_HPsymF_iff hkr] at h0
  obtain ⟨p1, p2, p3⟩ := h0
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩
  · rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩
    · rw [lx, ly] at hxy
      exact p1 ⟨x, hx⟩ ⟨y, hy⟩ hxy
    · exfalso; omega
    · exact (mem_btG.mp hB) x y (by omega)
    · exact (mem_btG.mp hB) x y (by omega)
  · exact p2 ⟨x, by unfold rSym at hx; omega⟩
  · exact p3 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy
  · have hy' : y.val = r + m * t := by omega
    constructor
    · rw [hF' x y hy', Matrix.one_apply]
    · by_cases hxy : x = y
      · subst hxy; rw [hF' x x hy', Matrix.one_apply]
      · rw [if_neg hxy]
        apply (mem_btG.mp hB) y x
        have hx1 : x.val < r + m * t := by
          have := x.2; have : x.val ≠ y.val := fun e => hxy (Fin.ext e); omega
        rw [hy']
        exact coarse_last hx1

/- English proof (translation)
Take `⟨q1, q2, q3, q4⟩` from `hM`. Establish `hkr : k + rS ≤ r` using `by omega`. Establish `hB : M ∈ blockUT n κ r (List.replicate m t)` using `mem_btG.mpr fun x y hxy => q1 x y (by`. Apply the tactic sequence `rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>`. Apply the tactic sequence `rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩ <;> omega)`.

Use `Subgroup.mem_inf.mpr ⟨mem_HPar.mpr ⟨hB, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_HPsymF_iff hkr]`. Use `⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩` and prove the remaining obligations. Use `q1 (Fin.castLE h i) (Fin.castLE h j) ?_` and prove the remaining obligations. Simplify using `only [Fin.coe_castLE]`.

Rewrite using `[facts_lt hr i.2, facts_lt hr j.2]`. Conclude with `hij`. Conclude with `q2 (Fin.castLE h i) (by simp only [Fin.coe_castLE]; unfold rSym; omega)`. Conclude with `q3 (Fin.castLE h i) (Fin.castLE h j) (by simpa using hi) (by simpa using hj)`. Introduce `x y hy`.

Rewrite using `[(q4 rfl x y (by omega)).1, Matrix.one_apply]`.
-/
theorem mem_of_inJ {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ)) : M ∈ HXmsym κ n k r t m rS h := by
  obtain ⟨q1, q2, q3, q4⟩ := hM
  have hkr : k + rS ≤ r := by omega
  have hB : M ∈ blockUT n κ r (List.replicate m t) := mem_btG.mpr fun x y hxy => q1 x y (by
    rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩ <;> omega)
  refine Subgroup.mem_inf.mpr ⟨mem_HPar.mpr ⟨hB, ?_⟩, ?_⟩
  · rw [mem_HPsymF_iff hkr]
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · refine q1 (Fin.castLE h i) (Fin.castLE h j) ?_
      simp only [Fin.coe_castLE]
      rw [facts_lt hr i.2, facts_lt hr j.2]
      exact hij
    · exact q2 (Fin.castLE h i) (by simp only [Fin.coe_castLE]; unfold rSym; omega)
    · exact q3 (Fin.castLE h i) (Fin.castLE h j) (by simpa using hi) (by simpa using hj)
  · intro x y hy
    rw [(q4 rfl x y (by omega)).1, Matrix.one_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hM show InJSym k rS t true _ ∧ InJSym k rS t true _`. Conclude with `⟨inJ_of_mem h hr ht hn hM, inJ_of_mem h hr ht hn (Subgroup.inv_mem _ hM)⟩`. Introduce `hM`. Conclude with `mem_of_inJ h hr ht hn hM.1`.
-/
theorem memX (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t)
    (hn : n = r + m * t + 1) (M : GL (Fin n) κ) :
    M ∈ HXmsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t true := by
  constructor
  · intro hM
    show InJSym k rS t true _ ∧ InJSym k rS t true _
    exact ⟨inJ_of_mem h hr ht hn hM, inJ_of_mem h hr ht hn (Subgroup.inv_mem _ hM)⟩
  · intro hM
    exact mem_of_inJ h hr ht hn hM.1

end GlobalTheory.MemXSym
