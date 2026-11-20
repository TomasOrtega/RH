import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
import Formalism.SharpRestriction.GrowthBounds.JointsLit

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Unfold `wdim`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Both sides reduce to the same expression.
-/
theorem wdim_shift {r : ℕ} (lam : Fin r → ℤ) (c : ℤ) : wdim (fun i => lam i + c) = wdim lam := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · congr 1
    push_cast
    ring
  · rfl

/- English proof (translation)
Unfold `wdim`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Int.cast_natCast]`.
-/
theorem wdim_nat {r : ℕ} (nu : Fin r → ℕ) :
    wdim (fun i => (nu i : ℤ)) = ∏ i : Fin r, ∏ j : Fin r,
      if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1 := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Int.cast_natCast]

/- English proof (translation)
Introduce `i j hij`. Break down `eq_or_lt_of_le hij with rfl | hlt` into its components or cases. Conclude with `le_rfl`. Establish `h1 : i.succ ≤ j.castSucc`. Rewrite using `[Fin.le_def]`.

Establish `: (i : ℕ) < (j : ℕ)` using `hlt`. Simplify using `using this`. Conclude with `((h j).2.trans (hl h1)).trans (h i).1`.
-/
theorem antitone_of_interlace {r : ℕ} {lamN : Fin (r + 1) → ℕ} (hl : Antitone lamN) (nu : Fin r → ℕ)
    (h : ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) : Antitone nu := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have h1 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      have : (i : ℕ) < (j : ℕ) := hlt
      simpa using this
    exact ((h j).2.trans (hl h1)).trans (h i).1

/- English proof (translation)
Introduce `r mu hmu`. Use `set c : ℤ := mu (Fin.last r) with hc`. Set `lamN : Fin (r + 1) → ℕ` to `fun i => (mu i - c).toNat`. Establish `hge : ∀ i, c ≤ mu i` using `fun i => hmu (Fin.le_last i)`. Establish `hcast : ∀ i, (lamN i : ℤ) = mu i - c` using `fun i => Int.toNat_of_nonneg (by linarith [hge i])`.

Establish `hanti : Antitone lamN`. Introduce `i j hij`. Establish `h1` using `hmu hij`. Establish `: (lamN j : ℤ) ≤ (lamN i : ℤ)` using `by rw [hcast, hcast]; linarith`. Conclude with `this` after adjusting the coercions.

Establish `e1 : wdim mu = (Module.finrank ℚ (Formalism.GradedWeylDivisibility.dualWeyl ℚ (r + 1) (r + 1) lamN) : ℚ)`. Establish `hmu' : mu = fun i => (lamN i : ℤ) + c` using `funext fun i => by rw [hcast]; ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, h2 ℚ r lamN hanti]`. Use `push_cast`.

Use `set F := (Fintype.piFinset (fun _ : Fin r => Finset.range (lamN 0 + 1))).filter (fun nu => ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) with hF`. Establish `hinj : Set.InjOn (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c) F`. Introduce `a _ b _ hab`. Use function extensionality and compare the values at `i`. Use `congrFun hab i` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[finsum_eq_sum_of_support_subset (s := F.image (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c))]`. Rewrite using `[Finset.sum_image hinj]`. Use `Finset.sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations.

Rewrite `hnu` using `[hF, Finset.mem_filter]`. Establish `hnu2` using `hnu.2`. Establish `hA : Antitone nu` using `antitone_of_interlace hanti nu hnu2`. Rewrite using `[if_pos, wdim_shift, wdim_nat, h3 ℚ r nu hA]`. Introduce `i`.

Use `show mu i.succ ≤ (nu i : ℤ) + c ∧ (nu i : ℤ) + c ≤ mu i.castSucc`. Establish `h1` using `hnu2 i`. Establish `a1` using `hcast i.succ`. Establish `a2` using `hcast i.castSucc`. Apply the tactic sequence `constructor <;> omega`.

Introduce `lam hlam`. Rewrite `hlam` using `[Function.mem_support]`. Establish `hcond : ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc`. Assume the negation of the conclusion as `hn`. Conclude with `hlam (if_neg hn)`.

Rewrite using `[Finset.coe_image]`. Use `⟨fun i => (lam i - c).toNat, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_coe, hF, Finset.mem_filter, Fintype.mem_piFinset]`. Establish `hl : ∀ i, ((lam i - c).toNat : ℤ) = lam i - c` using `fun i => Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])`. Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_range] show (lam i - c).toNat < lamN 0 + 1`. Establish `a0` using `hcast 0`. Establish `h0 : mu i.castSucc ≤ mu 0` using `hmu (Fin.zero_le _)`. Use `hl i` as an intermediate fact. Use `(hcond i).2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `show lamN i.succ ≤ (lam i - c).toNat ∧ (lam i - c).toNat ≤ lamN i.castSucc`. Establish `a1` using `hcast i.succ`. Establish `a2` using `hcast i.castSucc`. Establish `b1` using `hl i`.

Establish `b2` using `hcond i`. Apply the tactic sequence `constructor <;> omega`. Use function extensionality and compare the values at `i`. Establish `: ((lam i - c).toNat : ℤ) = lam i - c` using `Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])`. Simplify using `only [this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem numBranch_of {D : Formalism.BasicNotions.D7} (h2 : adm2 D) (h3 : adm3 D) : NumBranchAt := by
  intro r mu hmu
  classical
  set c : ℤ := mu (Fin.last r) with hc
  let lamN : Fin (r + 1) → ℕ := fun i => (mu i - c).toNat
  have hge : ∀ i, c ≤ mu i := fun i => hmu (Fin.le_last i)
  have hcast : ∀ i, (lamN i : ℤ) = mu i - c := fun i => Int.toNat_of_nonneg (by linarith [hge i])
  have hanti : Antitone lamN := by
    intro i j hij
    have h1 := hmu hij
    have : (lamN j : ℤ) ≤ (lamN i : ℤ) := by rw [hcast, hcast]; linarith
    exact_mod_cast this
  have e1 : wdim mu = (Module.finrank ℚ (Formalism.GradedWeylDivisibility.dualWeyl ℚ (r + 1) (r + 1) lamN) : ℚ) := by
    have hmu' : mu = fun i => (lamN i : ℤ) + c := funext fun i => by rw [hcast]; ring
    calc wdim mu = wdim (fun i => (lamN i : ℤ) + c) := congrArg wdim hmu'
      _ = wdim (fun i => (lamN i : ℤ)) := wdim_shift _ c
      _ = _ := by rw [wdim_nat, h3 ℚ (r + 1) lamN hanti]
  rw [e1, h2 ℚ r lamN hanti]
  push_cast
  set F := (Fintype.piFinset (fun _ : Fin r => Finset.range (lamN 0 + 1))).filter
    (fun nu => ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) with hF
  have hinj : Set.InjOn (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c) F := by
    intro a _ b _ hab
    funext i
    have := congrFun hab i
    simp only at this
    omega
  rw [finsum_eq_sum_of_support_subset (s := F.image (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c))]
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [hF, Finset.mem_filter] at hnu
    have hnu2 := hnu.2
    have hA : Antitone nu := antitone_of_interlace hanti nu hnu2
    rw [if_pos, wdim_shift, wdim_nat, h3 ℚ r nu hA]
    intro i
    show mu i.succ ≤ (nu i : ℤ) + c ∧ (nu i : ℤ) + c ≤ mu i.castSucc
    have h1 := hnu2 i
    have a1 := hcast i.succ
    have a2 := hcast i.castSucc
    constructor <;> omega
  · intro lam hlam
    rw [Function.mem_support] at hlam
    have hcond : ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc := by
      by_contra hn
      exact hlam (if_neg hn)
    rw [Finset.coe_image]
    refine ⟨fun i => (lam i - c).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, hF, Finset.mem_filter, Fintype.mem_piFinset]
      have hl : ∀ i, ((lam i - c).toNat : ℤ) = lam i - c := fun i =>
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [Finset.mem_range]
        show (lam i - c).toNat < lamN 0 + 1
        have a0 := hcast 0
        have h0 : mu i.castSucc ≤ mu 0 := hmu (Fin.zero_le _)
        have := hl i
        have := (hcond i).2
        omega
      · show lamN i.succ ≤ (lam i - c).toNat ∧ (lam i - c).toNat ≤ lamN i.castSucc
        have a1 := hcast i.succ
        have a2 := hcast i.castSucc
        have b1 := hl i
        have b2 := hcond i
        constructor <;> omega
    · funext i
      have : ((lam i - c).toNat : ℤ) = lam i - c :=
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      simp only [this]
      ring

/- English proof (translation)
Introduce `n N LL B P`. Establish `h` using `Formalism.MainNotions.G.Joints.Lit.weyl_dimension_formula_index_sets D n N P.mu (P.dom (Fin.last N))`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem stWeylAt (D : Formalism.BasicNotions.D7) : StWeylAt := by
  intro n N LL B P
  have h := Formalism.MainNotions.G.Joints.Lit.weyl_dimension_formula_index_sets D n N P.mu (P.dom (Fin.last N))
  rw [h]
  rfl

end Formalism.MainNotions.ColumnSystems.Pf
