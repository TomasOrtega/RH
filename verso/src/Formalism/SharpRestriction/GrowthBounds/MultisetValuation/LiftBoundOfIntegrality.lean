import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.YEPEComm

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]`.
-/
theorem sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Icc 1 m, f j = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem sum_ind {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : ι → ℝ) :
    ∑ v ∈ A, f v = ∑ v, if v ∈ A then f v else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

/- English proof (translation)
Establish `hS' : ∑ j ∈ range mm, ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) ≤ ∑ v ∈ VV \ BB, S v`. Rewrite using `[Finset.sum_comm, sum_ind (VV \ BB) S]`. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ VV \ BB`. Simplify using `only [hv, ↓reduceIte]`.

Conclude with `hS v (Finset.mem_sdiff.1 hv).1`. Simplify using `[hv]`. Establish `key : ∀ j ∈ range mm, (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) + ∑ v ∈ univ \ VV, G0n v (j + 1)) - dG j ≤ ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) + ((∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1))) - dG j …`. Introduce `j hj`. Establish `hj' : j < mm` using `Finset.mem_range.1 hj`.

It suffices to establish `h : ∑ v, ((if v ∈ VV then max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) else 0) + (if v ∈ univ \ VV then G0n v (j + 1) else 0) + (if inB j v then Prr v (j + 1) else 0)) ≤ ∑ v, ((if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) + (if inB j v th …`. Rewrite using `[sum_ind VV, sum_ind (univ \ VV)]`. Simplify using `only [Finset.sum_add_distrib] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ VV`. Establish `hv2 : v ∉ univ \ VV` using `by simp [hv]`. Distinguish the cases in `hb : v ∈ BB`. Establish `hv3 : v ∉ VV \ BB` using `by simp [hb]`. Distinguish the cases in `hi : inB j v`.

Establish `h1` using `((hin j v).1 hi).2`. Establish `h2` using `hPR v hv j hj'`. Simplify using `only [hv, hv2, hv3, hi, ↓reduceIte]`. Rewrite using `[max_eq_left h1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : ¬ (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))` using `fun h => hi ((hin j v).2 ⟨hb, h⟩)`. Simplify using `only [hv, hv2, hv3, hi, ↓reduceIte]`. Rewrite using `[max_eq_right (le_of_lt (not_le.1 h1))]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv3 : v ∈ VV \ BB` using `Finset.mem_sdiff.2 ⟨hv, hb⟩`.

Establish `hi : ¬ inB j v` using `fun h => hb ((hin j v).1 h).1`. Simplify using `only [hv, hv2, hv3, hi, ↓reduceIte]`. Establish `hm : max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) ≤ max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 + G0n v (j + 1)`. Use `le_max_left (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0` as an intermediate fact. Use `le_max_right (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0` as an intermediate fact.

Conclude with `max_le (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv2 : v ∈ univ \ VV` using `by simp [hv]`. Establish `hb : v ∉ BB` using `fun h => hv (hBB h)`. Establish `hv3 : v ∉ VV \ BB` using `by simp [hv]`.

Establish `hi : ¬ inB j v` using `fun h => hb ((hin j v).1 h).1`. Simplify using `only [hv, hv2, hv3, hi, ↓reduceIte]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `Finset.sum_le_sum key`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem basic₂ {ι : Type} [Fintype ι] [DecidableEq ι] (mm : ℕ) (VV BB : Finset ι) (hBB : BB ⊆ VV)
    (Gn G0n PRn Prr : ι → ℕ → ℝ) (S : ι → ℝ) (dG : ℕ → ℝ) (inB : ℕ → ι → Prop) [∀ j v, Decidable (inB j v)]
    (hin : ∀ j v, inB j v ↔ v ∈ BB ∧ G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    (hPR : ∀ v ∈ VV, ∀ j < mm, Prr v (j + 1) ≤ PRn v (j + 1))
    (hS : ∀ v ∈ VV, ∑ j ∈ range mm, max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 ≤ S v) :
    ∑ j ∈ range mm, (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) +
        ∑ v ∈ univ \ VV, G0n v (j + 1)) - ∑ j ∈ range mm, dG j ≤
      ∑ v ∈ VV \ BB, S v + ∑ j ∈ range mm, (∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1)) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
  have hS' : ∑ j ∈ range mm, ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0)
      ≤ ∑ v ∈ VV \ BB, S v := by
    rw [Finset.sum_comm, sum_ind (VV \ BB) S]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV \ BB
    · simp only [hv, ↓reduceIte]
      exact hS v (Finset.mem_sdiff.1 hv).1
    · simp [hv]
  have key : ∀ j ∈ range mm,
      (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) + ∑ v ∈ univ \ VV, G0n v (j + 1)) - dG j ≤
      ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
      ((∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1))) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
    intro j hj
    have hj' : j < mm := Finset.mem_range.1 hj
    suffices h : ∑ v, ((if v ∈ VV then max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) else 0) +
        (if v ∈ univ \ VV then G0n v (j + 1) else 0) + (if inB j v then Prr v (j + 1) else 0)) ≤
        ∑ v, ((if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
        (if inB j v then Gn v (j + 1) else G0n v (j + 1))) by
      rw [sum_ind VV, sum_ind (univ \ VV)]
      simp only [Finset.sum_add_distrib] at h
      linarith
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV
    · have hv2 : v ∉ univ \ VV := by simp [hv]
      by_cases hb : v ∈ BB
      · have hv3 : v ∉ VV \ BB := by simp [hb]
        by_cases hi : inB j v
        · have h1 := ((hin j v).1 hi).2
          have h2 := hPR v hv j hj'
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_left h1]
          linarith
        · have h1 : ¬ (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1)) := fun h => hi ((hin j v).2 ⟨hb, h⟩)
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_right (le_of_lt (not_le.1 h1))]
          linarith
      · have hv3 : v ∈ VV \ BB := Finset.mem_sdiff.2 ⟨hv, hb⟩
        have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
        simp only [hv, hv2, hv3, hi, ↓reduceIte]
        have hm : max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) ≤
            max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 + G0n v (j + 1) := by
          have := le_max_left (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          have := le_max_right (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          exact max_le (by linarith) (by linarith)
        linarith
    · have hv2 : v ∈ univ \ VV := by simp [hv]
      have hb : v ∉ BB := fun h => hv (hBB h)
      have hv3 : v ∉ VV \ BB := by simp [hv]
      have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
      simp only [hv, hv2, hv3, hi, ↓reduceIte]
      linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

/- English proof (translation)
Simplify using `only [Sys.Conclusion₂, PrZ, Pr]`. Use `push_cast`. Use `congr 1`. Take `⟨k, hk⟩` from `(X.G.P.setting v).even`. Rewrite using `[hk]`.

Establish `h2 : ((k + k : ℕ) : ℤ) / 2 = (k : ℤ)` using `by omega`. Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PrZ_cast (v : X.Pl) (j : ℕ) :
    ((PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j : ℤ) : ℝ) = X.Conclusion₂ v j := by
  simp only [Sys.Conclusion₂, PrZ, Pr]
  push_cast
  congr 1
  obtain ⟨k, hk⟩ := (X.G.P.setting v).even
  rw [hk]
  have h2 : ((k + k : ℕ) : ℤ) / 2 = (k : ℤ) := by omega
  rw [h2]
  push_cast
  ring

/- English proof (translation)
Introduce `Gn G0n PRn S VV hG hLow hPr hS F hF`. Use `choose u m hu hm hrest using h4`. Establish `hπ : (algebraMap X.G.O X.G.Kf X.vp) ≠ 0`. Introduce `h0`. Conclude with `X.unif.ne_zero ((IsFractionRing.injective X.G.O X.G.Kf) (h0.trans (map_zero _).symm))`.

Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨BB, hBB, Lv, hnd, hLv, F0, hF0, rfl⟩` from `hx`. Take `⟨F1, hF1, rfl⟩` from `hF0`. Set `Q : ℕ → X.Pl → Bool` to `fun j v => decide (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))`.

Establish `hmemL : ∀ v, v ∈ Lv ↔ v ∈ BB` using `fun v => by rw [← hLv, List.mem_toFinset]`. Establish `h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1)` using `fun v hv j hj => hG v (hBB ((hmemL v).1 hv)) (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)`. Establish `hmi` using `main_ind hfr hp hL hF hE u m hu (fun v j hj => (hrest v j hj).2.1) (fun v j hj => (hrest v j hj).2.2.1) (fun v j hj => (hrest v j hj).1) hy Lv hnd Gn G0n Q h1 hLow X.mm le_rfl F1 hF1`. Establish `hnum : (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) - ∑ j ∈ range X.mm, (X.dG j : ℝ)) ≤ ∑ v ∈ VV \ BB, S v + ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j`. Rewrite using `[sum_Icc_shift]`.

Establish `hb` using `basic₂ X.mm VV BB hBB Gn G0n PRn (fun v j => X.Conclusion₂ v j) S (fun j => (X.dG j : ℝ)) (fun j v => v ∈ Lv.filter (Q j)) (fun j v => by simp only [List.mem_filter, hmemL, Q, decide_eq_true_eq]) (fun v hv j hj => hPr v hv (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)) (fun v h …`. Use `hb.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [bbJ, PrS]`.

Move the coercions through the operations in `[PrZ_cast]`. Both sides reduce to the same expression. Unfold `Sys.vGe scale at hmi ⊢`. Take `⟨I, hI, hIeq⟩` from `hmi`. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hIeq ⊢`.

Rewrite using `[fold_eq hL]`. Use `set g := ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j with hg`. Use `set T : ℝ := (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) - ∑ j ∈ range X.mm, (X.dG j : ℝ)) with hT`. Establish `hceil : ⌈T * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉`. Rewrite using `[Int.ceil_le]`.

Use `push_cast`. Establish `h8 : (0 : ℝ) ≤ (X.eO : ℝ)` using `Nat.cast_nonneg _`. Establish `h6 : (∑ v ∈ VV \ BB, S v) * (X.eO : ℝ) ≤ ∑ v ∈ VV \ BB, (⌈S v * (X.eO : ℝ)⌉ : ℝ)`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun v _ => Int.le_ceil _`.

Establish `h7` using `Int.le_ceil (g * (X.eO : ℝ))`. Establish `h9` using `mul_le_mul_of_nonneg_right hnum h8`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ - ⌈T * (X.eO : ℝ)⌉` from `⟨_, Int.toNat_of_nonneg (by omega)⟩`. Use `⟨X.vp ^ n • I, Submodule.smul_mem _ _ hI, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]`. Rewrite using `[map_smul, map_smul, ← hIeq, ← algebraMap_smul X.G.Kf (X.vp ^ n) I, smul_smul, smul_smul]`. Use `congr 1`. Unfold `Sys.vsc`. Rewrite using `[map_pow, ← zpow_natCast, ← zpow_add₀ hπ, ← zpow_add₀ hπ, hn]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Unfold `Sys.vGe`. Rewrite using `[map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Unfold `Sys.vGe at *`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx`. Unfold `Sys.vGe at *`. Rewrite using `[← algebraMap_smul X.G.Kf a x, map_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem lift_bound_of_integrality (D : Formalism.BasicNotions.D7) {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0)
    (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y) (h4 : Conclusion4 D X)
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV hG hLow hPr hS F hF
  choose u m hu hm hrest using h4
  have hπ : (algebraMap X.G.O X.G.Kf X.vp) ≠ 0 := by
    intro h0
    exact X.unif.ne_zero ((IsFractionRing.injective X.G.O X.G.Kf) (h0.trans (map_zero _).symm))
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨BB, hBB, Lv, hnd, hLv, F0, hF0, rfl⟩ := hx
    obtain ⟨F1, hF1, rfl⟩ := hF0
    let Q : ℕ → X.Pl → Bool := fun j v => decide (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    have hmemL : ∀ v, v ∈ Lv ↔ v ∈ BB := fun v => by rw [← hLv, List.mem_toFinset]
    have h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1) := fun v hv j hj =>
      hG v (hBB ((hmemL v).1 hv)) (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hmi := main_ind hfr hp hL hF hE u m hu (fun v j hj => (hrest v j hj).2.1)
      (fun v j hj => (hrest v j hj).2.2.1) (fun v j hj => (hrest v j hj).1) hy Lv hnd Gn G0n Q h1 hLow
      X.mm le_rfl F1 hF1
    have hnum : (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) ≤ ∑ v ∈ VV \ BB, S v + ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j := by
      rw [sum_Icc_shift]
      have hb := basic₂ X.mm VV BB hBB Gn G0n PRn (fun v j => X.Conclusion₂ v j) S (fun j => (X.dG j : ℝ))
        (fun j v => v ∈ Lv.filter (Q j))
        (fun j v => by simp only [List.mem_filter, hmemL, Q, decide_eq_true_eq])
        (fun v hv j hj => hPr v hv (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
        (fun v hv => by rw [← sum_Icc_shift (fun j => max (Gn v j - PRn v j - G0n v j) 0)]; exact hS v hv)
      refine hb.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bbJ, PrS]
      push_cast [PrZ_cast]
      rfl
    unfold Sys.vGe scale at hmi ⊢
    obtain ⟨I, hI, hIeq⟩ := hmi
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hIeq ⊢
    rw [fold_eq hL]
    set g := ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j with hg
    set T : ℝ := (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) with hT
    have hceil : ⌈T * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ := by
      rw [Int.ceil_le]
      push_cast
      have h8 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
      have h6 : (∑ v ∈ VV \ BB, S v) * (X.eO : ℝ) ≤ ∑ v ∈ VV \ BB, (⌈S v * (X.eO : ℝ)⌉ : ℝ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => Int.le_ceil _
      have h7 := Int.le_ceil (g * (X.eO : ℝ))
      have h9 := mul_le_mul_of_nonneg_right hnum h8
      nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ - ⌈T * (X.eO : ℝ)⌉ :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨X.vp ^ n • I, Submodule.smul_mem _ _ hI, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [map_smul, map_smul, ← hIeq, ← algebraMap_smul X.G.Kf (X.vp ^ n) I, smul_smul, smul_smul]
    congr 1
    unfold Sys.vsc
    rw [map_pow, ← zpow_natCast, ← zpow_add₀ hπ, ← zpow_add₀ hπ, hn]
    congr 1
    ring
  | zero =>
    unfold Sys.vGe
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    unfold Sys.vGe at *
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    unfold Sys.vGe at *
    rw [← algebraMap_smul X.G.Kf a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
