import Formalism.GaussJetBounds.OneLetterGaussJets.StatementA
import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

/- English proof (translation)
Apply `Set.Finite.bddAbove` to reduce the goal to its premises. Apply `(Set.finite_range (fun t : ZMod d => capL d TT nu1 nu2 t)).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, _, rfl⟩`. Conclude with `⟨_, rfl⟩`.
-/
theorem cap_values_bddAbove (d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d)
    (I : Set ℕ) : BddAbove ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) '' I) := by
  apply Set.Finite.bddAbove
  apply (Set.finite_range (fun t : ZMod d => capL d TT nu1 nu2 t)).subset
  rintro _ ⟨i, _, rfl⟩
  exact ⟨_, rfl⟩

/- English proof (translation)
Establish `hc : (((-j).toNat : ℕ) : ZMod d) = -((j : ZMod d))`. Establish `: (((-j).toNat : ℕ) : ℤ) = -j` using `Int.toNat_of_nonneg (by omega)`. Rewrite using `[← Int.cast_natCast, this, Int.cast_neg]`. Establish `hs : s - (((-j).toNat : ℕ) : ZMod d) = s + (j : ZMod d)`. Rewrite using `[hc, sub_neg_eq_add]`.

Unfold `WcapOneLetter`. Apply `le_csSup (cap_values_bddAbove d TT nu1 nu2 s _)` to reduce the goal to its premises. Use `⟨(-j).toNat, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hodd`. Conclude with `⟨(-k - 1).toNat, by omega⟩`.

Rewrite using `[hs]`. Conclude with `hsz`. Simplify using `only`. Rewrite using `[hs]`.
-/
theorem cap_le_odd_shift_bound (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
    (s : ZMod d) (j : ℤ) (hj : j < 0) (hodd : Odd j)
    (hsz : l ^ (-j).toNat ≤ Dl d TT nu1 size (s + (j : ZMod d))) :
    capL d TT nu1 nu2 (s + (j : ZMod d)) ≤ WcapOneLetter l d TT nu1 nu2 size s := by
  have hc : (((-j).toNat : ℕ) : ZMod d) = -((j : ZMod d)) := by
    have : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    rw [← Int.cast_natCast, this, Int.cast_neg]
  have hs : s - (((-j).toNat : ℕ) : ZMod d) = s + (j : ZMod d) := by
    rw [hc, sub_neg_eq_add]
  unfold WcapOneLetter
  apply le_csSup (cap_values_bddAbove d TT nu1 nu2 s _)
  refine ⟨(-j).toNat, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := hodd
    exact ⟨(-k - 1).toNat, by omega⟩
  · rw [hs]
    exact hsz
  · simp only
    rw [hs]

/- English proof (translation)
Introduce `l d _ hl hd hde TT nu1 nu2 size h21 h1s sig hopt ι _ lt isTop spec κ htop htopsum hDsum hspec hcapsum`. Establish `hl2 : 2 ≤ l` using `by omega`. Establish `hsig : ∀ s, 0 ≤ sig s` using `fun s => (hopt.1.1 s).1`. Use `set Q : Finset (ZMod d × ℤ) := Finset.univ.biUnion (fun i => (spec i).toFinset) with hQdef`. Establish `hQ : ∀ q ∈ Q, ∃ i, spec i = some q`.

Introduce `q hq`. Rewrite `hq` using `[hQdef, Finset.mem_biUnion]`. Take `⟨i, _, hi⟩` from `hq`. Conclude with `⟨i, Option.mem_toFinset.1 hi⟩`. Establish `hQmem : ∀ i q, spec i = some q → q ∈ Q`.

Introduce `i q hi`. Rewrite using `[hQdef, Finset.mem_biUnion]`. Conclude with `⟨i, Finset.mem_univ _, Option.mem_toFinset.2 hi⟩`. Establish `hQspec : ∀ q ∈ Q, q.1 ∈ TT ∧ Odd q.2 ∧ (q.2 < 0 → l ^ (-q.2).toNat ≤ Dl d TT nu1 size (q.1 + (q.2 : ZMod d)))`. Introduce `q hq`.

Take `⟨i, hi⟩` from `hQ q hq`. Take `⟨h1, h2, h3, _, h5⟩` from `hspec i q.1 q.2 hi`. Use `⟨h1, h2, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[← h3]`. Conclude with `h5 h`.

Use `set R : ZMod d → Finset ℕ := fun s => (Q.filter (fun q => q.1 = s ∧ 0 < q.2)).image (fun q => q.2.toNat) with hRdef`. Establish `hRs : ∀ s, R s = (Q.filter (fun q => q.1 = s ∧ 0 < q.2)).image (fun q => q.2.toNat)` using `fun s => rfl`. Establish `hRodd : ∀ s, ∀ j ∈ R s, Odd j`. Introduce `s j hj`. Rewrite `hj` using `[hRs, Finset.mem_image]`.

Take `⟨q, hq, rfl⟩` from `hj`. Rewrite `hq` using `[Finset.mem_filter]`. Take `⟨hqQ, _, hpos⟩` from `hq`. Take `⟨k, hk⟩` from `(hQspec q hqQ).2.1`. Conclude with `⟨k.toNat, by omega⟩`.

Establish `hch` using `fun s => asmA_top l d hl2 TT nu1 nu2 s (R s) (hRodd s)`. Use `choose eps heps0 hepsD hepsT using hch`. Use `⟨eps, heps0, fun s _ e he => hepsD s e he, ?_⟩` and prove the remaining obligations. Establish `hrow : ∀ i, (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i)) else (κ i : ℝ) * (gam l - sig (lt i))) - (κ i : ℝ) * asmA_cost l eps (spec i) ≤ (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)` using `fun i => asmA_row l sig eps hsig lt isTop spec κ i (fun h => (htop i h).2)`. Establish `hsum1 : (∑ i, (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i)) else (κ i : ℝ) * (gam l - sig (lt i)))) - ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) ≤ ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)`.

Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_le_sum (fun i _ => hrow i)`. Rewrite `hsum1` using `[Finset.sum_ite]`. Establish `hT : ∑ i ∈ Finset.univ.filter (fun i => isTop i = true), (κ i : ℝ) * (gam l - eps (lt i)) = ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := lt) (t := TT) (fun i hi => (htop i (Finset.mem_filter.1 hi).2).1)]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s hs`. Rewrite using `[← htopsum s hs, Finset.sum_mul, Finset.filter_filter]`. Apply `Finset.sum_congr (by ext i; simp [and_comm])` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[(Finset.mem_filter.1 hi).2.1]`. Establish `hF : ∑ i ∈ Finset.univ.filter (fun i => ¬ isTop i = true), (κ i : ℝ) * (gam l - sig (lt i)) = Fnum l d (fun s => (Dl d TT nu1 size s : ℝ))`. Establish `hF' : Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) = ∑ s : ZMod d, (Dl d TT nu1 size s : ℝ) * (gam l - sig s)` using `hopt.2`. Rewrite using `[hF', ← Finset.sum_fiberwise_of_maps_to (g := lt) (t := Finset.univ) (fun i _ => Finset.mem_univ _)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `s _`. Rewrite using `[← hDsum s, Finset.sum_mul, Finset.filter_filter]`. Apply `Finset.sum_congr (by ext i; simp [and_comm])` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[(Finset.mem_filter.1 hi).2.1]`.

Establish `hC1 : ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) = ∑ q ∈ Q, (∑ i ∈ Finset.univ.filter (fun i => spec i = some (q.1, q.2)), (κ i : ℝ)) * asmA_cost l eps (some q)`. Establish `hpt : ∀ i, (κ i : ℝ) * asmA_cost l eps (spec i) = ∑ q ∈ Q, if spec i = some (q.1, q.2) then (κ i : ℝ) * asmA_cost l eps (some q) else 0`. Introduce `i`. Consider the cases of `hs : spec i with`. Consider the case `none => simp [asmA_cost]`.

Consider the case `some q0`. Rewrite using `[Finset.sum_eq_single q0]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hb` to reduce the goal to its premises. Simplify using `only [Option.some.injEq] at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Introduce `h`. Conclude with `absurd (hQmem i q0 hs) h`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q _`.

Rewrite using `[Finset.sum_mul, Finset.sum_filter]`. Establish `hC2 : ∑ q ∈ Q, (∑ i ∈ Finset.univ.filter (fun i => spec i = some (q.1, q.2)), (κ i : ℝ)) * asmA_cost l eps (some q) ≤ ∑ q ∈ Q, (capL d TT nu1 nu2 (q.1 + (q.2 : ZMod d)) : ℝ) * asmA_cost l eps (some q)` using `Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right (hcapsum q.1 q.2) (asmA_cost_nonneg l eps _))`. Establish `hC3 : ∑ q ∈ Q, (capL d TT nu1 nu2 (q.1 + (q.2 : ZMod d)) : ℝ) * asmA_cost l eps (some q) ≤ ∑ s ∈ TT, ((∑ j ∈ R s, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0) + gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := TT) (fun q hq => (hQspec q hq).1)]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `s hs`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not _ (fun q => 0 < q.2)]`. Apply `add_le_add` to reduce the goal to its premises. Apply `le_of_eq` to reduce the goal to its premises. Rewrite using `[hRs s, Finset.sum_image]`.

Rewrite using `[Finset.filter_filter]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce and unpack `⟨s', j⟩ hq`. Simplify using `only [Finset.mem_filter] at hq`. Take `⟨_, rfl, hj⟩` from `hq`.

Establish `hc : ((j.toNat : ℕ) : ZMod d) = (j : ZMod d)`. Establish `: ((j.toNat : ℕ) : ℤ) = j` using `Int.toNat_of_nonneg hj.le`. Rewrite using `[← Int.cast_natCast, this]`. Simplify using `[asmA_cost, hj, hc]`. Introduce `x hx y hy hxy`.

Simplify using `only [Finset.mem_coe, Finset.mem_filter] at hx hy`. Conclude with `Prod.ext (hx.2.1.trans hy.2.1.symm) (by simp only at hxy; omega)`. Use `set S' := (Q.filter (fun q => q.1 = s)).filter (fun q => ¬ 0 < q.2) with hS'`. Establish `hmemS : ∀ q ∈ S', q ∈ Q ∧ q.1 = s ∧ q.2 < 0`. Introduce `q hq`.

Rewrite `hq` using `[hS', Finset.mem_filter, Finset.mem_filter]`. Take `⟨⟨hqQ, hq1⟩, hq2⟩` from `hq`. Take `⟨k, hk⟩` from `(hQspec q hqQ).2.1`. Conclude with `⟨hqQ, hq1, by omega⟩`. Establish `hb1 : ∑ q ∈ S', (capL d TT nu1 nu2 (q.1 + (q.2 : ZMod d)) : ℝ) * asmA_cost l eps (some q) ≤ ∑ q ∈ S', (WcapOneLetter l d TT nu1 nu2 size s : ℝ) * ((l : ℝ) ^ (-q.2).toNat)⁻¹`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce and unpack `⟨s', j⟩ hq`. Take `⟨hqQ, hq1, hj⟩` from `hmemS _ hq`. Simplify using `only at hq1 hj`. Establish `hcost : asmA_cost l eps (some (s', j)) = ((l : ℝ) ^ (-j).toNat)⁻¹`.

Simplify using `[asmA_cost, not_lt.2 hj.le]`. Rewrite using `[hcost, ← hq1]`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Use `cap_le_odd_shift_bound l d TT nu1 nu2 size s' j hj (hQspec _ hqQ).2.1 ((hQspec _ hqQ).2.2 hj)` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hinj : ∀ x ∈ S', ∀ y ∈ S', (-x.2).toNat = (-y.2).toNat → x = y`. Introduce `x hx y hy hxy`. Take `⟨_, hx1, hx2⟩` from `hmemS x hx`. Take `⟨_, hy1, hy2⟩` from `hmemS y hy`. Conclude with `Prod.ext (hx1.trans hy1.symm) (by omega)`.

Establish `hb2 : ∑ q ∈ S', ((l : ℝ) ^ (-q.2).toNat)⁻¹ ≤ gam l`. Rewrite using `[← Finset.sum_image (f := fun n : ℕ => ((l : ℝ) ^ n)⁻¹) (g := fun q : ZMod d × ℤ => (-q.2).toNat) hinj]`. Apply `asmA_sum_odd_le l hl2` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_image]`.

Take `⟨q, hq, rfl⟩` from `hn`. Take `⟨hqQ, _, hq2⟩` from `hmemS q hq`. Take `⟨k, hk⟩` from `(hQspec q hqQ).2.1`. Conclude with `⟨(-k - 1).toNat, by omega⟩`. Rewrite `hb1` using `[← Finset.mul_sum]`.

Establish `hW0 : (0 : ℝ) ≤ (WcapOneLetter l d TT nu1 nu2 size s : ℝ)` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Establish `hkey : ∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) ≤ ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) - ∑ s ∈ TT, ((∑ j ∈ R s, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0) + gam l * (WcapOneLetter l d TT nu1 nu2 …`. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `s _`. Use `hepsT s` as an intermediate fact. Combine the linear relations using `[mul_sub (nu1 s : ℝ) (gam l) (eps s)]`. Combine the linear relations using `[hT, hF, hC1, hC2, hC3, hkey, hsum1]`.
-/
theorem gauss_jet_bound_of_parts : ThmAAssembly7 := by
  intro l d _ hl hd hde TT nu1 nu2 size h21 h1s sig hopt ι _ lt isTop spec κ htop htopsum hDsum
    hspec hcapsum
  classical
  have hl2 : 2 ≤ l := by omega
  have hsig : ∀ s, 0 ≤ sig s := fun s => (hopt.1.1 s).1
  set Q : Finset (ZMod d × ℤ) := Finset.univ.biUnion (fun i => (spec i).toFinset) with hQdef
  have hQ : ∀ q ∈ Q, ∃ i, spec i = some q := by
    intro q hq
    rw [hQdef, Finset.mem_biUnion] at hq
    obtain ⟨i, _, hi⟩ := hq
    exact ⟨i, Option.mem_toFinset.1 hi⟩
  have hQmem : ∀ i q, spec i = some q → q ∈ Q := by
    intro i q hi
    rw [hQdef, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, Option.mem_toFinset.2 hi⟩
  have hQspec : ∀ q ∈ Q, q.1 ∈ TT ∧ Odd q.2 ∧
      (q.2 < 0 → l ^ (-q.2).toNat ≤ Dl d TT nu1 size (q.1 + (q.2 : ZMod d))) := by
    intro q hq
    obtain ⟨i, hi⟩ := hQ q hq
    obtain ⟨h1, h2, h3, _, h5⟩ := hspec i q.1 q.2 hi
    refine ⟨h1, h2, fun h => ?_⟩
    rw [← h3]
    exact h5 h
  set R : ZMod d → Finset ℕ := fun s =>
    (Q.filter (fun q => q.1 = s ∧ 0 < q.2)).image (fun q => q.2.toNat) with hRdef
  have hRs : ∀ s, R s = (Q.filter (fun q => q.1 = s ∧ 0 < q.2)).image (fun q => q.2.toNat) :=
    fun s => rfl
  have hRodd : ∀ s, ∀ j ∈ R s, Odd j := by
    intro s j hj
    rw [hRs, Finset.mem_image] at hj
    obtain ⟨q, hq, rfl⟩ := hj
    rw [Finset.mem_filter] at hq
    obtain ⟨hqQ, _, hpos⟩ := hq
    obtain ⟨k, hk⟩ := (hQspec q hqQ).2.1
    exact ⟨k.toNat, by omega⟩
  have hch := fun s => asmA_top l d hl2 TT nu1 nu2 s (R s) (hRodd s)
  choose eps heps0 hepsD hepsT using hch
  refine ⟨eps, heps0, fun s _ e he => hepsD s e he, ?_⟩

  have hrow : ∀ i, (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i))) - (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) :=
    fun i => asmA_row l sig eps hsig lt isTop spec κ i (fun h => (htop i h).2)
  have hsum1 : (∑ i, (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i)))) - ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => hrow i)
  rw [Finset.sum_ite] at hsum1

  have hT : ∑ i ∈ Finset.univ.filter (fun i => isTop i = true), (κ i : ℝ) * (gam l - eps (lt i)) =
      ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := lt) (t := TT)
      (fun i hi => (htop i (Finset.mem_filter.1 hi).2).1)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← htopsum s hs, Finset.sum_mul, Finset.filter_filter]
    apply Finset.sum_congr (by ext i; simp [and_comm])
    intro i hi
    rw [(Finset.mem_filter.1 hi).2.1]

  have hF : ∑ i ∈ Finset.univ.filter (fun i => ¬ isTop i = true),
      (κ i : ℝ) * (gam l - sig (lt i)) = Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) := by
    have hF' : Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) =
        ∑ s : ZMod d, (Dl d TT nu1 size s : ℝ) * (gam l - sig s) := hopt.2
    rw [hF', ← Finset.sum_fiberwise_of_maps_to (g := lt) (t := Finset.univ)
      (fun i _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro s _
    rw [← hDsum s, Finset.sum_mul, Finset.filter_filter]
    apply Finset.sum_congr (by ext i; simp [and_comm])
    intro i hi
    rw [(Finset.mem_filter.1 hi).2.1]

  have hC1 : ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) =
      ∑ q ∈ Q, (∑ i ∈ Finset.univ.filter (fun i => spec i = some (q.1, q.2)), (κ i : ℝ)) *
        asmA_cost l eps (some q) := by
    have hpt : ∀ i, (κ i : ℝ) * asmA_cost l eps (spec i) =
        ∑ q ∈ Q, if spec i = some (q.1, q.2) then (κ i : ℝ) * asmA_cost l eps (some q)
          else 0 := by
      intro i
      cases hs : spec i with
      | none => simp [asmA_cost]
      | some q0 =>
        rw [Finset.sum_eq_single q0]
        · simp
        · intro b _ hb
          rw [if_neg]
          intro h
          apply hb
          simp only [Option.some.injEq] at h
          subst h
          rfl
        · intro h
          exact absurd (hQmem i q0 hs) h
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_mul, Finset.sum_filter]
  have hC2 : ∑ q ∈ Q, (∑ i ∈ Finset.univ.filter (fun i => spec i = some (q.1, q.2)), (κ i : ℝ)) *
        asmA_cost l eps (some q) ≤
      ∑ q ∈ Q, (capL d TT nu1 nu2 (q.1 + (q.2 : ZMod d)) : ℝ) * asmA_cost l eps (some q) :=
    Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right (hcapsum q.1 q.2)
      (asmA_cost_nonneg l eps _))
  have hC3 : ∑ q ∈ Q, (capL d TT nu1 nu2 (q.1 + (q.2 : ZMod d)) : ℝ) * asmA_cost l eps (some q) ≤
      ∑ s ∈ TT, ((∑ j ∈ R s, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) *
        max (1 - (l : ℝ) ^ j * eps s) 0) + gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := TT)
      (fun q hq => (hQspec q hq).1)]
    apply Finset.sum_le_sum
    intro s hs
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun q => 0 < q.2)]
    apply add_le_add
    ·
      apply le_of_eq
      rw [hRs s, Finset.sum_image]
      · rw [Finset.filter_filter]
        apply Finset.sum_congr rfl
        rintro ⟨s', j⟩ hq
        simp only [Finset.mem_filter] at hq
        obtain ⟨_, rfl, hj⟩ := hq
        have hc : ((j.toNat : ℕ) : ZMod d) = (j : ZMod d) := by
          have : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj.le
          rw [← Int.cast_natCast, this]
        simp [asmA_cost, hj, hc]
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
        exact Prod.ext (hx.2.1.trans hy.2.1.symm) (by simp only at hxy; omega)
    ·
      set S' := (Q.filter (fun q => q.1 = s)).filter (fun q => ¬ 0 < q.2) with hS'
      have hmemS : ∀ q ∈ S', q ∈ Q ∧ q.1 = s ∧ q.2 < 0 := by
        intro q hq
        rw [hS', Finset.mem_filter, Finset.mem_filter] at hq
        obtain ⟨⟨hqQ, hq1⟩, hq2⟩ := hq
        obtain ⟨k, hk⟩ := (hQspec q hqQ).2.1
        exact ⟨hqQ, hq1, by omega⟩
      have hb1 : ∑ q ∈ S', (capL d TT nu1 nu2 (q.1 + (q.2 : ZMod d)) : ℝ) *
            asmA_cost l eps (some q) ≤
          ∑ q ∈ S', (WcapOneLetter l d TT nu1 nu2 size s : ℝ) * ((l : ℝ) ^ (-q.2).toNat)⁻¹ := by
        apply Finset.sum_le_sum
        rintro ⟨s', j⟩ hq
        obtain ⟨hqQ, hq1, hj⟩ := hmemS _ hq
        simp only at hq1 hj
        have hcost : asmA_cost l eps (some (s', j)) = ((l : ℝ) ^ (-j).toNat)⁻¹ := by
          simp [asmA_cost, not_lt.2 hj.le]
        rw [hcost, ← hq1]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := cap_le_odd_shift_bound l d TT nu1 nu2 size s' j hj (hQspec _ hqQ).2.1
          ((hQspec _ hqQ).2.2 hj)
        exact_mod_cast this
      have hinj : ∀ x ∈ S', ∀ y ∈ S', (-x.2).toNat = (-y.2).toNat → x = y := by
        intro x hx y hy hxy
        obtain ⟨_, hx1, hx2⟩ := hmemS x hx
        obtain ⟨_, hy1, hy2⟩ := hmemS y hy
        exact Prod.ext (hx1.trans hy1.symm) (by omega)
      have hb2 : ∑ q ∈ S', ((l : ℝ) ^ (-q.2).toNat)⁻¹ ≤ gam l := by
        rw [← Finset.sum_image (f := fun n : ℕ => ((l : ℝ) ^ n)⁻¹)
          (g := fun q : ZMod d × ℤ => (-q.2).toNat) hinj]
        apply asmA_sum_odd_le l hl2
        intro n hn
        rw [Finset.mem_image] at hn
        obtain ⟨q, hq, rfl⟩ := hn
        obtain ⟨hqQ, _, hq2⟩ := hmemS q hq
        obtain ⟨k, hk⟩ := (hQspec q hqQ).2.1
        exact ⟨(-k - 1).toNat, by omega⟩
      rw [← Finset.mul_sum] at hb1
      have hW0 : (0 : ℝ) ≤ (WcapOneLetter l d TT nu1 nu2 size s : ℝ) := Nat.cast_nonneg _
      calc _ ≤ _ := hb1
        _ ≤ (WcapOneLetter l d TT nu1 nu2 size s : ℝ) * gam l := mul_le_mul_of_nonneg_left hb2 hW0
        _ = gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ) := mul_comm _ _
  have hkey : ∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) ≤
      ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) -
        ∑ s ∈ TT, ((∑ j ∈ R s, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) *
          max (1 - (l : ℝ) ^ j * eps s) 0) + gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro s _
    have := hepsT s
    linarith [mul_sub (nu1 s : ℝ) (gam l) (eps s)]
  linarith [hT, hF, hC1, hC2, hC3, hkey, hsum1]

/- English proof (translation)
Introduce `l d _ hl TT nu1 size s`. Use `set M : ℕ := Finset.univ.sup nu1 + Dl d TT nu1 size s with hM`. Apply `((Set.finite_univ (α := ZMod d)).prod (Set.finite_Icc (-(M : ℤ)) (M : ℤ))).subset` to reduce the goal to its premises. Introduce and unpack `⟨s0, j⟩ ⟨_, _, _, hp, hn⟩`. Simplify using `only at hp hn`.

Use `⟨Set.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Use `show -(M : ℤ) ≤ j`. Distinguish the cases in `hj : j < 0`. Establish `h1` using `hn hj`. Establish `h2 : (-j).toNat < l ^ (-j).toNat` using `Nat.lt_pow_self (by omega)`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use `show j ≤ (M : ℤ)`. Distinguish the cases in `hj : 0 < j`. Establish `h1` using `hp hj`.

Establish `h2 : j.toNat < l ^ j.toNat` using `Nat.lt_pow_self (by omega)`. Establish `h3 : nu1 s0 ≤ Finset.univ.sup nu1` using `Finset.le_sup (f := nu1) (Finset.mem_univ s0)`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem letter_labels_finite : LabFinite7 := by
  intro l d _ hl TT nu1 size s
  set M : ℕ := Finset.univ.sup nu1 + Dl d TT nu1 size s with hM
  apply ((Set.finite_univ (α := ZMod d)).prod (Set.finite_Icc (-(M : ℤ)) (M : ℤ))).subset
  rintro ⟨s0, j⟩ ⟨_, _, _, hp, hn⟩
  simp only at hp hn
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · show -(M : ℤ) ≤ j
    by_cases hj : j < 0
    · have h1 := hn hj
      have h2 : (-j).toNat < l ^ (-j).toNat := Nat.lt_pow_self (by omega)
      omega
    · omega
  · show j ≤ (M : ℤ)
    by_cases hj : 0 < j
    · have h1 := hp hj
      have h2 : j.toNat < l ^ j.toNat := Nat.lt_pow_self (by omega)
      have h3 : nu1 s0 ≤ Finset.univ.sup nu1 := Finset.le_sup (f := nu1) (Finset.mem_univ s0)
      omega
    · omega

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
