import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCutIntoBoundedGroupsFinset
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV
open scoped BigOperators

namespace GlobalTheory.GoodDepth.Zero

/- English proof (translation)
Distinguish the cases in `h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B`. Take `⟨pc, h1, h2, h3⟩` from `GlobalTheory.exists_cut_columns_bounded_width K s B e h`. Use `⟨pc, h2, fun _ hsupp k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ Finset.Icc 1 K`. Conclude with `h1 k hk`.

Establish `hek : e k = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hk (Finset.mem_Icc.mpr (hsupp k hne))`. Rewrite using `[hek]`. Conclude with `Finset.sum_eq_zero fun u _ => h3 u k hk`.

Conclude with `⟨fun _ _ => 0, fun _ => by simp, fun h' => absurd h' h⟩`.
-/
theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hsupp k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have hek : e k = 0 := by
        by_contra hne
        exact hk (Finset.mem_Icc.mpr (hsupp k hne))
      rw [hek]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, fun _ => by simp, fun h' => absurd h' h⟩

/- English proof (translation)
Unfold `monAl`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `k hk`. Simplify using `only [Finset.mem_Icc] at hk ⊢`. Conclude with `⟨by omega, hk.2.trans (min_le_left _ _)⟩`.
-/
theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_Icc] at hk ⊢
  exact ⟨by omega, hk.2.trans (min_le_left _ _)⟩

/- English proof (translation)
Break down `Nat.eq_zero_or_pos l with hl | hl` into its components or cases. Establish `hz : ∀ z ∈ Pk.Z, ∀ g a k, Pk.ga z g a k = 0`. Introduce `z hz g a k`. Assume the negation of the conclusion as `hne`. Establish `hs` using `Pk.supp z hz g a k hne`.

Establish `h0 : Pk.s * (l - 1) = 0` using `by simp [hl]`. Establish `hf` using `(Pk.first z hz g a).trans h0.le`. Conclude with `hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))`. Establish `h` using `Pk.val (fun _ => []) (by simp) (by simp) (by intro o ho g a k; simp [hz o ho g a k])`. Simplify using `using h`.

Establish `hcut : ∀ z g a, ∃ pc : Fin Pk.s → ℕ → ℕ, (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧ (z ∈ Pk.Z → ∀ k, ∑ u, pc u k = Pk.ga z g a k)`. Introduce `z g a`. Take `⟨pc, h1, h2⟩` from `cut Pk.K Pk.s (l - 1) (Pk.ga z g a)`. Conclude with `⟨pc, h1, fun hz => h2 (Pk.first z hz g a) fun k hk => ⟨(Pk.supp z hz g a k hk).1, (Pk.supp z hz g a k hk).2.2⟩⟩`. Use `choose pc hpc1 hpc2 using hcut`.

Set `blk : P.Pl → Fin 2 × Fin Pk.s → RF.GlobalTheory P.d × ℝ` to `fun z q => (RF.GlobalTheory.mon q.1 (fun a => pc z q.1 a q.2) Pk.K, 0)`. Set `L : P.Pl → List (RF.GlobalTheory P.d × ℝ)` to `fun z => (Finset.univ : Finset (Fin 2 × Fin Pk.s)).toList.map (blk z)`. Establish `hsum0 : ∑ o ∈ Pk.Z, ((L o).map Prod.snd).sum = 0`. Simplify using `[L, blk]`. Use `(Pk.val L ?_ ?_ ?_).trans hsum0.le` and prove the remaining obligations.

Introduce `o _ p hp`. Simplify using `only [L, List.mem_map, Finset.mem_toList] at hp`. Take `⟨q, -, rfl⟩` from `hp`. Use `(hM Pk.R.C Pk.R.V P.d (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) q.1 (fun a => pc o q.1 a q.2) Pk.K).2 ?_` and prove the remaining obligations. Introduce `a ρ`.

Rewrite using `[Pk.R.hVl]`. Establish `h1` using `(monAl_le_first Pk.K ((Pk.R.X o).rkF q.1 a) (pc o q.1 a q.2) ρ).trans (hpc1 o q.1 a q.2)`. Use linear arithmetic over natural numbers and integers. Establish `hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K`. Introduce `o`.

Simplify using `only [L, List.map_map]`. Rewrite using `[Finset.sum_map_toList]`. Simplify using `[blk, RF.GlobalTheory.what₂]`. Rewrite using `[Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Introduce `o ho g a k`. Establish `hw : ∀ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k = if q.1 = g then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0) else 0`. Introduce and unpack `⟨g', u⟩`. Distinguish the cases in `hg : g' = g`. Substitute `hg` using the available equality.

Simplify using `[blk, RF.GlobalTheory.wt]`. Simplify using `[blk, RF.GlobalTheory.wt, hg, Ne.symm hg]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [L, List.map_map]`. Rewrite using `[Finset.sum_map_toList]`.

Both sides reduce to the same expression. Use `_ = ∑ q : Fin 2 × Fin Pk.s, if q.1 = g then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0) else 0 := Finset.sum_congr rfl fun q _ => hw q`. Use `_ = ∑ u : Fin Pk.s, (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a u k else 0) := by`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single g]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Use `_ = Pk.ga o g a k := by`. Distinguish the cases in `hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a)`.

Simplify using `only [if_pos hk]`. Conclude with `hpc2 o g a ho k`. Simplify using `only [if_neg hk, Finset.sum_const_zero]`. Use `symm`. Assume the negation of the conclusion as `hne`.

Establish `hs` using `Pk.supp o ho g a k hne`. Conclude with `hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩`.
-/
theorem zero_of_pkg (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZero P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z ∈ Pk.Z, ∀ g a k, Pk.ga z g a k = 0 := by
      intro z hz g a k
      by_contra hne
      have hs := Pk.supp z hz g a k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z hz g a).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp)
      (by intro o ho g a k; simp [hz o ho g a k])
    simpa using h
  · have hcut : ∀ z g a, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧
        (z ∈ Pk.Z → ∀ k, ∑ u, pc u k = Pk.ga z g a k) := by
      intro z g a
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.ga z g a)
      exact ⟨pc, h1, fun hz => h2 (Pk.first z hz g a)
        fun k hk => ⟨(Pk.supp z hz g a k hk).1, (Pk.supp z hz g a k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let blk : P.Pl → Fin 2 × Fin Pk.s → RF.GlobalTheory P.d × ℝ :=
      fun z q => (RF.GlobalTheory.mon q.1 (fun a => pc z q.1 a q.2) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory P.d × ℝ) :=
      fun z => (Finset.univ : Finset (Fin 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o ∈ Pk.Z, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_).trans hsum0.le
    · intro o _ p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V P.d (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) q.1
        (fun a => pc o q.1 a q.2) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 := (monAl_le_first Pk.K ((Pk.R.X o).rkF q.1 a) (pc o q.1 a q.2) ρ).trans (hpc1 o q.1 a q.2)
      omega
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul]
      calc Pk.Z.card * (2 * Pk.s * Pk.K) = 2 * Pk.K * Pk.s * Pk.Z.card := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o ho g a k
      have hw : ∀ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k =
          if q.1 = g then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0)
          else 0 := by
        rintro ⟨g', u⟩
        by_cases hg : g' = g
        · subst hg
          simp [blk, RF.GlobalTheory.wt]
        · simp [blk, RF.GlobalTheory.wt, hg, Ne.symm hg]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) g a k).sum
          = ∑ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : Fin 2 × Fin Pk.s, if q.1 = g then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.ga o g a k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a)
            · simp only [if_pos hk]
              exact hpc2 o g a ho k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o ho g a k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

/- English proof (translation)
Break down `Nat.eq_zero_or_pos l with hl | hl` into its components or cases. Establish `hz : ∀ z σ k, Pk.gaC z σ k = 0`. Introduce `z σ k`. Assume the negation of the conclusion as `hne`. Establish `hs` using `Pk.supp z σ k hne`.

Establish `h0 : Pk.s * (l - 1) = 0` using `by simp [hl]`. Establish `hf` using `(Pk.first z σ).trans h0.le`. Conclude with `hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))`. Establish `h` using `Pk.val (fun _ => []) (by simp) (by simp) (by simp) (by intro o σ k; simp [hz o σ k])`. Simplify using `using h`.

Establish `hcut : ∀ z σ, ∃ pc : Fin Pk.s → ℕ → ℕ, (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧ (∀ k, ∑ u, pc u k = Pk.gaC z σ k)`. Introduce `z σ`. Take `⟨pc, h1, h2⟩` from `cut Pk.K Pk.s (l - 1) (Pk.gaC z σ)`. Conclude with `⟨pc, h1, h2 (Pk.first z σ) fun k hk => ⟨(Pk.supp z σ k hk).1, (Pk.supp z σ k hk).2.2⟩⟩`. Use `choose pc hpc1 hpc2 using hcut`.

Set `ee : P.Pl → ZMod 2 × Fin Pk.s → ZMod 2 → ℕ → ℕ` to `fun z q a k => if a = q.1 then pc z q.1 q.2 k else 0`. Set `blk : P.Pl → ZMod 2 × Fin Pk.s → RF.GlobalTheory 2 × ℝ` to `fun z q => (RF.GlobalTheory.mon 0 (ee z q) Pk.K, 0)`. Set `L : P.Pl → List (RF.GlobalTheory 2 × ℝ)` to `fun z => (Finset.univ : Finset (ZMod 2 × Fin Pk.s)).toList.map (blk z)`. Establish `hsum0 : ∑ o, ((L o).map Prod.snd).sum = 0`. Simplify using `[L, blk]`.

Use `(Pk.val L ?_ ?_ ?_ ?_).trans hsum0.le` and prove the remaining obligations. Introduce `o p hp`. Simplify using `only [L, List.mem_map, Finset.mem_toList] at hp`. Take `⟨q, -, rfl⟩` from `hp`. Use `(hM Pk.R.C Pk.R.V 2 (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) 0 (ee o q) Pk.K).2 ?_` and prove the remaining obligations.

Introduce `a ρ`. Rewrite using `[Pk.R.hVl]`. Establish `h1 : ∑ k ∈ Finset.Icc 1 Pk.K, ee o q a k ≤ l - 1`. Distinguish the cases in `ha : a = q.1`. Simplify `hpc1 o q.1 q.2` using `[ee, ha]`.

Simplify using `[ee, ha]`. Establish `h2` using `(monAl_le_first Pk.K ((Pk.R.X o).rkF 0 a) (ee o q a) ρ).trans h1`. Use linear arithmetic over natural numbers and integers. Introduce `o p hp g e N hpe`. Simplify using `only [L, List.mem_map, Finset.mem_toList] at hp`.

Take `⟨q, -, rfl⟩` from `hp`. Take `⟨-, rfl, -⟩` from `RF.GlobalTheory.mon.inj hpe`. Conclude with `⟨q.1, fun a k ha => by simp [ee, ha]⟩`. Establish `hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K`. Introduce `o`.

Simplify using `only [L, List.map_map]`. Rewrite using `[Finset.sum_map_toList]`. Simplify using `[blk, RF.GlobalTheory.what₂]`. Rewrite using `[Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul, Finset.card_univ]`. Combine the equalities or inequalities in the displayed calculation.

Introduce `o σ k`. Establish `hw : ∀ q : ZMod 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k = if q.1 = σ then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0) else 0`. Introduce and unpack `⟨a, u⟩`. Distinguish the cases in `ha : a = σ`. Substitute `ha` using the available equality.

Simplify using `[blk, ee, RF.GlobalTheory.wt]`. Simplify using `[blk, ee, RF.GlobalTheory.wt, ha, Ne.symm ha]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [L, List.map_map]`. Rewrite using `[Finset.sum_map_toList]`.

Both sides reduce to the same expression. Use `_ = ∑ q : ZMod 2 × Fin Pk.s, if q.1 = σ then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0) else 0 := Finset.sum_congr rfl fun q _ => hw q`. Use `_ = ∑ u : Fin Pk.s, (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ u k else 0) := by`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single σ]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Use `_ = Pk.gaC o σ k := by`. Distinguish the cases in `hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ)`.

Simplify using `only [if_pos hk]`. Conclude with `hpc2 o σ k`. Simplify using `only [if_neg hk, Finset.sum_const_zero]`. Use `symm`. Assume the negation of the conclusion as `hne`.

Establish `hs` using `Pk.supp o σ k hne`. Conclude with `hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩`.
-/
theorem zero_of_pkgC (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZeroC P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z σ k, Pk.gaC z σ k = 0 := by
      intro z σ k
      by_contra hne
      have hs := Pk.supp z σ k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z σ).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp) (by simp)
      (by intro o σ k; simp [hz o σ k])
    simpa using h
  · have hcut : ∀ z σ, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧ (∀ k, ∑ u, pc u k = Pk.gaC z σ k) := by
      intro z σ
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.gaC z σ)
      exact ⟨pc, h1, h2 (Pk.first z σ)
        fun k hk => ⟨(Pk.supp z σ k hk).1, (Pk.supp z σ k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let ee : P.Pl → ZMod 2 × Fin Pk.s → ZMod 2 → ℕ → ℕ :=
      fun z q a k => if a = q.1 then pc z q.1 q.2 k else 0
    let blk : P.Pl → ZMod 2 × Fin Pk.s → RF.GlobalTheory 2 × ℝ :=
      fun z q => (RF.GlobalTheory.mon 0 (ee z q) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory 2 × ℝ) :=
      fun z => (Finset.univ : Finset (ZMod 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_ ?_).trans hsum0.le
    · intro o p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V 2 (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) 0 (ee o q) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 : ∑ k ∈ Finset.Icc 1 Pk.K, ee o q a k ≤ l - 1 := by
        by_cases ha : a = q.1
        · simpa [ee, ha] using hpc1 o q.1 q.2
        · simp [ee, ha]
      have h2 := (monAl_le_first Pk.K ((Pk.R.X o).rkF 0 a) (ee o q a) ρ).trans h1
      omega
    · intro o p hp g e N hpe
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hpe
      exact ⟨q.1, fun a k ha => by simp [ee, ha]⟩
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul, Finset.card_univ]
      calc 2 * (Fintype.card P.Pl * (2 * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * Fintype.card P.Pl := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o σ k
      have hw : ∀ q : ZMod 2 × Fin Pk.s,
          (blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k =
          if q.1 = σ then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0)
          else 0 := by
        rintro ⟨a, u⟩
        by_cases ha : a = σ
        · subst ha
          simp [blk, ee, RF.GlobalTheory.wt]
        · simp [blk, ee, RF.GlobalTheory.wt, ha, Ne.symm ha]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) 0 σ k + p.1.wt (Pk.R.X o) 1 (σ + 1) k).sum
          = ∑ q : ZMod 2 × Fin Pk.s,
              ((blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k) := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : ZMod 2 × Fin Pk.s, if q.1 = σ then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single σ]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.gaC o σ k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ)
            · simp only [if_pos hk]
              exact hpc2 o σ k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o σ k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

end GlobalTheory.GoodDepth.Zero

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkg GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk, fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkgC GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk⟩`.
-/
theorem GlobalTheory.GoodDepth.zeroBd : GlobalTheory.GoodDepth.ZeroBd :=
  ⟨fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkg GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk,
    fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkgC GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk⟩
