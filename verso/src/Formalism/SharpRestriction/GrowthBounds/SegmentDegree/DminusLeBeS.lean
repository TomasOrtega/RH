import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TauDegreeOnPathBound
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LDigits

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Introduce `r Q be c ρ hr hQ`. Establish `hQ0 : 0 < Q` using `by omega`. Establish `hcore` using `Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ`. Use `le_trans hcore ?_` and prove the remaining obligations. Establish `hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤ ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter fun w => (c + ∑ i, w i) % Q = ρ % Q).card`.

Use `Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_` and prove the remaining obligations. Introduce `u hu`. Establish `hu'` using `(Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2`. Use `Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l => Finset.mem_range.mpr (u l).isLt, ?_⟩)` and prove the remaining obligations. Establish `h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q]` using `hu'`.

Establish `h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q]` using `Nat.ModEq.add_left c h1`. Establish `h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q]`. Establish `hc : c % Q < Q` using `Nat.mod_lt _ hQ0`. Establish `e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q`. Use `Nat.mod_le c Q` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e1]`. Establish `e2 : c - c % Q + Q ≡ 0 [MOD Q]`. Establish `hd : Q ∣ c - c % Q` using `Nat.dvd_sub_mod c`. Conclude with `(Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))`.

Establish `e3 : ρ % Q ≡ ρ [MOD Q]` using `Nat.mod_modEq ρ Q`. Simplify using `using e2.add e3`. Conclude with `h2.trans h3`. Introduce `u _ u' _ huu`. Use function extensionality and compare the values at `l`.

Conclude with `Fin.ext (congrFun huu l)`. Conclude with `hle` after adjusting the coercions.
-/
theorem residue_class_count : ResidueClassCount := by
  classical
  intro r Q be c ρ hr hQ
  have hQ0 : 0 < Q := by omega
  have hcore := Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ
  refine le_trans hcore ?_
  have hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
      (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤
      ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card := by
    refine Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l =>
        Finset.mem_range.mpr (u l).isLt, ?_⟩)
      have h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q] := hu'
      have h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q] := Nat.ModEq.add_left c h1
      have h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q] := by
        have hc : c % Q < Q := Nat.mod_lt _ hQ0
        have e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q := by
          have := Nat.mod_le c Q
          omega
        rw [e1]
        have e2 : c - c % Q + Q ≡ 0 [MOD Q] := by
          have hd : Q ∣ c - c % Q := Nat.dvd_sub_mod c
          exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))
        have e3 : ρ % Q ≡ ρ [MOD Q] := Nat.mod_modEq ρ Q
        simpa using e2.add e3
      exact h2.trans h3
    · intro u _ u' _ huu
      funext l
      exact Fin.ext (congrFun huu l)
  exact_mod_cast hle

/- English proof (translation)
Introduce `n hn`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn.ne'`. Introduce `f g h`. Rewrite using `[Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]`. Establish `h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc` using `Finset.sum_le_sum fun i _ => h i.castSucc (by simp)`.

Establish `e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m` using `Fin.ext (by simp)`. Rewrite using `[e]`. Establish `e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0` using `rfl`. Rewrite using `[e0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tele_le : ∀ (n : ℕ) (hn : 0 < n) (f g : Fin n → ℤ),
    (∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ ≤ g a) →
    ∑ a, (f a - g a) ≤ f ⟨0, hn⟩ - g ⟨n - 1, by omega⟩ := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro f g h
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
  have h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc :=
    Finset.sum_le_sum fun i _ => h i.castSucc (by simp)
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e]
  have e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0 := rfl
  rw [e0]
  linarith

section D21

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

/- English proof (translation)
Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hV` using `hX.valid`. Establish `hrN` using `k_r_le_segN X.F hV hr j`. Unfold `T.dminus Dat.beS`. Establish `himg : (X.F.letters j).filter (· < X.F.fr j 0) = (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j)`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hlt⟩`. Take `⟨i, rfl⟩` from `segE_surj X.F j hx`.

Conclude with `⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩`. Rewrite using `[himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]`. Use `Finset.sum_le_sum fun l _ => ?_` and prove the remaining obligations.

Use `split_ifs with h1 h2 h2`. Rewrite using `[hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]`. It suffices to derive a contradiction. Establish `hl` using `l.isLt`. Establish `ht : l.val - (segN X.F j - r) < r` using `by omega`.

Establish `hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r))` using `(segE_eq_fr_iff X.F hV j l ht).mpr (by omega)`. Establish `hvec : (segLL X.F j).vec l = true`. Rewrite using `[comb_vec, hseg]`. Conclude with `(hV.2.2.2.2.1 j _ ht).2`. Rewrite `h1` using `[hvec]`.

Conclude with `absurd h1.2 (by simp)`. Conclude with `Nat.zero_le _`. Conclude with `le_rfl`.
-/
theorem dminus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) :
    T.dminus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  unfold T.dminus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · exfalso
    have hl := l.isLt
    have ht : l.val - (segN X.F j - r) < r := by omega
    have hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r)) :=
      (segE_eq_fr_iff X.F hV j l ht).mpr (by omega)
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
    rw [hvec] at h1
    exact absurd h1.2 (by simp)
  · exact Nat.zero_le _
  · exact le_rfl

end D21

/- English proof (translation)
Introduce `p n' r K _ _ _ X hX j b μ dd hP i hi`. Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hV` using `hX.valid`. Establish `hrN` using `k_r_le_segN X.F hV hr j`. Take `⟨P, hPμ⟩` from `hP.path`.

Establish `hil` using `i.isLt`. Establish `hnot : ¬ i.val < segN X.F j - r` using `fun h => by`. Use `(segE_lt_fr_iff X.F hV hr j i).mpr h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `ht : i.val - (segN X.F j - r) < r` using `by omega`.

Establish `hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r))` using `(segE_eq_fr_iff X.F hV j i ht).mpr (by omega)`. Establish `hvec : (segLL X.F j).vec i = true`. Rewrite using `[comb_vec, hseg]`. Conclude with `(hV.2.2.2.2.1 j _ ht).2`. Establish `hs` using `T.step_vec P i hvec`.

Rewrite `hs` using `[hPμ]`. Establish `hn : 0 < r + K` using `by omega`. Establish `h1` using `tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1`. Rewrite `h1` using `[hs.2.2]`. Establish `h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ)` using `hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)`.

Establish `h3` using `T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩`. Rewrite `h3` using `[hPμ]`. Establish `h4` using `dminus_le_beS X p K hX j b μ dd hP i.val`. Establish `h5 : μ i.castSucc = μ ⟨i.val, by omega⟩` using `rfl`. Rewrite `h1` using `[h2, h5]`.

Establish `h4' : (T.dminus (segLL X.F j) dd i.val : ℤ) ≤ (X.beS p K j b : ℤ)` using `by exact_mod_cast h4`. Establish `: (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ)` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem tau_degree_on_path_bound : TauDegreeOnPathBound := by
  intro p n' r K _ _ _ X hX j b μ dd hP i hi
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  obtain ⟨P, hPμ⟩ := hP.path
  have hil := i.isLt
  have hnot : ¬ i.val < segN X.F j - r := fun h => by
    have := (segE_lt_fr_iff X.F hV hr j i).mpr h
    omega
  have ht : i.val - (segN X.F j - r) < r := by omega
  have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
    (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
  have hvec : (segLL X.F j).vec i = true := by
    rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
  have hs := T.step_vec P i hvec
  rw [hPμ] at hs
  have hn : 0 < r + K := by omega
  have h1 := tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1
  rw [hs.2.2] at h1
  have h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ) :=
    hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)
  have h3 := T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩
  rw [hPμ] at h3
  have h4 := dminus_le_beS X p K hX j b μ dd hP i.val
  have h5 : μ i.castSucc = μ ⟨i.val, by omega⟩ := rfl
  rw [h2, h5] at h1
  have h4' : (T.dminus (segLL X.F j) dd i.val : ℤ) ≤ (X.beS p K j b : ℤ) := by exact_mod_cast h4
  have : (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ) := by linarith
  exact_mod_cast this

end Formalism.MainNotions.SelectionLemmas.Pf
