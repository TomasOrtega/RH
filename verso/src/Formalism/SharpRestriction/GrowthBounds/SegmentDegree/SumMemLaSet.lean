import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FamilyDegreesAdmissible

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

/- English proof (translation)
Unfold `Dat.sumhT`. Use `sum_one_le_prod _ _ fun j _ => sum_one_le_prod _ _ fun x _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `sum_one_le_bin _ _ _`. Conclude with `le_rfl`.
-/
theorem sum_one_le_hT (t : Fin n') (v : Fin (r + K) → ℕ) : 1 ≤ X.sumhT p K t v := by
  unfold Dat.sumhT
  refine sum_one_le_prod _ _ fun j _ => sum_one_le_prod _ _ fun x _ => ?_
  split_ifs
  · exact sum_one_le_bin _ _ _
  · exact le_rfl

/- English proof (translation)
Unfold `Dat.laSet`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Use `⟨fun c => ?_, h2, fun j x hx hpos => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_range]`. Establish `: v c ≤ ∑ c, v c` using `Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[F.uniqP j j0 x x0 hx hx0 hpos]`. Conclude with `⟨h1, h3⟩`.
-/
theorem sum_mem_laSet (F : SumFacts X p K) {j0 x0 : ℤ} (hx0 : x0 ∈ X.toLate j0) (v : Fin (r + K) → ℕ)
    (h1 : ∀ c, v c < X.Pz p K j0 x0) (h2 : ∑ c, v c ≤ X.a' p K (posOf n' x0))
    (h3 : (∑ c, v c) % X.Pz p K j0 x0 = X.a' p K (posOf n' x0) % X.Pz p K j0 x0) :
    v ∈ X.laSet p K (posOf n' x0) := by
  classical
  unfold Dat.laSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun c => ?_, h2, fun j x hx hpos => ?_⟩
  · rw [Finset.mem_range]
    have : v c ≤ ∑ c, v c := Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · rw [F.uniqP j j0 x x0 hx hx0 hpos]
    exact ⟨h1, h3⟩

/- English proof (translation)
Establish `h0 : (0 : Fin (r + K) → ℕ) ∈ X.laSet p K t`. Unfold `Dat.laSet`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Use `⟨fun c => by simp, by simp, fun j x hx hpos => ?_⟩` and prove the remaining obligations. Conclude with `absurd (hpos ▸ (sum_late_mem hx).2.2.2) ht`.

Unfold `Dat.sumSt`. Conclude with `(sum_one_le_hT t 0).trans (Finset.single_le_sum (f := fun v => X.sumhT p K t v) (fun v _ => zero_le_one.trans (sum_one_le_hT t v)) h0)`.
-/
theorem sum_St_nontop (t : Fin n') (ht : t ∉ X.F.TT) : 1 ≤ X.sumSt p K t := by
  classical
  have h0 : (0 : Fin (r + K) → ℕ) ∈ X.laSet p K t := by
    unfold Dat.laSet
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun c => by simp, by simp, fun j x hx hpos => ?_⟩
    exact absurd (hpos ▸ (sum_late_mem hx).2.2.2) ht
  unfold Dat.sumSt
  exact (sum_one_le_hT t 0).trans
    (Finset.single_le_sum (f := fun v => X.sumhT p K t v) (fun v _ => zero_le_one.trans (sum_one_le_hT t v)) h0)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun v _ => zero_le_one.trans (sum_one_le_hT t v)`.
-/
theorem sum_St_nonneg (t : Fin n') : 0 ≤ X.sumSt p K t :=
  Finset.sum_nonneg fun v _ => zero_le_one.trans (sum_one_le_hT t v)

/- English proof (translation)
Unfold `Dat.Pz`. Conclude with `pow_pos hp _`.
-/
theorem Pz_pos (hp : 0 < p) (j x : ℤ) : 0 < X.Pz p K j x := by unfold Dat.Pz; exact pow_pos hp _

/- English proof (translation)
Establish `hl` using `(F.LLsub _ _ hx0).1`. Establish `hd` using `sum_digit_count (r + K) (X.a' p K (posOf n' x0)) (X.Pz p K (j0.val : ℤ) x0) (by omega) (Pz_pos hp _ _) (X.laSet p K (posOf n' x0)) (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)`. Establish `hd' : sumBin r K (X.a' p K (posOf n' x0)) ≤ ∑ v ∈ X.laSet p K (posOf n' x0), sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x0)`. Unfold `sumBin`. Conclude with `hd` after adjusting the coercions.

Use `hd'.trans (Finset.sum_le_sum fun v _ => ?_)` and prove the remaining obligations. Unfold `Dat.sumhT`. Establish `hin : ∀ j : Fin X.F.J, ∀ x ∈ X.F.LLset (j.val : ℤ), (1 : ℝ) ≤ (if posOf n' x = posOf n' x0 then sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1)`. Introduce `j x _`. Use `split_ifs`.

Conclude with `sum_one_le_bin _ _ _`. Conclude with `le_rfl`. Establish `s1` using `sum_single_le_prod (X.F.LLset (j0.val : ℤ)) (fun x => if posOf n' x = posOf n' x0 then sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x) else 1) (hin j0) hx0`. Establish `s2` using `sum_single_le_prod (Finset.univ : Finset (Fin X.F.J)) (fun j => ∏ x ∈ X.F.LLset (j.val : ℤ), if posOf n' x = posOf n' x0 then sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1) (fun j _ => sum_one_le_prod _ _ (hin j)) (Finset.mem_univ j0)`. Simplify using `only [if_true] at s1`.

Conclude with `s1.trans s2`.
-/
theorem sum_St_LL (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : Fin X.F.J) {x0 : ℤ}
    (hx0 : x0 ∈ X.F.LLset (j0.val : ℤ)) :
    sumBin r K (X.a' p K (posOf n' x0)) ≤ X.sumSt p K (posOf n' x0) := by
  classical
  have hl := (F.LLsub _ _ hx0).1
  have hd := sum_digit_count (r + K) (X.a' p K (posOf n' x0)) (X.Pz p K (j0.val : ℤ) x0) (by omega) (Pz_pos hp _ _)
    (X.laSet p K (posOf n' x0)) (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : sumBin r K (X.a' p K (posOf n' x0)) ≤ ∑ v ∈ X.laSet p K (posOf n' x0),
      sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x0) := by
    unfold sumBin
    exact_mod_cast hd
  refine hd'.trans (Finset.sum_le_sum fun v _ => ?_)
  unfold Dat.sumhT
  have hin : ∀ j : Fin X.F.J, ∀ x ∈ X.F.LLset (j.val : ℤ), (1 : ℝ) ≤
      (if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1) := by
    intro j x _
    split_ifs
    · exact sum_one_le_bin _ _ _
    · exact le_rfl
  have s1 := sum_single_le_prod (X.F.LLset (j0.val : ℤ)) (fun x => if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x) else 1) (hin j0) hx0
  have s2 := sum_single_le_prod (Finset.univ : Finset (Fin X.F.J)) (fun j => ∏ x ∈ X.F.LLset (j.val : ℤ),
      if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1)
      (fun j _ => sum_one_le_prod _ _ (hin j)) (Finset.mem_univ j0)
  simp only [if_true] at s1
  exact s1.trans s2

/- English proof (translation)
Establish `hl` using `F.frlate j0 i`. Establish `hd` using `sum_label_count (r + K) (X.a' p K (posOf n' (X.F.fr j0 i.val))) (X.Pz p K j0 (X.F.fr j0 i.val)) (by omega) (Pz_pos hp _ _) (F.kP _ _ hl) (X.laSet p K (posOf n' (X.F.fr j0 i.val))) (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)`. Establish `hd' : ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤ ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ)` using `by exact_mod_cast hd`. Use `hd'.trans ?_` and prove the remaining obligations. Unfold `Dat.sumSt`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_St_fr (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : ℤ) (i : Fin r) :
    ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤ X.sumSt p K (posOf n' (X.F.fr j0 i.val)) := by
  classical
  have hl := F.frlate j0 i
  have hd := sum_label_count (r + K) (X.a' p K (posOf n' (X.F.fr j0 i.val))) (X.Pz p K j0 (X.F.fr j0 i.val)) (by omega)
    (Pz_pos hp _ _) (F.kP _ _ hl) (X.laSet p K (posOf n' (X.F.fr j0 i.val)))
    (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤
      ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ) := by exact_mod_cast hd
  refine hd'.trans ?_
  unfold Dat.sumSt
  calc ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ)
      = ∑ _v ∈ X.laSet p K (posOf n' (X.F.fr j0 i.val)), (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => sum_one_le_hT _ v

/- English proof (translation)
Unfold `Dat.sumSt`. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun la _ => ?_` and prove the remaining obligations. Unfold `Dat.sumhT`. Rewrite using `[Finset.prod_comm]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_ite_eq]`. Simplify using `[Dat.nz]`.
-/
theorem sum_LA :
    ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ), sumBin r K (X.nz p K la (j.val : ℤ) x) =
      ∏ t : Fin n', X.sumSt p K t := by
  classical
  unfold Dat.sumSt
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun la _ => ?_
  unfold Dat.sumhT
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_ite_eq]
  simp [Dat.nz]

/- English proof (translation)
Use `⟨by nlinarith, mul_nonneg hP0 (by linarith), by nlinarith⟩` and prove the remaining obligations.
-/
theorem sub_le_mul_one_sub_and_mem_unit_interval {P c s : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : s ≤ P) :
    s - c ≤ P * (1 - c) ∧ 0 ≤ P * (1 - c) ∧ P * (1 - c) ≤ 1 := by
  refine ⟨by nlinarith, mul_nonneg hP0 (by linarith), by nlinarith⟩

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
