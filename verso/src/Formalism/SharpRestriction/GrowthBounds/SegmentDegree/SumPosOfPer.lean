import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumTotalLoss
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopDegreeComparison

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fr_add_mul_period (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    F.fr (j + m * F.J) i = F.fr j i + m * n' := by
  have hper := hV.2.1
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h1 := hper (j + k * F.J) i
    rw [show j + ((k : ℤ) + 1) * (F.J : ℤ) = j + k * F.J + F.J by ring, h1, ih]
    ring
  | pred k ih =>
    have h1 := hper (j + (-(k : ℤ) - 1) * F.J) i
    rw [show j + (-(k : ℤ) - 1) * (F.J : ℤ) + F.J = j + -(k : ℤ) * F.J by ring, ih] at h1
    linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Separate the alternatives or extract the components of the hypothesis.

Substitute using the available equality. A detailed English derivation is pending.
-/
theorem fr_lt_fr_of_lt_of_valid (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i' hii' hi'r
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k (by omega))
    · subst h
      exact hV.2.2.1 j i (by omega)

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem sum_fr_le (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases h.lt_or_eq with h | h
  · exact (fr_lt_fr_of_lt_of_valid hV j i i' h h').le
  · subst h
    exact le_rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem sum_posOf_per (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  unfold posOf
  congr 3
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dist_add_mul_period (hV : F.Valid L₁ N₁) (j x m : ℤ) : F.dist (j + m * F.J) (x + m * n') = F.dist j x := by
  unfold Frames.dist
  rw [fr_add_mul_period hV]
  congr 1
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem sum_prod_Ioc (g : ℕ → ℤ) (hg : Monotone g) (P : ℤ → Prop) [DecidablePred P] (ψ : ℤ → ℝ) (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ x ∈ (Finset.Ioc (g j) (g (j + 1))).filter P, ψ x =
      ∏ x ∈ (Finset.Ioc (g 0) (g m)).filter P, ψ x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, ← Finset.prod_union
      (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)), ← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le m)) (hg (Nat.le_succ m))]

end Geo

section GeoX

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (p K : ℕ)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem mem_late_iff (hV : X.F.Valid L₁ N₁) (j x : ℤ) :
    x ∈ X.toLate j ↔ (eFr X.F (j - 1) < x ∧ x ≤ eFr X.F j) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have : X.toLate j = nonW X.F j := rfl
  rw [this, nonW_eq hV, Finset.mem_filter, Finset.mem_Ioc]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_shift_of_posOf_eq_of_mem_late (hV : X.F.Valid L₁ N₁) {j j' x x' : ℤ} (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : ∃ m : ℤ, j' = j + m * X.F.J ∧ x' = x + m * n' := by
  have h1 : x % (n' : ℤ) = x' % (n' : ℤ) := by rw [← posOf_val, ← posOf_val, h]
  have h2 : (n' : ℤ) ∣ x' - x := Int.ModEq.dvd h1
  obtain ⟨m, hm⟩ := h2
  have hm' : x' = x + m * n' := by linarith [mul_comm (n' : ℤ) m]
  refine ⟨m, ?_, hm'⟩
  have a1 := (mem_late_iff X hV j x).mp hx
  have a2 := (mem_late_iff X hV j' x').mp hx'
  have p1 : eFr X.F (j + m * X.F.J) = eFr X.F j + m * n' := fr_add_mul_period hV j (r - 1) m
  have p0 : eFr X.F (j + m * X.F.J - 1) = eFr X.F (j - 1) + m * n' := by
    have := fr_add_mul_period hV (j - 1) (r - 1) m
    rw [show j + m * X.F.J - 1 = j - 1 + m * X.F.J by ring]
    exact this
  exact idx_unique (eFr_strictMono hV) (x := x') a2.1.1 a2.1.2 (by rw [p0]; linarith [a1.1.1])
    (by rw [p1]; linarith [a1.1.2])

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem sum_Rj_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Rj p K (j + m * X.F.J) = X.Rj p K j := by
  unfold Dat.Rj
  have e : j + m * X.F.J - 1 = (j - 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j - 1) 0 m, dist_add_mul_period hV]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem sum_Pz_per (hV : X.F.Valid L₁ N₁) (j x m : ℤ) :
    X.Pz p K (j + m * X.F.J) (x + m * n') = X.Pz p K j x := by
  unfold Dat.Pz
  rw [dist_add_mul_period hV, sum_Rj_per X p K hV]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_Qc_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Qc p K (j + m * X.F.J) = X.Qc p K j := by
  unfold Dat.Qc
  have e : j + m * X.F.J + 1 = (j + 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j + 1) (r - 1) m, fr_add_mul_period hV j (r - 1) m, sum_Rj_per X p K hV, sum_Rj_per X p K hV]
  congr 2
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem sum_uniqP (hV : X.F.Valid L₁ N₁) (j j' x x' : ℤ) (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : X.Pz p K j x = X.Pz p K j' x' := by
  obtain ⟨m, rfl, rfl⟩ := exists_shift_of_posOf_eq_of_mem_late X hV hx hx' h
  exact (sum_Pz_per X p K hV j x m).symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_perW (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) :
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val) := by
  have e1 : X.F.fr (j + X.F.J - 1) i.val = X.F.fr (j - 1) i.val + 1 * n' := by
    have := fr_add_mul_period hV (j - 1) i.val 1
    rw [show j + (X.F.J : ℤ) - 1 = j - 1 + 1 * X.F.J by ring]
    exact this
  have e2 : j + (X.F.J : ℤ) = j + 1 * X.F.J := by ring
  unfold Dat.Bw
  rw [e1, e2, sum_posOf_per, dist_add_mul_period hV, sum_Rj_per X p K hV]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Use symmetry to reverse the relation.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem prod_tiling (hV : X.F.Valid L₁ N₁) (φ : Fin n' → ℝ) :
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) := by
  classical
  have hm := eFr_strictMono hV
  have h1 : ∀ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) =
      ∏ x ∈ (Finset.Ioc ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) (j + 1))).filter
        (fun x => posOf n' x ∈ X.F.TT), φ (posOf n' x) := by
    intro j _
    have : X.toLate (j : ℤ) = nonW X.F j := rfl
    rw [this, nonW_eq hV]
    simp
  rw [Finset.prod_congr rfl h1, sum_prod_Ioc (fun i : ℕ => eFr X.F ((i : ℤ) - 1))
    (fun a b hab => hm.monotone (by omega)) (fun x => posOf n' x ∈ X.F.TT) (fun x => φ (posOf n' x)) X.F.J]
  have h2 : eFr X.F ((X.F.J : ℤ) - 1) = eFr X.F (((0 : ℕ) : ℤ) - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    simp only [eFr]
    have e1 : ((X.F.J : ℤ) - 1) = -1 + X.F.J := by ring
    have e2 : (((0 : ℕ) : ℤ) - 1) = -1 := by norm_num
    rw [e1, e2, this]
  simp only [h2]
  set a := eFr X.F (((0 : ℕ) : ℤ) - 1) with ha
  symm
  refine Finset.prod_bij (fun x _ => posOf n' x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact posOf_injOn a (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1) hxy
  · intro t ht
    have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have b0 := Int.emod_nonneg ((t.val : ℤ) - (a + 1)) hn.ne'
    have b1 := Int.emod_lt_of_pos ((t.val : ℤ) - (a + 1)) hn
    have hpos : posOf n' (a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ)) = t := by
      have e : a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ) =
          (t.val : ℤ) + (-(((t.val : ℤ) - (a + 1)) / (n' : ℤ))) * n' := by
        have := Int.emod_add_mul_ediv ((t.val : ℤ) - (a + 1)) (n' : ℤ)
        linarith
      rw [e, sum_posOf_per, posOf_natCast]
    refine ⟨a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ), ?_, hpos⟩
    rw [Finset.mem_filter, Finset.mem_Ioc, hpos]
    exact ⟨⟨by omega, by omega⟩, ht⟩
  · intro x _
    rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem sum_LLsub (hV : X.F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ X.F.LLset j) : x ∈ X.toLate j ∧ x < X.F.fr j 0 := by
  classical
  unfold Frames.LLset at hx
  rw [Finset.mem_filter, Finset.mem_Ioo] at hx
  refine ⟨(mem_late_iff X hV j x).mpr ⟨⟨hx.1.1, ?_⟩, hx.2⟩, hx.1.2⟩
  exact hx.1.2.le.trans (fr_zero_le_eFr hV j)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_frlate (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) : X.F.fr j i.val ∈ X.toLate j := by
  refine (mem_late_iff X hV j _).mpr ⟨⟨?_, ?_⟩, (hV.2.2.2.2.1 j i.val i.isLt).1⟩
  · have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    exact lt_of_lt_of_le h1 (fr_zero_le hV j i.val i.isLt)
  · exact sum_fr_le hV j i.val (r - 1) (by have := i.isLt; omega) (Nat.sub_lt (NeZero.pos r) Nat.one_pos)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sum_split (hV : X.F.Valid L₁ N₁) (j : ℤ) (ψ : ℤ → ℝ) :
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val) := by
  classical
  have hinj : Function.Injective (fun i : Fin r => X.F.fr j i.val) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact absurd hab (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j a.val b.val h b.isLt))
    · exact absurd hab.symm (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j b.val a.val h a.isLt))
  have hU : X.toLate j = X.F.LLset j ∪ Finset.univ.image (fun i : Fin r => X.F.fr j i.val) := by
    ext x
    rw [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hx
      have a1 := (mem_late_iff X hV j x).mp hx
      by_cases h0 : x < X.F.fr j 0
      · left
        unfold Frames.LLset
        rw [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨a1.1.1, h0⟩, a1.2⟩
      · right
        obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV j x a1.2 (not_lt.mp h0) (r - 1)
          (Nat.sub_lt (NeZero.pos r) Nat.one_pos) a1.1.2
        exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · rintro (hx | ⟨i, -, rfl⟩)
      · exact (sum_LLsub X hV j x hx).1
      · exact sum_frlate X hV j i
  have hdisj : Disjoint (X.F.LLset j) (Finset.univ.image (fun i : Fin r => X.F.fr j i.val)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx'
    have := (sum_LLsub X hV j _ hx).2
    have := fr_zero_le hV j i.val i.isLt
    omega
  rw [hU, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => hinj h)]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.
-/
theorem J_le_card_TT_of_valid (hV : X.F.Valid L₁ N₁) : X.F.J ≤ X.F.TT.card := by
  classical
  refine le_trans ?_ (sum_card_nonW hV)
  calc X.F.J = ∑ _j ∈ Finset.range X.F.J, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.card_pos.mpr
      ⟨X.F.fr (j : ℤ) (⟨0, NeZero.pos r⟩ : Fin r).val, sum_frlate X hV (j : ℤ) ⟨0, NeZero.pos r⟩⟩

end GeoX

end Formalism.MainNotions.SelectionLemmas.Pf
