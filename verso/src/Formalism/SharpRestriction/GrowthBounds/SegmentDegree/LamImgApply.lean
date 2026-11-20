import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamSatRestrict

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

structure LamGeo {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  U1 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.toLate (j.val : ℤ), ∀ x' ∈ X.toLate (j'.val : ℤ), posOf n' x = posOf n' x' →
    j = j' ∧ x = x'
  U2 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.F.letters (j'.val : ℤ),
    X.F.IsW (j'.val : ℤ) x' → posOf n' x = posOf n' x' → j = j' ∧ x = x'
  LK : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.toLate (j'.val : ℤ),
    posOf n' x = posOf n' x' → (∃ i < r, x' = X.F.fr (j'.val : ℤ) i) ∧
      X.Pz p K (j.val : ℤ) x = X.Pz p K (j'.val : ℤ) x' * X.Qc p K (j'.val : ℤ)
  EX : ∀ t ∈ X.F.TT, ∃ j : Fin X.F.J, ∃ x ∈ X.toLate (j.val : ℤ), posOf n' x = t

def RestLamGeo (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    LamGeo X p K

def RestLamTau : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (i : Fin r),
      X.bfam p K la e (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) = e j i

/- English proof (translation)
Establish `hP : 0 < P` using `lt_of_le_of_lt (Nat.zero_le _) h1`. Establish `e1 : (la + P * A) % P = la` using `by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]`. Establish `e2 : (la' + P * A') % P = la'` using `by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]`. Establish `hla : la = la'` using `by rw [← e1, ← e2, h]`. Use `⟨hla, ?_⟩` and prove the remaining obligations.

Substitute `hla` using the available equality. Establish `h3 : P * A = P * A'` using `by omega`. Conclude with `Nat.eq_of_mul_eq_mul_left hP h3`.
-/
theorem lam_digit {P la la' A A' : ℕ} (h1 : la < P) (h2 : la' < P) (h : la + P * A = la' + P * A') :
    la = la' ∧ A = A' := by
  have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le _) h1
  have e1 : (la + P * A) % P = la := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have e2 : (la' + P * A') % P = la' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  have hla : la = la' := by rw [← e1, ← e2, h]
  refine ⟨hla, ?_⟩
  subst hla
  have h3 : P * A = P * A' := by omega
  exact Nat.eq_of_mul_eq_mul_left hP h3

section Eval

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

/- English proof (translation)
Unfold `imgMon`. Rewrite using `[Finsupp.sum_apply]`. Establish `hsub : m.support ⊆ X.F.letters (j.val : ℤ) ×ˢ (Finset.univ : Finset (Fin (r + K)))`. Introduce `v hv`. Conclude with `Finset.mem_product.mpr ⟨(hm v (Finsupp.mem_support_iff.mp hv)).1, Finset.mem_univ _⟩`.

Rewrite using `[Finsupp.sum_of_support_subset m hsub _ (by intro v _; simp), Finset.sum_product]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [Finsupp.single_apply, Dat.lamG, Prod.mk.injEq]`. Distinguish the cases in `h : posOf n' x = t`. Simplify using `[h, Dat.lamE, Dat.Pz]`.

Simplify using `[h]`.
-/
theorem lam_img_apply (j : Fin X.F.J) (m : ℤ × Fin (r + K) →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (t : Fin n') (c : Fin (r + K)) :
    imgMon (X.lamG K j) (X.lamE p K j) m (t, c) =
      ∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = t then X.Pz p K (j.val : ℤ) x * m (x, c) else 0 := by
  classical
  unfold imgMon
  rw [Finsupp.sum_apply]
  have hsub : m.support ⊆ X.F.letters (j.val : ℤ) ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨(hm v (Finsupp.mem_support_iff.mp hv)).1, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (by intro v _; simp), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finsupp.single_apply, Dat.lamG, Prod.mk.injEq]
  by_cases h : posOf n' x = t
  · simp [h, Dat.lamE, Dat.Pz]
  · simp [h]

open Classical in

def segmentWeightExponent (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ)) (t : Fin n') (c : Fin (r + K)) : ℕ :=
  ∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
    if posOf n' x = t then m j (x, c) else 0

/- English proof (translation)
Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_congr rfl fun j _ => lam_img_apply X p K j (m j) (hm j) _ c]`. Establish `hsplit : ∀ j : Fin X.F.J, (∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) = (∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x, if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) el …`. Introduce `j`. Unfold `Dat.toLate`. Conclude with `(Finset.sum_filter_add_sum_filter_not _ _ _).symm`.

Rewrite using `[Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]`. Establish `hlate : (∑ j : Fin X.F.J, ∑ x ∈ X.toLate (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) = X.Pz p K (j0.val : ℤ) x0 * m j0 (x0, c)`. Rewrite using `[Finset.sum_eq_single j0]`. Rewrite using `[Finset.sum_eq_single x0]`. Rewrite using `[if_pos rfl]`.

Introduce `x hx hne`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hne (hG.U1 j0 j0 x hx x0 hx0 h).2`. Introduce `h`.

Conclude with `absurd hx0 h`. Introduce `j _ hne`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hne (hG.U1 j j0 x hx x0 hx0 h).1`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hW : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x, if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) = X.Pz p K (j0.val : ℤ) x0 * (X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c)`. Unfold `segmentWeightExponent`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Take `⟨hxl, hxW⟩` from `Finset.mem_filter.mp hx`.

Use `split_ifs with h`. Rewrite using `[(hG.LK j j0 x hxl hxW x0 hx0 h).2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[hlate, hW]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_eval (hG : LamGeo X p K) (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ))
    (hm : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (j0 : Fin X.F.J) (x0 : ℤ) (hx0 : x0 ∈ X.toLate (j0.val : ℤ))
    (c : Fin (r + K)) :
    (∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (posOf n' x0, c) =
      X.Pz p K (j0.val : ℤ) x0 * (m j0 (x0, c) + X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_congr rfl fun j _ => lam_img_apply X p K j (m j) (hm j) _ c]
  have hsplit : ∀ j : Fin X.F.J,
      (∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      (∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
        if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) +
      ∑ x ∈ X.toLate (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0 := by
    intro j
    unfold Dat.toLate
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  have hlate : (∑ j : Fin X.F.J, ∑ x ∈ X.toLate (j.val : ℤ),
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * m j0 (x0, c) := by
    rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single x0]
      · rw [if_pos rfl]
      · intro x hx hne
        rw [if_neg]
        intro h
        exact hne (hG.U1 j0 j0 x hx x0 hx0 h).2
      · intro h; exact absurd hx0 h
    · intro j _ hne
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [if_neg]
      intro h
      exact hne (hG.U1 j j0 x hx x0 hx0 h).1
    · intro h; exact absurd (Finset.mem_univ _) h
  have hW : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * (X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
    unfold segmentWeightExponent
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
    split_ifs with h
    · rw [(hG.LK j j0 x hxl hxW x0 hx0 h).2]; ring
    · simp
  rw [hlate, hW]; ring

end Eval

/- English proof (translation)
Introduce `p n' r K _ _ _ X hX hLa hk la hla e he la' hla' e' he' m m' hm hm' heq`. Establish `hG` using `hGeo p n' r K X hX hLa hk`. Establish `hok : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)` using `fun j => (hm j).1`. Establish `hok' : ∀ j v, m' j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)` using `fun j => (hm' j).1`. Establish `hlaS` using `Fintype.mem_piFinset.mp hla`.

Establish `hlaS'` using `Fintype.mem_piFinset.mp hla'`. Establish `hdec : ∀ (j0 : Fin X.F.J) (x0 : ℤ), x0 ∈ X.toLate (j0.val : ℤ) → ∀ c : Fin (r + K), la (posOf n' x0) c = la' (posOf n' x0) c ∧ m j0 (x0, c) = m' j0 (x0, c) ∧ segmentWeightExponent X K m (posOf n' x0) c = segmentWeightExponent X K m' (posOf n' x0) c`. Introduce `j0 x0 hx0 c`. Establish `h1` using `congrArg (fun f => f (posOf n' x0, c)) heq`. Simplify using `only [Finsupp.add_apply] at h1`.

Rewrite `h1` using `[lam_eval X p K hG m hok j0 x0 hx0 c, lam_eval X p K hG m' hok' j0 x0 hx0 c]`. Establish `hl1 : la (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0` using `((Finset.mem_filter.mp (hlaS (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c`. Establish `hl2 : la' (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0` using `((Finset.mem_filter.mp (hlaS' (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c`. Take `⟨g1, g2⟩` from `lam_digit hl1 hl2 h1`. Use `⟨g1, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hfc : (∃ i < r, x0 = X.F.fr (j0.val : ℤ) i) ∧ c.val < r`. Take `⟨⟨i, hi, rfl⟩, hc⟩` from `hfc`. Establish `hcc : c = Fin.castAdd K ⟨c.val, hc⟩` using `Fin.ext rfl`. Establish `a1 : m j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ)`. Rewrite using `[hcc]`.

Conclude with `(hm j0).2.2 i hi ⟨c.val, hc⟩`. Establish `a2 : m' j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ)`. Rewrite using `[hcc]`. Conclude with `(hm' j0).2.2 i hi ⟨c.val, hc⟩`. Conclude with `lam_digit a1 a2 g2`.

Establish `hw0 : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j v, mm j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) → segmentWeightExponent X K mm (posOf n' x0) c = 0`. Introduce `mm hmm`. Unfold `segmentWeightExponent`. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Take `⟨hxl, hxW⟩` from `Finset.mem_filter.mp hx`.

Use `split_ifs with h`. Assume the negation of the conclusion as `hne`. Apply `hfc` to reduce the goal to its premises. Use `⟨(hG.LK j j0 x hxl hxW x0 hx0 h).1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `(hmm j (x, c) hne).2 (not_lt.mp hc) hxW`. Both sides reduce to the same expression. Rewrite `g2`, the goal using `[hw0 m hok, hw0 m' hok']`. Simplify using `only [mul_zero, add_zero] at g2`. Conclude with `⟨g2, rfl⟩`.

Establish `hlaeq : la = la'`. Use function extensionality and compare the values at `t c`. Distinguish the cases in `ht : t ∈ X.F.TT`. Take `⟨j0, x0, hx0, rfl⟩` from `hG.EX t ht`. Conclude with `(hdec j0 x0 hx0 c).1`.

Establish `ha : X.a' p K t = 0`. Unfold `Dat.a' Dat.d`. Rewrite using `[if_neg ht]`. Simplify using the standard rewrite rules. Establish `b1` using `(Finset.mem_filter.mp (hlaS t)).2.1`.

Establish `b2` using `(Finset.mem_filter.mp (hlaS' t)).2.1`. Rewrite `b1`, `b2` using `[ha]`. Establish `c1` using `Finset.single_le_sum (f := fun c => la t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)`. Establish `c2` using `Finset.single_le_sum (f := fun c => la' t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)`. Use linear arithmetic over natural numbers and integers.

Establish `hmeq : m = m'`. Use function extensionality and compare the values at `j`. Use extensionality with `v`. Take `⟨x, c⟩` from `v`. Distinguish the cases in `hv : (x, c) ∈ okVars X.F K (j.val : ℤ)`.

Distinguish the cases in `hW : X.F.IsW (j.val : ℤ) x`. Establish `hTT : posOf n' x ∈ X.F.TT`. Use `hv.1` as an intermediate fact. Unfold `Frames.letters at this`. Conclude with `(Finset.mem_filter.mp this).2`.

Take `⟨j0, x0, hx0, hpos⟩` from `hG.EX _ hTT`. Establish `h3` using `(hdec j0 x0 hx0 c).2.2`. Establish `hwv : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), segmentWeightExponent X K mm (posOf n' x0) c = mm j (x, c)`. Introduce `mm`. Unfold `segmentWeightExponent`.

Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Finset.sum_eq_single x]`. Rewrite using `[if_pos hpos.symm]`. Introduce `y hy hne`. Take `⟨hyl, hyW⟩` from `Finset.mem_filter.mp hy`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hne (hG.U2 j j y hyl hyW x hv.1 hW (h.trans hpos)).2`. Introduce `h`. Conclude with `absurd (Finset.mem_filter.mpr ⟨hv.1, hW⟩) h`.

Introduce `j' _ hne`. Use `Finset.sum_eq_zero fun y hy => ?_` and prove the remaining obligations. Take `⟨hyl, hyW⟩` from `Finset.mem_filter.mp hy`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hne (hG.U2 j' j y hyl hyW x hv.1 hW (h.trans hpos)).1`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `h3` using `[hwv m, hwv m']`. Conclude with `h3`.

Conclude with `(hdec j x (Finset.mem_filter.mpr ⟨hv.1, hW⟩) c).2.1`. Establish `z1 : m j (x, c) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hv (hok j _ h)`. Establish `z2 : m' j (x, c) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hv (hok' j _ h)`. Rewrite using `[z1, z2]`. Use `⟨⟨hlaeq, ?_⟩, hmeq⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j i`.

Establish `d1` using `(hm j).2.1 (X.F.fr (j.val : ℤ) i.val)`. Establish `d2` using `(hm' j).2.1 (X.F.fr (j.val : ℤ) i.val)`. Rewrite `d1`, `d2` using `[hTau p n' r K X hX]`. Rewrite using `[← d1, ← d2, hmeq]`.
-/
theorem restLamInj_of (C₀ : ℝ) (hGeo : RestLamGeo C₀) (hTau : RestLamTau) : RestLamInj C₀ := by
  intro p n' r K _ _ _ X hX hLa hk la hla e he la' hla' e' he' m m' hm hm' heq
  classical
  have hG := hGeo p n' r K X hX hLa hk
  have hok : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm j).1
  have hok' : ∀ j v, m' j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm' j).1
  have hlaS := Fintype.mem_piFinset.mp hla
  have hlaS' := Fintype.mem_piFinset.mp hla'

  have hdec : ∀ (j0 : Fin X.F.J) (x0 : ℤ), x0 ∈ X.toLate (j0.val : ℤ) → ∀ c : Fin (r + K),
      la (posOf n' x0) c = la' (posOf n' x0) c ∧ m j0 (x0, c) = m' j0 (x0, c) ∧
        segmentWeightExponent X K m (posOf n' x0) c = segmentWeightExponent X K m' (posOf n' x0) c := by
    intro j0 x0 hx0 c
    have h1 := congrArg (fun f => f (posOf n' x0, c)) heq
    simp only [Finsupp.add_apply] at h1
    rw [lam_eval X p K hG m hok j0 x0 hx0 c, lam_eval X p K hG m' hok' j0 x0 hx0 c] at h1
    have hl1 : la (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    have hl2 : la' (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS' (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    obtain ⟨g1, g2⟩ := lam_digit hl1 hl2 h1
    refine ⟨g1, ?_⟩
    by_cases hfc : (∃ i < r, x0 = X.F.fr (j0.val : ℤ) i) ∧ c.val < r
    · obtain ⟨⟨i, hi, rfl⟩, hc⟩ := hfc
      have hcc : c = Fin.castAdd K ⟨c.val, hc⟩ := Fin.ext rfl
      have a1 : m j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm j0).2.2 i hi ⟨c.val, hc⟩
      have a2 : m' j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm' j0).2.2 i hi ⟨c.val, hc⟩
      exact lam_digit a1 a2 g2
    · have hw0 : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j v, mm j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) →
          segmentWeightExponent X K mm (posOf n' x0) c = 0 := by
        intro mm hmm
        unfold segmentWeightExponent
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x hx => ?_
        obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
        split_ifs with h
        · by_contra hne
          apply hfc
          refine ⟨(hG.LK j j0 x hxl hxW x0 hx0 h).1, ?_⟩
          by_contra hc
          exact (hmm j (x, c) hne).2 (not_lt.mp hc) hxW
        · rfl
      rw [hw0 m hok, hw0 m' hok'] at g2 ⊢
      simp only [mul_zero, add_zero] at g2
      exact ⟨g2, rfl⟩
  have hlaeq : la = la' := by
    funext t c
    by_cases ht : t ∈ X.F.TT
    · obtain ⟨j0, x0, hx0, rfl⟩ := hG.EX t ht
      exact (hdec j0 x0 hx0 c).1
    · have ha : X.a' p K t = 0 := by
        unfold Dat.a' Dat.d
        rw [if_neg ht]; simp
      have b1 := (Finset.mem_filter.mp (hlaS t)).2.1
      have b2 := (Finset.mem_filter.mp (hlaS' t)).2.1
      rw [ha] at b1 b2
      have c1 := Finset.single_le_sum (f := fun c => la t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have c2 := Finset.single_le_sum (f := fun c => la' t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
  have hmeq : m = m' := by
    funext j
    ext v
    obtain ⟨x, c⟩ := v
    by_cases hv : (x, c) ∈ okVars X.F K (j.val : ℤ)
    · by_cases hW : X.F.IsW (j.val : ℤ) x
      · have hTT : posOf n' x ∈ X.F.TT := by
          have := hv.1
          unfold Frames.letters at this
          exact (Finset.mem_filter.mp this).2
        obtain ⟨j0, x0, hx0, hpos⟩ := hG.EX _ hTT
        have h3 := (hdec j0 x0 hx0 c).2.2
        have hwv : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), segmentWeightExponent X K mm (posOf n' x0) c = mm j (x, c) := by
          intro mm
          unfold segmentWeightExponent
          rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single x]
            · rw [if_pos hpos.symm]
            · intro y hy hne
              obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
              rw [if_neg]
              intro h
              exact hne (hG.U2 j j y hyl hyW x hv.1 hW (h.trans hpos)).2
            · intro h; exact absurd (Finset.mem_filter.mpr ⟨hv.1, hW⟩) h
          · intro j' _ hne
            refine Finset.sum_eq_zero fun y hy => ?_
            obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
            rw [if_neg]
            intro h
            exact hne (hG.U2 j' j y hyl hyW x hv.1 hW (h.trans hpos)).1
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hwv m, hwv m'] at h3
        exact h3
      · exact (hdec j x (Finset.mem_filter.mpr ⟨hv.1, hW⟩) c).2.1
    · have z1 : m j (x, c) = 0 := by
        by_contra h; exact hv (hok j _ h)
      have z2 : m' j (x, c) = 0 := by
        by_contra h; exact hv (hok' j _ h)
      rw [z1, z2]
  refine ⟨⟨hlaeq, ?_⟩, hmeq⟩
  funext j i
  have d1 := (hm j).2.1 (X.F.fr (j.val : ℤ) i.val)
  have d2 := (hm' j).2.1 (X.F.fr (j.val : ℤ) i.val)
  rw [hTau p n' r K X hX] at d1 d2
  rw [← d1, ← d2, hmeq]

end Formalism.MainNotions.SelectionLemmas.Pf
