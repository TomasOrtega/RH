import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumTotalLoss
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopDegreeComparison

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Establish `hper` using `hV.2.1`. Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h1` using `hper (j + k * F.J) i`.

Rewrite using `[show j + ((k : ℤ) + 1) * (F.J : ℤ) = j + k * F.J + F.J by ring, h1, ih]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `pred k ih`. Establish `h1` using `hper (j + (-(k : ℤ) - 1) * F.J) i`. Rewrite `h1` using `[show j + (-(k : ℤ) - 1) * (F.J : ℤ) + F.J = j + -(k : ℤ) * F.J by ring, ih]`.

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
Introduce `i' hii' hi'r`. Proceed by induction on `i' with`. Consider the case `zero => omega`. Consider the case `succ k ih`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h` into its components or cases.

Conclude with `lt_trans (ih h (by omega)) (hV.2.2.1 j k (by omega))`. Substitute `h` using the available equality. Conclude with `hV.2.2.1 j i (by omega)`.
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
Break down `h.lt_or_eq with h | h` into its components or cases. Conclude with `(fr_lt_fr_of_lt_of_valid hV j i i' h h').le`. Substitute `h` using the available equality. Conclude with `le_rfl`.
-/
theorem sum_fr_le (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases h.lt_or_eq with h | h
  · exact (fr_lt_fr_of_lt_of_valid hV j i i' h h').le
  · subst h
    exact le_rfl

/- English proof (translation)
Unfold `posOf`. Use `congr 3`. Simplify using the standard rewrite rules.
-/
theorem sum_posOf_per (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  unfold posOf
  congr 3
  simp

/- English proof (translation)
Unfold `Frames.dist`. Rewrite using `[fr_add_mul_period hV]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dist_add_mul_period (hV : F.Valid L₁ N₁) (j x m : ℤ) : F.dist (j + m * F.J) (x + m * n') = F.dist j x := by
  unfold Frames.dist
  rw [fr_add_mul_period hV]
  congr 1
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.prod_range_succ, ih, ← Finset.prod_union (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)), ← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le m)) (hg (Nat.le_succ m))]`.
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
Establish `: X.toLate j = nonW X.F j` using `rfl`. Rewrite using `[this, nonW_eq hV, Finset.mem_filter, Finset.mem_Ioc]`.
-/
theorem mem_late_iff (hV : X.F.Valid L₁ N₁) (j x : ℤ) :
    x ∈ X.toLate j ↔ (eFr X.F (j - 1) < x ∧ x ≤ eFr X.F j) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have : X.toLate j = nonW X.F j := rfl
  rw [this, nonW_eq hV, Finset.mem_filter, Finset.mem_Ioc]

/- English proof (translation)
Establish `h1 : x % (n' : ℤ) = x' % (n' : ℤ)` using `by rw [← posOf_val, ← posOf_val, h]`. Establish `h2 : (n' : ℤ) ∣ x' - x` using `Int.ModEq.dvd h1`. Take `⟨m, hm⟩` from `h2`. Establish `hm' : x' = x + m * n'` using `by linarith [mul_comm (n' : ℤ) m]`. Use `⟨m, ?_, hm'⟩` and prove the remaining obligations.

Establish `a1` using `(mem_late_iff X hV j x).mp hx`. Establish `a2` using `(mem_late_iff X hV j' x').mp hx'`. Establish `p1 : eFr X.F (j + m * X.F.J) = eFr X.F j + m * n'` using `fr_add_mul_period hV j (r - 1) m`. Establish `p0 : eFr X.F (j + m * X.F.J - 1) = eFr X.F (j - 1) + m * n'`. Use `fr_add_mul_period hV (j - 1) (r - 1) m` as an intermediate fact.

Rewrite using `[show j + m * X.F.J - 1 = j - 1 + m * X.F.J by ring]`. Conclude with `this`. Conclude with `idx_unique (eFr_strictMono hV) (x := x') a2.1.1 a2.1.2 (by rw [p0]; linarith [a1.1.1]) (by rw [p1]; linarith [a1.1.2])`.
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
Unfold `Dat.Rj`. Establish `e : j + m * X.F.J - 1 = (j - 1) + m * X.F.J` using `by ring`. Rewrite using `[e, fr_add_mul_period hV (j - 1) 0 m, dist_add_mul_period hV]`.
-/
theorem sum_Rj_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Rj p K (j + m * X.F.J) = X.Rj p K j := by
  unfold Dat.Rj
  have e : j + m * X.F.J - 1 = (j - 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j - 1) 0 m, dist_add_mul_period hV]

/- English proof (translation)
Unfold `Dat.Pz`. Rewrite using `[dist_add_mul_period hV, sum_Rj_per X p K hV]`.
-/
theorem sum_Pz_per (hV : X.F.Valid L₁ N₁) (j x m : ℤ) :
    X.Pz p K (j + m * X.F.J) (x + m * n') = X.Pz p K j x := by
  unfold Dat.Pz
  rw [dist_add_mul_period hV, sum_Rj_per X p K hV]

/- English proof (translation)
Unfold `Dat.Qc`. Establish `e : j + m * X.F.J + 1 = (j + 1) + m * X.F.J` using `by ring`. Rewrite using `[e, fr_add_mul_period hV (j + 1) (r - 1) m, fr_add_mul_period hV j (r - 1) m, sum_Rj_per X p K hV, sum_Rj_per X p K hV]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_Qc_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Qc p K (j + m * X.F.J) = X.Qc p K j := by
  unfold Dat.Qc
  have e : j + m * X.F.J + 1 = (j + 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j + 1) (r - 1) m, fr_add_mul_period hV j (r - 1) m, sum_Rj_per X p K hV, sum_Rj_per X p K hV]
  congr 2
  ring

/- English proof (translation)
Take `⟨m, rfl, rfl⟩` from `exists_shift_of_posOf_eq_of_mem_late X hV hx hx' h`. Conclude with `(sum_Pz_per X p K hV j x m).symm`.
-/
theorem sum_uniqP (hV : X.F.Valid L₁ N₁) (j j' x x' : ℤ) (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : X.Pz p K j x = X.Pz p K j' x' := by
  obtain ⟨m, rfl, rfl⟩ := exists_shift_of_posOf_eq_of_mem_late X hV hx hx' h
  exact (sum_Pz_per X p K hV j x m).symm

/- English proof (translation)
Establish `e1 : X.F.fr (j + X.F.J - 1) i.val = X.F.fr (j - 1) i.val + 1 * n'`. Use `fr_add_mul_period hV (j - 1) i.val 1` as an intermediate fact. Rewrite using `[show j + (X.F.J : ℤ) - 1 = j - 1 + 1 * X.F.J by ring]`. Conclude with `this`. Establish `e2 : j + (X.F.J : ℤ) = j + 1 * X.F.J` using `by ring`.

Unfold `Dat.Bw`. Rewrite using `[e1, e2, sum_posOf_per, dist_add_mul_period hV, sum_Rj_per X p K hV]`.
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
Establish `hm` using `eFr_strictMono hV`. Establish `h1 : ∀ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) = ∏ x ∈ (Finset.Ioc ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) (j + 1))).filter (fun x => posOf n' x ∈ X.F.TT), φ (posOf n' x)`. Introduce `j _`. Establish `: X.toLate (j : ℤ) = nonW X.F j` using `rfl`. Rewrite using `[this, nonW_eq hV]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl h1, sum_prod_Ioc (fun i : ℕ => eFr X.F ((i : ℤ) - 1)) (fun a b hab => hm.monotone (by omega)) (fun x => posOf n' x ∈ X.F.TT) (fun x => φ (posOf n' x)) X.F.J]`. Establish `h2 : eFr X.F ((X.F.J : ℤ) - 1) = eFr X.F (((0 : ℕ) : ℤ) - 1) + n'`. Use `hV.2.1 (-1) (r - 1)` as an intermediate fact. Simplify using `only [eFr]`.

Establish `e1 : ((X.F.J : ℤ) - 1) = -1 + X.F.J` using `by ring`. Establish `e2 : (((0 : ℕ) : ℤ) - 1) = -1` using `by norm_num`. Rewrite using `[e1, e2, this]`. Simplify using `only [h2]`. Use `set a := eFr X.F (((0 : ℕ) : ℤ) - 1) with ha`.

Use `symm`. Use `Finset.prod_bij (fun x _ => posOf n' x) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `(Finset.mem_filter.mp hx).2`. Introduce `x hx y hy hxy`.

Conclude with `posOf_injOn a (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1) hxy`. Introduce `t ht`. Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `b0` using `Int.emod_nonneg ((t.val : ℤ) - (a + 1)) hn.ne'`. Establish `b1` using `Int.emod_lt_of_pos ((t.val : ℤ) - (a + 1)) hn`.

Establish `hpos : posOf n' (a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ)) = t`. Establish `e : a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ) = (t.val : ℤ) + (-(((t.val : ℤ) - (a + 1)) / (n' : ℤ))) * n'`. Use `Int.emod_add_mul_ediv ((t.val : ℤ) - (a + 1)) (n' : ℤ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e, sum_posOf_per, posOf_natCast]`.

Use `⟨a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ), ?_, hpos⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, Finset.mem_Ioc, hpos]`. Conclude with `⟨⟨by omega, by omega⟩, ht⟩`. Introduce `x _`. Both sides reduce to the same expression.
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
Unfold `Frames.LLset at hx`. Rewrite `hx` using `[Finset.mem_filter, Finset.mem_Ioo]`. Use `⟨(mem_late_iff X hV j x).mpr ⟨⟨hx.1.1, ?_⟩, hx.2⟩, hx.1.2⟩` and prove the remaining obligations. Conclude with `hx.1.2.le.trans (fr_zero_le_eFr hV j)`.
-/
theorem sum_LLsub (hV : X.F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ X.F.LLset j) : x ∈ X.toLate j ∧ x < X.F.fr j 0 := by
  classical
  unfold Frames.LLset at hx
  rw [Finset.mem_filter, Finset.mem_Ioo] at hx
  refine ⟨(mem_late_iff X hV j x).mpr ⟨⟨hx.1.1, ?_⟩, hx.2⟩, hx.1.2⟩
  exact hx.1.2.le.trans (fr_zero_le_eFr hV j)

/- English proof (translation)
Use `(mem_late_iff X hV j _).mpr ⟨⟨?_, ?_⟩, (hV.2.2.2.2.1 j i.val i.isLt).1⟩` and prove the remaining obligations. Establish `h1` using `hV.2.2.2.1 (j - 1)`. Rewrite `h1` using `[sub_add_cancel]`. Conclude with `lt_of_lt_of_le h1 (fr_zero_le hV j i.val i.isLt)`. Conclude with `sum_fr_le hV j i.val (r - 1) (by have := i.isLt; omega) (Nat.sub_lt (NeZero.pos r) Nat.one_pos)`.
-/
theorem sum_frlate (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) : X.F.fr j i.val ∈ X.toLate j := by
  refine (mem_late_iff X hV j _).mpr ⟨⟨?_, ?_⟩, (hV.2.2.2.2.1 j i.val i.isLt).1⟩
  · have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    exact lt_of_lt_of_le h1 (fr_zero_le hV j i.val i.isLt)
  · exact sum_fr_le hV j i.val (r - 1) (by have := i.isLt; omega) (Nat.sub_lt (NeZero.pos r) Nat.one_pos)

/- English proof (translation)
Establish `hinj : Function.Injective (fun i : Fin r => X.F.fr j i.val)`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h` into its components or cases. Conclude with `absurd hab (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j a.val b.val h b.isLt))`.

Conclude with `absurd hab.symm (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j b.val a.val h a.isLt))`. Establish `hU : X.toLate j = X.F.LLset j ∪ Finset.univ.image (fun i : Fin r => X.F.fr j i.val)`. Use extensionality with `x`. Rewrite using `[Finset.mem_union, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `a1` using `(mem_late_iff X hV j x).mp hx`. Distinguish the cases in `h0 : x < X.F.fr j 0`. Use `left`. Unfold `Frames.LLset`.

Rewrite using `[Finset.mem_filter, Finset.mem_Ioo]`. Conclude with `⟨⟨a1.1.1, h0⟩, a1.2⟩`. Use `right`. Take `⟨i, hi, rfl⟩` from `comb_frame_top X.F hV j x a1.2 (not_lt.mp h0) (r - 1) (Nat.sub_lt (NeZero.pos r) Nat.one_pos) a1.1.2`. Conclude with `⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩`.

Introduce and unpack `(hx | ⟨i, -, rfl⟩)`. Conclude with `(sum_LLsub X hV j x hx).1`. Conclude with `sum_frlate X hV j i`. Establish `hdisj : Disjoint (X.F.LLset j) (Finset.univ.image (fun i : Fin r => X.F.fr j i.val))`. Rewrite using `[Finset.disjoint_left]`.

Introduce `x hx hx'`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hx'`. Use `(sum_LLsub X hV j _ hx).2` as an intermediate fact. Use `fr_zero_le hV j i.val i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hU, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => hinj h)]`.
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
Use `le_trans ?_ (sum_card_nonW hV)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem J_le_card_TT_of_valid (hV : X.F.Valid L₁ N₁) : X.F.J ≤ X.F.TT.card := by
  classical
  refine le_trans ?_ (sum_card_nonW hV)
  calc X.F.J = ∑ _j ∈ Finset.range X.F.J, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.card_pos.mpr
      ⟨X.F.fr (j : ℤ) (⟨0, NeZero.pos r⟩ : Fin r).val, sum_frlate X hV (j : ℤ) ⟨0, NeZero.pos r⟩⟩

end GeoX

end Formalism.MainNotions.SelectionLemmas.Pf
