import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopDegreeComparison

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Per

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Use `hV.2.1 (j + (k : ℤ) * F.J) i` as an intermediate fact. Rewrite using `[show j + ((k : ℤ) + 1) * F.J = j + (k : ℤ) * F.J + F.J by ring, this, ih]; ring`.

Consider the case `pred k ih`. Use `hV.2.1 (j + (-(k : ℤ) - 1) * F.J) i` as an intermediate fact. Rewrite `this` using `[show j + (-(k : ℤ) - 1) * F.J + F.J = j + -(k : ℤ) * F.J by ring, ih]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fr_period (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    F.fr (j + m * F.J) i = F.fr j i + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := hV.2.1 (j + (k : ℤ) * F.J) i
    rw [show j + ((k : ℤ) + 1) * F.J = j + (k : ℤ) * F.J + F.J by ring, this, ih]; ring
  | pred k ih =>
    have := hV.2.1 (j + (-(k : ℤ) - 1) * F.J) i
    rw [show j + (-(k : ℤ) - 1) * F.J + F.J = j + -(k : ℤ) * F.J by ring, ih] at this
    linarith

/- English proof (translation)
Unfold `posOf`. Use `congr 2`. Rewrite using `[Int.add_mul_emod_self_right]`.
-/
theorem posOf_add_mul (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  unfold posOf
  congr 2
  rw [Int.add_mul_emod_self_right]

/- English proof (translation)
Establish `hJ : (1 : ℤ) ≤ F.J` using `by exact_mod_cast hV.1`. Take `⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j % F.J` from `⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))⟩`. Establish `hkJ : (k : ℤ) < F.J` using `hk ▸ Int.emod_lt_of_pos _ (by omega)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hj⟩ : ∃ m : ℤ, j = (k : ℤ) + m * F.J := by`. Use `⟨j / F.J, ?_⟩` and prove the remaining obligations.

Establish `h` using `((Int.ediv_emod_unique (a := j) (b := (F.J : ℤ)) (by omega)).1 ⟨rfl, rfl⟩).1`. Rewrite using `[hk]`. Combine the linear relations using `[mul_comm (F.J : ℤ) (j / F.J)]`. Establish `e1 : F.fr j (r - 1) = F.fr (k : ℤ) (r - 1) + m * n'`. Rewrite using `[hj]`.

Conclude with `fr_period hV _ _ _`. Establish `e2 : F.fr (j - 1) 0 = F.fr ((k : ℤ) - 1) 0 + m * n'`. Rewrite using `[show j - 1 = ((k : ℤ) - 1) + m * F.J by rw [hj]; ring]`. Conclude with `fr_period hV _ _ _`. Establish `e3 : F.fr (j - 1) (r - 1) = F.fr ((k : ℤ) - 1) (r - 1) + m * n'`.

Rewrite using `[show j - 1 = ((k : ℤ) - 1) + m * F.J by rw [hj]; ring]`. Conclude with `fr_period hV _ _ _`. Establish `hpos : posOf n' (x - m * n') = posOf n' x`. Establish `h` using `posOf_add_mul (n' := n') (x - m * n') m`. Rewrite `h` using `[sub_add_cancel]`.

Conclude with `h.symm`. Use `⟨k, by exact_mod_cast hkJ, x - m * n', ?_, ?_, hpos, ?_⟩` and prove the remaining obligations. Simplify using `only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx ⊢`. Rewrite `hx` using `[e1, e2]`. Rewrite using `[hpos]`.

Conclude with `⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, hx.2⟩`. Simplify using `only [Frames.IsW] at hW ⊢`. Rewrite `hW` using `[e3]`. Introduce `h`. Conclude with `hW (by linarith)`.

Simplify using `only [Frames.dist]`. Rewrite using `[e1]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem late_reduce (hV : F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ F.letters j) (hW : ¬ F.IsW j x) :
    ∃ j' : ℕ, j' < F.J ∧ ∃ x' : ℤ, x' ∈ F.letters (j' : ℤ) ∧ ¬ F.IsW (j' : ℤ) x' ∧ posOf n' x' = posOf n' x ∧
      F.dist (j' : ℤ) x' = F.dist j x := by
  have hJ : (1 : ℤ) ≤ F.J := by exact_mod_cast hV.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j % F.J :=
    ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))⟩
  have hkJ : (k : ℤ) < F.J := hk ▸ Int.emod_lt_of_pos _ (by omega)
  obtain ⟨m, hj⟩ : ∃ m : ℤ, j = (k : ℤ) + m * F.J := by
    refine ⟨j / F.J, ?_⟩
    have h := ((Int.ediv_emod_unique (a := j) (b := (F.J : ℤ)) (by omega)).1 ⟨rfl, rfl⟩).1
    rw [hk]
    linarith [mul_comm (F.J : ℤ) (j / F.J)]
  have e1 : F.fr j (r - 1) = F.fr (k : ℤ) (r - 1) + m * n' := by
    rw [hj]
    exact fr_period hV _ _ _
  have e2 : F.fr (j - 1) 0 = F.fr ((k : ℤ) - 1) 0 + m * n' := by
    rw [show j - 1 = ((k : ℤ) - 1) + m * F.J by rw [hj]; ring]
    exact fr_period hV _ _ _
  have e3 : F.fr (j - 1) (r - 1) = F.fr ((k : ℤ) - 1) (r - 1) + m * n' := by
    rw [show j - 1 = ((k : ℤ) - 1) + m * F.J by rw [hj]; ring]
    exact fr_period hV _ _ _
  have hpos : posOf n' (x - m * n') = posOf n' x := by
    have h := posOf_add_mul (n' := n') (x - m * n') m
    rw [sub_add_cancel] at h
    exact h.symm
  refine ⟨k, by exact_mod_cast hkJ, x - m * n', ?_, ?_, hpos, ?_⟩
  · simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    rw [e1, e2] at hx
    rw [hpos]
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, hx.2⟩
  · simp only [Frames.IsW] at hW ⊢
    rw [e3] at hW
    intro h
    exact hW (by linarith)
  · simp only [Frames.dist]
    rw [e1]
    congr 1
    ring

end Per

section Lab

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

open Classical in

def ellExp (l : Fin n' × Fin (r + K) →₀ ℕ) (j : ℤ) : ℤ × Fin (r + K) →₀ ℕ :=
  Finsupp.onFinset (X.toLate j ×ˢ (Finset.univ : Finset (Fin (r + K))))
    (fun v => if v.1 ∈ X.toLate j then l (posOf n' v.1, v.2) / p ^ X.F.dist j v.1 else 0)
    (fun v hv => by
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      by_contra h
      exact hv (if_neg h))

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ellExp_apply (l : Fin n' × Fin (r + K) →₀ ℕ) (j : ℤ) (v : ℤ × Fin (r + K)) :
    ellExp X p K l j v = if v.1 ∈ X.toLate j then l (posOf n' v.1, v.2) / p ^ X.F.dist j v.1 else 0 := rfl

open Classical in
/- English proof (translation)
Unfold `imgMon ellExp`. Rewrite using `[Finsupp.sum_apply, Finsupp.onFinset_sum _ (fun v => by simp)]`. Rewrite using `[Finset.sum_product]`. Use `Finset.sum_congr rfl (fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single c]`.

Distinguish the cases in `h : posOf n' x = t`. Substitute `h` using the available equality. Simplify using `[hx]`. Simplify using `[hx, h, Finsupp.single_apply, Prod.ext_iff]`. Introduce `b _ hb`.

Simplify using `[Finsupp.single_apply, Prod.ext_iff, hb]`. Simplify using the standard rewrite rules.
-/
theorem img_ellExp (l : Fin n' × Fin (r + K) →₀ ℕ) (j : ℤ) (t : Fin n') (c : Fin (r + K)) :
    imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ X.F.dist j v.1) (ellExp X p K l j) (t, c) =
      ∑ x ∈ X.toLate j, if posOf n' x = t then p ^ X.F.dist j x * (l (t, c) / p ^ X.F.dist j x) else 0 := by
  unfold imgMon ellExp
  rw [Finsupp.sum_apply, Finsupp.onFinset_sum _ (fun v => by simp)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.sum_eq_single c]
  · by_cases h : posOf n' x = t
    · subst h
      simp [hx]
    · simp [hx, h, Finsupp.single_apply, Prod.ext_iff]
  · intro b _ hb
    simp [Finsupp.single_apply, Prod.ext_iff, hb]
  · simp

end Lab

/- English proof (translation)
Rewrite using `[phSeg, aeval_monomial, map_one, one_mul, imgMon, Finsupp.sum, monomial_sum_one, Finsupp.prod]`. Use `Finset.prod_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[← X_pow_eq_monomial, ← pow_mul]`.
-/
private theorem phSeg_monomial_one {O : Type} [CommRing O] {n' r : ℕ} [NeZero n'] (K p : ℕ)
    (F : Frames n' r) (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) :
    phSeg O K p F j (monomial e 1) =
      monomial (imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
        (fun v => p ^ F.dist j v.1) e) (1 : O) := by
  rw [phSeg, aeval_monomial, map_one, one_mul, imgMon, Finsupp.sum, monomial_sum_one, Finsupp.prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [← X_pow_eq_monomial, ← pow_mul]

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')`. Establish `hm : x % (n' : ℤ) = y % (n' : ℤ)`. Establish `h` using `congrArg Fin.val hxy`. Simplify using `only [posOf] at h`. Establish `ha` using `Int.emod_nonneg x hn.ne'`.

Establish `hb` using `Int.emod_lt_of_pos x hn`. Establish `hc` using `Int.emod_nonneg y hn.ne'`. Establish `hd` using `Int.emod_lt_of_pos y hn`. Generalize the expression as in `x % (n' : ℤ) = a at *`. Generalize the expression as in `y % (n' : ℤ) = b at *`.

Rewrite `h` using `[Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Take `⟨q, hq⟩` from `(show x ≡ y [ZMOD n'] from hm).dvd`. Break down `lt_trichotomy q 0 with hq0 | hq0 | hq0` into its components or cases. Use the polynomial consequences of the given equalities and inequalities.

Rewrite `hq` using `[hq0, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem eq_of_posOf_eq_of_dist_lt {n' : ℕ} [NeZero n'] {x y : ℤ} (hxy : posOf n' x = posOf n' y)
    (h1 : x - y < n') (h2 : y - x < n') : x = y := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hm : x % (n' : ℤ) = y % (n' : ℤ) := by
    have h := congrArg Fin.val hxy
    simp only [posOf] at h
    have ha := Int.emod_nonneg x hn.ne'
    have hb := Int.emod_lt_of_pos x hn
    have hc := Int.emod_nonneg y hn.ne'
    have hd := Int.emod_lt_of_pos y hn
    generalize x % (n' : ℤ) = a at *
    generalize y % (n' : ℤ) = b at *
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  obtain ⟨q, hq⟩ := (show x ≡ y [ZMOD n'] from hm).dvd
  rcases lt_trichotomy q 0 with hq0 | hq0 | hq0
  · nlinarith
  · rw [hq0, mul_zero] at hq
    linarith
  · nlinarith

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Conclude with `le_rfl`. Consider the case `succ k ih`.

Introduce `hk`. Conclude with `le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j k hk))`.
-/
private theorem fr_first_le_fr_of_valid {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ k, k < r → F.fr j 0 ≤ F.fr j k := by
  intro k
  induction k with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j k hk))

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `step : ∀ i : ℤ, F.fr i (r - 1) < F.fr (i + 1) (r - 1)` using `fun i => lt_of_lt_of_le (hV.2.2.2.1 i) (fr_first_le_fr_of_valid hV (i + 1) (r - 1) (by omega))`. Establish `hmono : StrictMono (fun i : ℤ => F.fr i (r - 1))` using `strictMono_int_of_lt_succ step`. Establish `hper : F.fr ((F.J : ℤ) - 1) (r - 1) = F.fr (-1) (r - 1) + n'`. Establish `h` using `fr_period hV (-1) (r - 1) 1`.

Rewrite `h` using `[show (-1 : ℤ) + 1 * F.J = F.J - 1 by ring, one_mul]`. Conclude with `h`. Establish `bnd : ∀ (j : ℕ), j < F.J → ∀ x, x ∈ F.letters (j : ℤ) → ¬ F.IsW (j : ℤ) x → F.fr ((j : ℤ) - 1) (r - 1) < x ∧ x ≤ F.fr (j : ℤ) (r - 1) ∧ F.fr (-1) (r - 1) < x ∧ x ≤ F.fr (-1) (r - 1) + n'`. Introduce `j hj x hx hW`. Simplify using `only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx`.

Simplify using `only [Frames.IsW, not_le] at hW`. Establish `a1 : F.fr (-1) (r - 1) ≤ F.fr ((j : ℤ) - 1) (r - 1)` using `hmono.monotone (by omega)`. Establish `a2 : F.fr (j : ℤ) (r - 1) ≤ F.fr ((F.J : ℤ) - 1) (r - 1)` using `hmono.monotone (by omega)`. Conclude with `⟨hW, hx.1.2, by linarith, by linarith⟩`. Take `⟨b1, c1, d1, e1⟩` from `bnd j1 hj1 x1 h1 h1'`.

Take `⟨b2, c2, d2, e2⟩` from `bnd j2 hj2 x2 h2 h2'`. Establish `hx : x1 = x2` using `eq_of_posOf_eq_of_dist_lt hp (by linarith) (by linarith)`. Substitute `hx` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Break down `Nat.lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `: F.fr (j1 : ℤ) (r - 1) ≤ F.fr ((j2 : ℤ) - 1) (r - 1)` using `hmono.monotone (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: F.fr (j2 : ℤ) (r - 1) ≤ F.fr ((j1 : ℤ) - 1) (r - 1)` using `hmono.monotone (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem eq_of_posOf_eq_of_mem_letters_not_isW {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) {j1 j2 : ℕ} (hj1 : j1 < F.J) (hj2 : j2 < F.J) {x1 x2 : ℤ}
    (h1 : x1 ∈ F.letters (j1 : ℤ)) (h1' : ¬ F.IsW (j1 : ℤ) x1)
    (h2 : x2 ∈ F.letters (j2 : ℤ)) (h2' : ¬ F.IsW (j2 : ℤ) x2)
    (hp : posOf n' x1 = posOf n' x2) : j1 = j2 ∧ x1 = x2 := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have step : ∀ i : ℤ, F.fr i (r - 1) < F.fr (i + 1) (r - 1) := fun i =>
    lt_of_lt_of_le (hV.2.2.2.1 i) (fr_first_le_fr_of_valid hV (i + 1) (r - 1) (by omega))
  have hmono : StrictMono (fun i : ℤ => F.fr i (r - 1)) := strictMono_int_of_lt_succ step
  have hper : F.fr ((F.J : ℤ) - 1) (r - 1) = F.fr (-1) (r - 1) + n' := by
    have h := fr_period hV (-1) (r - 1) 1
    rw [show (-1 : ℤ) + 1 * F.J = F.J - 1 by ring, one_mul] at h
    exact h
  have bnd : ∀ (j : ℕ), j < F.J → ∀ x, x ∈ F.letters (j : ℤ) → ¬ F.IsW (j : ℤ) x →
      F.fr ((j : ℤ) - 1) (r - 1) < x ∧ x ≤ F.fr (j : ℤ) (r - 1) ∧
        F.fr (-1) (r - 1) < x ∧ x ≤ F.fr (-1) (r - 1) + n' := by
    intro j hj x hx hW
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [Frames.IsW, not_le] at hW
    have a1 : F.fr (-1) (r - 1) ≤ F.fr ((j : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    have a2 : F.fr (j : ℤ) (r - 1) ≤ F.fr ((F.J : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    exact ⟨hW, hx.1.2, by linarith, by linarith⟩
  obtain ⟨b1, c1, d1, e1⟩ := bnd j1 hj1 x1 h1 h1'
  obtain ⟨b2, c2, d2, e2⟩ := bnd j2 hj2 x2 h2 h2'
  have hx : x1 = x2 := eq_of_posOf_eq_of_dist_lt hp (by linarith) (by linarith)
  subst hx
  refine ⟨?_, rfl⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : F.fr (j1 : ℤ) (r - 1) ≤ F.fr ((j2 : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    linarith
  · have : F.fr (j2 : ℤ) (r - 1) ≤ F.fr ((j1 : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    linarith

/- English proof (translation)
Introduce `p n' r K _ _ _ D O _ hH l hl`. Establish `hV` using `hH.valid`. Establish `hp : 0 < p` using `hH.prime.pos`. Establish `hpp : ∀ k : ℕ, 0 < p ^ k` using `fun k => pow_pos hp k`. Establish `hmem : ∀ (j x : ℤ), x ∈ D.toLate j ↔ x ∈ D.F.letters j ∧ ¬ D.F.IsW j x` using `fun j x => by`.

Simplify using `[Dat.toLate, Finset.mem_filter]`. Use `set S : Fin n' × Fin (r + K) →₀ ℕ := ∑ j ∈ Finset.range D.F.J, imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ D.F.dist (j : ℤ) v.1) (ellExp D p K l j) with hS`. Establish `hSval : ∀ t c, S (t, c) = ∑ j ∈ Finset.range D.F.J, ∑ x ∈ D.toLate (j : ℤ), if posOf n' x = t then p ^ D.F.dist (j : ℤ) x * (l (t, c) / p ^ D.F.dist (j : ℤ) x) else 0`. Introduce `t c`. Rewrite using `[hS, Finsupp.finset_sum_apply]`.

Conclude with `Finset.sum_congr rfl (fun j _ => img_ellExp D p K l j t c)`. Establish `hS1 : ∀ t c (j0 : ℕ) (x0 : ℤ), j0 < D.F.J → x0 ∈ D.toLate (j0 : ℤ) → posOf n' x0 = t → S (t, c) = p ^ D.F.dist (j0 : ℤ) x0 * (l (t, c) / p ^ D.F.dist (j0 : ℤ) x0)`. Introduce `t c j0 x0 hj0 hx0 ht`. Rewrite using `[hSval, Finset.sum_eq_single j0, Finset.sum_eq_single x0, if_pos ht]`. Introduce `x hx hne`.

Rewrite using `[if_neg]`. Introduce `hxt`. Rewrite `hx`, `hx0` using `[hmem]`. Conclude with `hne (eq_of_posOf_eq_of_mem_letters_not_isW hV hj0 hj0 hx.1 hx.2 hx0.1 hx0.2 (hxt.trans ht.symm)).2`. Introduce `h`.

Conclude with `absurd hx0 h`. Introduce `b hb hne`. Use `Finset.sum_eq_zero (fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `hxt`.

Rewrite `hx`, `hx0` using `[hmem]`. Conclude with `hne (eq_of_posOf_eq_of_mem_letters_not_isW hV (Finset.mem_range.1 hb) hj0 hx.1 hx.2 hx0.1 hx0.2 (hxt.trans ht.symm)).1`. Introduce `h`. Conclude with `absurd (Finset.mem_range.2 hj0) h`. Establish `hS0 : ∀ t c, (∀ (j : ℕ), j < D.F.J → ∀ x ∈ D.toLate (j : ℤ), posOf n' x ≠ t) → S (t, c) = 0`.

Introduce `t c h`. Rewrite using `[hSval]`. Use `Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun x hx => ?_))` and prove the remaining obligations. Rewrite using `[if_neg (h j (Finset.mem_range.1 hj) x hx)]`. Establish `hle : ∀ t c, S (t, c) ≤ l (t, c)`.

Introduce `t c`. Distinguish the cases in `h : ∃ j0 : ℕ, j0 < D.F.J ∧ ∃ x0 ∈ D.toLate (j0 : ℤ), posOf n' x0 = t`. Take `⟨j0, hj0, x0, hx0, ht⟩` from `h`. Rewrite using `[hS1 t c j0 x0 hj0 hx0 ht]`. Conclude with `Nat.mul_div_le _ _`.

Use `push_neg at h`. Rewrite using `[hS0 t c h]`. Conclude with `Nat.zero_le _`. Establish `hsum : l - S + S = l`. Use extensionality with `⟨t, c⟩`.

Rewrite using `[Finsupp.add_apply, Finsupp.tsub_apply]`. Use `hle t c` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨l - S, fun j => ellExp D p K l j, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx hW c`.

Take `⟨j', hj', x', hx', hW', hpos, hdist⟩` from `late_reduce hV j x hx hW`. Rewrite using `[Finsupp.tsub_apply, ← hpos, hS1 _ c j' x' hj' ((hmem _ _).2 ⟨hx', hW'⟩) rfl, ← hdist]`. Establish `h0` using `Nat.mod_add_div (l (posOf n' x', c)) (p ^ D.F.dist (j' : ℤ) x')`. Establish `hlt` using `Nat.mod_lt (l (posOf n' x', c)) (hpp (D.F.dist (j' : ℤ) x'))`. Generalize the expression as in `l (posOf n' x', c) = a at *`.

Generalize the expression as in `p ^ D.F.dist (j' : ℤ) x' = b at *`. Generalize the expression as in `b * (a / b) = w at *`. Generalize the expression as in `a % b = m at *`. Use linear arithmetic over natural numbers and integers. Introduce `j`.

Use `⟨fun v hv => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [ellExp_apply] at hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (if_neg h)`. Simplify using `only [ellExp_apply] split_ifs with h`.

Rewrite `h` using `[hmem]`. Use `hl j v.1 h.1 h.2 v.2` as an intermediate fact. Rewrite using `[Nat.div_lt_iff_lt_mul (hpp _), ← pow_add, Nat.add_comm (D.Rj p K j)]`. Conclude with `this`. Conclude with `hpp _`.

Simplify using `only [phSeg_monomial_one]`. Rewrite using `[← monomial_sum_one, monomial_mul, one_mul]`. Conclude with `congrArg (fun m => monomial m (1 : O)) hsum.symm`.
-/
theorem coarse_label_factorisation : CoarseLabelFactorisation := by
  intro p n' r K _ _ _ D O _ hH l hl
  have hV := hH.valid
  have hp : 0 < p := hH.prime.pos
  have hpp : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp k
  have hmem : ∀ (j x : ℤ), x ∈ D.toLate j ↔ x ∈ D.F.letters j ∧ ¬ D.F.IsW j x := fun j x => by
    simp [Dat.toLate, Finset.mem_filter]
  set S : Fin n' × Fin (r + K) →₀ ℕ := ∑ j ∈ Finset.range D.F.J,
    imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
      (fun v => p ^ D.F.dist (j : ℤ) v.1) (ellExp D p K l j) with hS
  have hSval : ∀ t c, S (t, c) = ∑ j ∈ Finset.range D.F.J, ∑ x ∈ D.toLate (j : ℤ),
      if posOf n' x = t then p ^ D.F.dist (j : ℤ) x * (l (t, c) / p ^ D.F.dist (j : ℤ) x) else 0 := by
    intro t c
    rw [hS, Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl (fun j _ => img_ellExp D p K l j t c)
  have hS1 : ∀ t c (j0 : ℕ) (x0 : ℤ), j0 < D.F.J → x0 ∈ D.toLate (j0 : ℤ) → posOf n' x0 = t →
      S (t, c) = p ^ D.F.dist (j0 : ℤ) x0 * (l (t, c) / p ^ D.F.dist (j0 : ℤ) x0) := by
    intro t c j0 x0 hj0 hx0 ht
    rw [hSval, Finset.sum_eq_single j0, Finset.sum_eq_single x0, if_pos ht]
    · intro x hx hne
      rw [if_neg]
      intro hxt
      rw [hmem] at hx hx0
      exact hne (eq_of_posOf_eq_of_mem_letters_not_isW hV hj0 hj0 hx.1 hx.2 hx0.1 hx0.2 (hxt.trans ht.symm)).2
    · intro h
      exact absurd hx0 h
    · intro b hb hne
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [if_neg]
      intro hxt
      rw [hmem] at hx hx0
      exact hne (eq_of_posOf_eq_of_mem_letters_not_isW hV (Finset.mem_range.1 hb) hj0 hx.1 hx.2 hx0.1 hx0.2
        (hxt.trans ht.symm)).1
    · intro h
      exact absurd (Finset.mem_range.2 hj0) h
  have hS0 : ∀ t c, (∀ (j : ℕ), j < D.F.J → ∀ x ∈ D.toLate (j : ℤ), posOf n' x ≠ t) →
      S (t, c) = 0 := by
    intro t c h
    rw [hSval]
    refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun x hx => ?_))
    rw [if_neg (h j (Finset.mem_range.1 hj) x hx)]
  have hle : ∀ t c, S (t, c) ≤ l (t, c) := by
    intro t c
    by_cases h : ∃ j0 : ℕ, j0 < D.F.J ∧ ∃ x0 ∈ D.toLate (j0 : ℤ), posOf n' x0 = t
    · obtain ⟨j0, hj0, x0, hx0, ht⟩ := h
      rw [hS1 t c j0 x0 hj0 hx0 ht]
      exact Nat.mul_div_le _ _
    · push_neg at h
      rw [hS0 t c h]
      exact Nat.zero_le _
  have hsum : l - S + S = l := by
    ext ⟨t, c⟩
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    have := hle t c
    omega
  refine ⟨l - S, fun j => ellExp D p K l j, ?_, ?_, ?_⟩
  · intro j x hx hW c
    obtain ⟨j', hj', x', hx', hW', hpos, hdist⟩ := late_reduce hV j x hx hW
    rw [Finsupp.tsub_apply, ← hpos, hS1 _ c j' x' hj' ((hmem _ _).2 ⟨hx', hW'⟩) rfl, ← hdist]
    have h0 := Nat.mod_add_div (l (posOf n' x', c)) (p ^ D.F.dist (j' : ℤ) x')
    have hlt := Nat.mod_lt (l (posOf n' x', c)) (hpp (D.F.dist (j' : ℤ) x'))
    generalize l (posOf n' x', c) = a at *
    generalize p ^ D.F.dist (j' : ℤ) x' = b at *
    generalize b * (a / b) = w at *
    generalize a % b = m at *
    omega
  · intro j
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · simp only [ellExp_apply] at hv
      by_contra h
      exact hv (if_neg h)
    · simp only [ellExp_apply]
      split_ifs with h
      · rw [hmem] at h
        have := hl j v.1 h.1 h.2 v.2
        rw [Nat.div_lt_iff_lt_mul (hpp _), ← pow_add, Nat.add_comm (D.Rj p K j)]
        exact this
      · exact hpp _
  · simp only [phSeg_monomial_one]
    rw [← monomial_sum_one, monomial_mul, one_mul]
    exact congrArg (fun m => monomial m (1 : O)) hsum.symm

end Formalism.MainNotions.SelectionLemmas.Pf
