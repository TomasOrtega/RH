import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamImgApply
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CoarseLabelFactorisation

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Substitute `h` using the available equality. Break down `lt_trichotomy m 0 with hm | hm | hm` into its components or cases. Establish `: m * J ≤ -J` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Conclude with `hm`.

Establish `: J ≤ m * J` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem lam_m_zero {a b m J : ℤ} (ha : 0 ≤ a) (ha' : a < J) (hb : 0 ≤ b) (hb' : b < J) (h : b = a + m * J) :
    m = 0 := by
  subst h
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : m * J ≤ -J := by nlinarith
    omega
  · exact hm
  · have : J ≤ m * J := by nlinarith
    omega

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_ i hi`. Establish `: i = 0` using `by omega`.

Substitute `this` using the available equality. Conclude with `le_refl _`. Consider the case `succ k ih`. Introduce `hk i hi`. Break down `Nat.lt_or_ge i (k + 1) with h | h` into its components or cases.

Establish `h1` using `ih (by omega) i (by omega)`. Establish `h2` using `hV.2.2.1 j k hk`. Use linear arithmetic over natural numbers and integers. Establish `: i = k + 1` using `by omega`. Substitute `this` using the available equality.

Conclude with `le_refl _`.
-/
private theorem fr_le_fr_of_index_le {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (j : ℤ) : ∀ k, k < r → ∀ i ≤ k, F.fr j i ≤ F.fr j k := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    have : i = 0 := by omega
    subst this
    exact le_refl _
  | succ k ih =>
    intro hk i hi
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · have h1 := ih (by omega) i (by omega)
      have h2 := hV.2.2.1 j k hk
      omega
    · have : i = k + 1 := by omega
      subst this
      exact le_refl _

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_ h1 h2`. Conclude with `⟨0, le_refl _, le_antisymm h2 h1⟩`.

Consider the case `succ k ih`. Introduce `hk h1 h2`. Break down `le_or_gt x (F.fr j k) with h | h` into its components or cases. Take `⟨i, hi, hxi⟩` from `ih (by omega) h1 h`. Conclude with `⟨i, by omega, hxi⟩`.

Break down `lt_or_eq_of_le h2 with h' | h'` into its components or cases. Conclude with `absurd hx (hV.2.2.2.2.2.1 j k x hk h h')`. Conclude with `⟨k + 1, le_refl _, h'⟩`.
-/
private theorem exists_index_eq_fr_of_between {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (j x : ℤ) (hx : posOf n' x ∈ F.TT) :
    ∀ k, k < r → F.fr j 0 ≤ x → x ≤ F.fr j k → ∃ i ≤ k, x = F.fr j i := by
  intro k
  induction k with
  | zero =>
    intro _ h1 h2
    exact ⟨0, le_refl _, le_antisymm h2 h1⟩
  | succ k ih =>
    intro hk h1 h2
    rcases le_or_gt x (F.fr j k) with h | h
    · obtain ⟨i, hi, hxi⟩ := ih (by omega) h1 h
      exact ⟨i, by omega, hxi⟩
    · rcases lt_or_eq_of_le h2 with h' | h'
      · exact absurd hx (hV.2.2.2.2.2.1 j k x hk h h')
      · exact ⟨k + 1, le_refl _, h'⟩

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Simplify using `only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx`. Take `⟨⟨hx1, hx2⟩, hxT⟩` from `hx`. Establish `hW' : x ≤ X.F.fr (j - 1) (r - 1)` using `hW`. Take `⟨i, hi, rfl⟩` from `exists_index_eq_fr_of_between X.F hV (j - 1) x hxT (r - 1) (by omega) hx1 hW'`.

Use `⟨?_, i, by omega, rfl⟩` and prove the remaining obligations. Establish `hg` using `hV.2.2.2.1 (j - 1 - 1)`. Establish `h1 : j - 1 - 1 + 1 = j - 1` using `by ring`. Rewrite `hg` using `[h1]`. Establish `hm0` using `fr_le_fr_of_index_le X.F hV (j - 1 - 1) (r - 1) (by omega) 0 (Nat.zero_le _)`.

Establish `hmi` using `fr_le_fr_of_index_le X.F hV (j - 1) (r - 1) (by omega) i hi`. Establish `hm0i` using `fr_le_fr_of_index_le X.F hV (j - 1) i (by omega) 0 (Nat.zero_le _)`. Unfold `Dat.toLate`. Simplify using `only [Finset.mem_filter]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `Frames.letters`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, hmi⟩, hxT⟩`. Unfold `Frames.IsW`. Use linear arithmetic over natural numbers and integers.
-/
theorem lam_W_late {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j x : ℤ)
    (hx : x ∈ X.F.letters j) (hW : X.F.IsW j x) : x ∈ X.toLate (j - 1) ∧ ∃ i < r, x = X.F.fr (j - 1) i := by
  classical
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hx1, hx2⟩, hxT⟩ := hx
  have hW' : x ≤ X.F.fr (j - 1) (r - 1) := hW
  obtain ⟨i, hi, rfl⟩ := exists_index_eq_fr_of_between X.F hV (j - 1) x hxT (r - 1) (by omega) hx1 hW'
  refine ⟨?_, i, by omega, rfl⟩
  have hg := hV.2.2.2.1 (j - 1 - 1)
  have h1 : j - 1 - 1 + 1 = j - 1 := by ring
  rw [h1] at hg
  have hm0 := fr_le_fr_of_index_le X.F hV (j - 1 - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  have hmi := fr_le_fr_of_index_le X.F hV (j - 1) (r - 1) (by omega) i hi
  have hm0i := fr_le_fr_of_index_le X.F hV (j - 1) i (by omega) 0 (Nat.zero_le _)
  unfold Dat.toLate
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hmi⟩, hxT⟩
  · unfold Frames.IsW
    omega

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `h1` using `hV.2.2.2.1 a`. Establish `h2` using `fr_le_fr_of_index_le F hV (a + 1) (r - 1) (by omega) 0 (Nat.zero_le _)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem fr_last_lt_fr_last_succ {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (a : ℤ) : F.fr a (r - 1) < F.fr (a + 1) (r - 1) := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := hV.2.2.2.1 a
  have h2 := fr_le_fr_of_index_le F hV (a + 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  omega

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h` using `fr_last_lt_fr_last_succ F hV (a + k)`.

Use `push_cast`. Rewrite using `[← add_assoc]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem fr_last_le_fr_last_add_nat {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (a : ℤ) : ∀ k : ℕ, F.fr a (r - 1) ≤ F.fr (a + k) (r - 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := fr_last_lt_fr_last_succ F hV (a + k)
    push_cast
    rw [← add_assoc]
    omega

/- English proof (translation)
Establish `h1` using `fr_last_le_fr_last_add_nat F hV a (b - a).toNat`. Rewrite `h1` using `[Int.toNat_of_nonneg (by omega), show a + (b - a) = b by ring]`. Conclude with `h1`.
-/
private theorem fr_last_monotone {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (a b : ℤ) (h : a ≤ b) : F.fr a (r - 1) ≤ F.fr b (r - 1) := by
  have h1 := fr_last_le_fr_last_add_nat F hV a (b - a).toNat
  rw [Int.toNat_of_nonneg (by omega), show a + (b - a) = b by ring] at h1
  exact h1

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')`. Establish `hper` using `hV.2.1 (s - 1) (r - 1)`. Rewrite `hper` using `[show s - 1 + (F.J : ℤ) = s + F.J - 1 by ring]`. Establish `m1` using `fr_last_monotone F hV (s - 1) (a - 1) (by omega)`. Establish `m2` using `fr_last_monotone F hV a (s + F.J - 1) (by omega)`.

Establish `m3` using `fr_last_monotone F hV (s - 1) (b - 1) (by omega)`. Establish `m4` using `fr_last_monotone F hV b (s + F.J - 1) (by omega)`. Establish `e1 : x % (n' : ℤ) + n' * (x / n') = x` using `by rw [Int.emod_def]; ring`. Establish `e2 : x' % (n' : ℤ) + n' * (x' / n') = x'` using `by rw [Int.emod_def]; ring`. Establish `hq` using `lam_m_zero (a := x - F.fr (s - 1) (r - 1) - 1) (b := x' - F.fr (s - 1) (r - 1) - 1) (m := x' / n' - x / n') (J := n') (by omega) (by omega) (by omega) (by omega) (by linear_combination e1 - e2 - hp)`.

Establish `hxx : x = x'`. Establish `hq' : x' / (n' : ℤ) = x / n'` using `by linarith`. Rewrite `e2` using `[hq']`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, hxx⟩` and prove the remaining obligations.

Substitute `hxx` using the available equality. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Use `fr_last_monotone F hV a (b - 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Use `fr_last_monotone F hV b (a - 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem eq_of_mod_eq_of_mem_Ioc_fr_last {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (s a b x x' : ℤ) (hsa : s ≤ a) (haJ : a < s + F.J) (hsb : s ≤ b)
    (hbJ : b < s + F.J) (hx1 : F.fr (a - 1) (r - 1) < x) (hx2 : x ≤ F.fr a (r - 1))
    (hx1' : F.fr (b - 1) (r - 1) < x') (hx2' : x' ≤ F.fr b (r - 1))
    (hp : x % (n' : ℤ) = x' % (n' : ℤ)) : a = b ∧ x = x' := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hper := hV.2.1 (s - 1) (r - 1)
  rw [show s - 1 + (F.J : ℤ) = s + F.J - 1 by ring] at hper
  have m1 := fr_last_monotone F hV (s - 1) (a - 1) (by omega)
  have m2 := fr_last_monotone F hV a (s + F.J - 1) (by omega)
  have m3 := fr_last_monotone F hV (s - 1) (b - 1) (by omega)
  have m4 := fr_last_monotone F hV b (s + F.J - 1) (by omega)
  have e1 : x % (n' : ℤ) + n' * (x / n') = x := by rw [Int.emod_def]; ring
  have e2 : x' % (n' : ℤ) + n' * (x' / n') = x' := by rw [Int.emod_def]; ring
  have hq := lam_m_zero (a := x - F.fr (s - 1) (r - 1) - 1) (b := x' - F.fr (s - 1) (r - 1) - 1)
    (m := x' / n' - x / n') (J := n') (by omega) (by omega) (by omega) (by omega)
    (by linear_combination e1 - e2 - hp)
  have hxx : x = x' := by
    have hq' : x' / (n' : ℤ) = x / n' := by linarith
    rw [hq'] at e2
    linarith
  refine ⟨?_, hxx⟩
  subst hxx
  rcases lt_trichotomy a b with h | h | h
  · have := fr_last_monotone F hV a (b - 1) (by omega)
    omega
  · exact h
  · have := fr_last_monotone F hV b (a - 1) (by omega)
    omega

/- English proof (translation)
Unfold `Dat.toLate at h`. Simplify using `only [Finset.mem_filter] at h`. Take `⟨h1, h2⟩` from `h`. Unfold `Frames.letters at h1`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc] at h1`.

Unfold `Frames.IsW at h2`. Conclude with `⟨by omega, h1.1.2, h1.2⟩`.
-/
private theorem mem_Ioc_and_posOf_mem_of_mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) (h : x ∈ X.toLate j) :
    X.F.fr (j - 1) (r - 1) < x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  unfold Dat.toLate at h
  simp only [Finset.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  unfold Frames.letters at h1
  simp only [Finset.mem_filter, Finset.mem_Icc] at h1
  unfold Frames.IsW at h2
  exact ⟨by omega, h1.1.2, h1.2⟩

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `h0` using `fr_le_fr_of_index_le X.F hV (j - 1) (r - 1) (by omega) 0 (Nat.zero_le _)`. Unfold `Dat.toLate`. Simplify using `only [Finset.mem_filter]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `Frames.letters`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, h2⟩, h3⟩`. Unfold `Frames.IsW`. Use linear arithmetic over natural numbers and integers.
-/
private theorem mem_late_of_mem_Ioc_of_posOf_mem {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ}
    (hV : X.F.Valid L₁ N₁) (j x : ℤ) (h1 : X.F.fr (j - 1) (r - 1) < x) (h2 : x ≤ X.F.fr j (r - 1))
    (h3 : posOf n' x ∈ X.F.TT) : x ∈ X.toLate j := by
  classical
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h0 := fr_le_fr_of_index_le X.F hV (j - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  unfold Dat.toLate
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, h2⟩, h3⟩
  · unfold Frames.IsW
    omega

/- English proof (translation)
Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')`. Unfold `posOf at h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only at h'`. Use `clear h`.

Establish `a1` using `Int.emod_nonneg x (ne_of_gt hn)`. Establish `a2` using `Int.emod_lt_of_pos x hn`. Establish `b1` using `Int.emod_nonneg x' (ne_of_gt hn)`. Establish `b2` using `Int.emod_lt_of_pos x' hn`. Generalize the expression as in `x % (n' : ℤ) = u at *`.

Generalize the expression as in `x' % (n' : ℤ) = v at *`. Rewrite `h'` using `[Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem emod_eq_of_posOf_eq' {n' : ℕ} [NeZero n'] {x x' : ℤ} (h : posOf n' x = posOf n' x') :
    x % (n' : ℤ) = x' % (n' : ℤ) := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  unfold posOf at h
  have h' := congrArg Fin.val h
  simp only at h'
  clear h
  have a1 := Int.emod_nonneg x (ne_of_gt hn)
  have a2 := Int.emod_lt_of_pos x hn
  have b1 := Int.emod_nonneg x' (ne_of_gt hn)
  have b2 := Int.emod_lt_of_pos x' hn
  generalize x % (n' : ℤ) = u at *
  generalize x' % (n' : ℤ) = v at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Rewrite using `[pow_succ, ← Nat.div_div_eq_div_mul, Nat.log_div_base, ih]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem nat_log_div_pow_eq_sub (p N : ℕ) : ∀ d : ℕ, Nat.log p (N / p ^ d) = Nat.log p N - d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.log_div_base, ih]
    omega

/- English proof (translation)
Unfold `Dat.Rj`. Rewrite using `[div_mul_eq_div_div, ← Nat.cast_pow, Nat.floor_div_natCast]`. Conclude with `nat_log_div_pow_eq_sub p _ _`.
-/
private theorem Rj_eq_log_floor {n' r : ℕ} (X : Dat n' r) (p K : ℕ) (j : ℤ) :
    X.Rj p K j = Nat.log p ⌊X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * ↑X.Ns)⌋₊ - X.F.dist j (X.F.fr (j - 1) 0) := by
  unfold Dat.Rj
  rw [div_mul_eq_div_div, ← Nat.cast_pow, Nat.floor_div_natCast]
  exact nat_log_div_pow_eq_sub p _ _

/- English proof (translation)
Establish `hRj` using `Rj_eq_log_floor X p K j`. Establish `hRc` using `Rj_eq_log_floor X p K c`. Establish `hRc1` using `Rj_eq_log_floor X p K (c + 1)`. Unfold `Dat.Pz Dat.Qc`. Rewrite using `[hRj, hRc, hRc1, ← pow_add]`.

Use `congr 1`. Unfold `Frames.dist`. Use linear arithmetic over natural numbers and integers.
-/
private theorem Pz_eq_Pz_mul_Qc {n' r : ℕ} (X : Dat n' r) (p K : ℕ) (j c x x' s : ℤ)
    (h1 : X.F.fr c (r - 1) = X.F.fr (j - 1) (r - 1) + s)
    (h2 : X.F.fr (c - 1) 0 = X.F.fr (j - 1 - 1) 0 + s)
    (h3 : X.F.fr (c + 1) (r - 1) = X.F.fr j (r - 1) + s)
    (h4 : X.F.fr (c + 1 - 1) 0 = X.F.fr (j - 1) 0 + s)
    (hx' : x' = x + s) (hxT : x ≤ X.F.fr (j - 1) (r - 1))
    (hTT : X.F.fr (j - 1) (r - 1) < X.F.fr j (r - 1))
    (hA : X.F.fr (j - 1) 0 ≤ X.F.fr j (r - 1))
    (hB : X.F.fr (j - 1 - 1) 0 ≤ X.F.fr (j - 1) (r - 1))
    (hC : X.F.fr (j - 1 - 1) 0 < X.F.fr (j - 1) 0) :
    X.Pz p K j x = X.Pz p K c x' * X.Qc p K c := by
  have hRj := Rj_eq_log_floor X p K j
  have hRc := Rj_eq_log_floor X p K c
  have hRc1 := Rj_eq_log_floor X p K (c + 1)
  unfold Dat.Pz Dat.Qc
  rw [hRj, hRc, hRc1, ← pow_add]
  congr 1
  unfold Frames.dist
  omega

/- English proof (translation)
Introduce `p n' r K _ _ _ X hH _ _`. Establish `hV` using `hH.valid`. Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `hn : (0 : ℤ) < n'` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')`. Establish `hJ : 1 ≤ X.F.J` using `hV.1`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j j' x hx x' hx' hp`. Take `⟨a1, a2, a3⟩` from `mem_Ioc_and_posOf_mem_of_mem_late X _ x hx`. Take `⟨b1, b2, b3⟩` from `mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'`. Establish `hj` using `j.isLt`.

Establish `hj'` using `j'.isLt`. Take `⟨e1, e2⟩` from `eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 _ _ x x' (by omega) (by omega) (by omega) (by omega) a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)`. Conclude with `⟨Fin.ext (by omega), e2⟩`. Introduce `j j' x hx hW x' hx' hW' hp`. Take `⟨hl, -⟩` from `lam_W_late X hV _ x hx hW`.

Take `⟨hl', -⟩` from `lam_W_late X hV _ x' hx' hW'`. Take `⟨a1, a2, a3⟩` from `mem_Ioc_and_posOf_mem_of_mem_late X _ x hl`. Take `⟨b1, b2, b3⟩` from `mem_Ioc_and_posOf_mem_of_mem_late X _ x' hl'`. Establish `hj` using `j.isLt`. Establish `hj'` using `j'.isLt`.

Take `⟨e1, e2⟩` from `eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV (-1) _ _ x x' (by omega) (by omega) (by omega) (by omega) a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)`. Conclude with `⟨Fin.ext (by omega), e2⟩`. Introduce `j j' x hx hW x' hx' hp`. Take `⟨hl, i, hi, hxi⟩` from `lam_W_late X hV _ x hx hW`. Take `⟨a1, a2, a3⟩` from `mem_Ioc_and_posOf_mem_of_mem_late X _ x hl`.

Take `⟨b1, b2, b3⟩` from `mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'`. Establish `hj` using `j.isLt`. Establish `hj'` using `j'.isLt`. Establish `hTT : X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) < X.F.fr ((j : ℕ) : ℤ) (r - 1)`. Establish `h` using `fr_last_lt_fr_last_succ X.F hV (((j : ℕ) : ℤ) - 1)`.

Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hf1` using `fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1) (r - 1) (by omega) 0 (Nat.zero_le _)`. Establish `hf2` using `fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1 - 1) (r - 1) (by omega) 0 (Nat.zero_le _)`. Establish `hg` using `hV.2.2.2.1 (((j : ℕ) : ℤ) - 1 - 1)`. Rewrite `hg` using `[sub_add_cancel]`.

Establish `hA : X.F.fr (((j : ℕ) : ℤ) - 1) 0 ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1)` using `by omega`. Establish `hC : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 < X.F.fr (((j : ℕ) : ℤ) - 1) 0` using `by omega`. Establish `hB : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 ≤ X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1)` using `by omega`. Break down `Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0` into its components or cases. Establish `q1 : X.F.fr (((j : ℕ) : ℤ) - 1 + X.F.J - 1) (r - 1) = X.F.fr (((j : ℕ) : ℤ) - 1 - 1) (r - 1) + n'`.

Rewrite using `[show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]`. Conclude with `hV.2.1 _ _`. Establish `q2` using `hV.2.1 (((j : ℕ) : ℤ) - 1) (r - 1)`. Establish `hpy : (x + n') % (n' : ℤ) = x' % (n' : ℤ)`. Rewrite using `[Int.add_emod_right]`.

Conclude with `emod_eq_of_posOf_eq' hp`. Take `⟨e1, e2⟩` from `eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1 + X.F.J) ((j' : ℕ) : ℤ) (x + n') x' (by omega) (by omega) (by omega) (by omega) (by rw [q1]; omega) (by rw [q2]; omega) b1 b2 hpy`. Use `⟨⟨i, hi, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← e1, ← e2, hxi]`. Conclude with `(hV.2.1 _ _).symm`.

Rewrite using `[← e1, ← e2]`. Use `Pz_eq_Pz_mul_Qc X p K _ _ x _ n' (hV.2.1 _ _) ?_ ?_ ?_ rfl a2 hTT hA hB hC` and prove the remaining obligations. Rewrite using `[show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]`. Conclude with `hV.2.1 _ _`. Rewrite using `[show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 = ((j : ℕ) : ℤ) + X.F.J by ring]`.

Conclude with `hV.2.1 _ _`. Rewrite using `[show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 - 1 = ((j : ℕ) : ℤ) - 1 + X.F.J by ring]`. Conclude with `hV.2.1 _ _`. Take `⟨e1, e2⟩` from `eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1) ((j' : ℕ) : ℤ) x x' (by omega) (by omega) (by omega) (by omega) a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)`. Use `⟨⟨i, hi, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← e1, ← e2]`. Conclude with `hxi`. Rewrite using `[← e1, ← e2]`. Use `Pz_eq_Pz_mul_Qc X p K _ (((j : ℕ) : ℤ) - 1) x x 0 (by rw [add_zero]) (by rw [add_zero]) ?_ ?_ (by rw [add_zero]) a2 hTT hA hB hC` and prove the remaining obligations. Rewrite using `[sub_add_cancel, add_zero]`.

Rewrite using `[sub_add_cancel, add_zero]`. Introduce `t ht`. Establish `hper` using `hV.2.1 (-1) (r - 1)`. Take `⟨y, hy⟩ : ∃ y : ℤ, y = X.F.fr (-1) (r - 1) + 1 + (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) % (n' : ℤ)` from `⟨_, rfl⟩`. Establish `hy0` using `Int.emod_nonneg (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) (ne_of_gt hn)`.

Establish `hy1` using `Int.emod_lt_of_pos (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) hn`. Establish `ht'` using `t.isLt`. Establish `hypos : posOf n' y = t`. Establish `hmod : y % (n' : ℤ) = ((t : ℕ) : ℤ)`. Establish `hy2 : y = ((t : ℕ) : ℤ) + (n' : ℤ) * (-((((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) / (n' : ℤ)))`.

Rewrite using `[hy, Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy2, Int.add_mul_emod_self_left]`. Conclude with `Int.emod_eq_of_lt (by omega) (by omega)`. Unfold `posOf`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[hmod, Int.toNat_natCast]`. Conclude with `Nat.mod_eq_of_lt ht'`. Establish `hyB : y ≤ X.F.fr (((X.F.J - 1 : ℕ)) : ℤ) (r - 1)`.

Rewrite using `[show (((X.F.J - 1 : ℕ)) : ℤ) = -1 + X.F.J by omega, hper]`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∃ k : ℕ, y ≤ X.F.fr (k : ℤ) (r - 1)` using `⟨_, hyB⟩`. Establish `hk0` using `Nat.find_spec hex`. Establish `hk0le` using `Nat.find_min' hex hyB`.

Establish `hmin : ∀ m < Nat.find hex, ¬ y ≤ X.F.fr (m : ℤ) (r - 1)` using `fun m hm => Nat.find_min hex hm`. Generalize the expression as in `Nat.find hex = k0 at hk0 hk0le hmin`. Establish `hlow : X.F.fr ((k0 : ℤ) - 1) (r - 1) < y`. Break down `Nat.eq_zero_or_pos k0 with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Rewrite using `[Nat.cast_zero, zero_sub]`. Use linear arithmetic over natural numbers and integers. Establish `h` using `hmin (k0 - 1) (by omega)`. Rewrite `h` using `[show (((k0 - 1 : ℕ)) : ℤ) = (k0 : ℤ) - 1 by omega]`. Use linear arithmetic over natural numbers and integers.

Use `⟨⟨k0, by omega⟩, y, ?_, hypos⟩` and prove the remaining obligations. Conclude with `mem_late_of_mem_Ioc_of_posOf_mem X hV _ y hlow hk0 (by rw [hypos]; exact ht)`.
-/
theorem restLamGeo (C₀ : ℝ) : RestLamGeo C₀ := by
  classical
  intro p n' r K _ _ _ X hH _ _
  have hV := hH.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hJ : 1 ≤ X.F.J := hV.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j j' x hx x' hx' hp
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hx
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 _ _ x x' (by omega) (by omega) (by omega) (by omega)
      a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)
    exact ⟨Fin.ext (by omega), e2⟩
  · intro j j' x hx hW x' hx' hW' hp
    obtain ⟨hl, -⟩ := lam_W_late X hV _ x hx hW
    obtain ⟨hl', -⟩ := lam_W_late X hV _ x' hx' hW'
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hl
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hl'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV (-1) _ _ x x' (by omega) (by omega) (by omega) (by omega)
      a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)
    exact ⟨Fin.ext (by omega), e2⟩
  · intro j j' x hx hW x' hx' hp
    obtain ⟨hl, i, hi, hxi⟩ := lam_W_late X hV _ x hx hW
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hl
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'
    have hj := j.isLt
    have hj' := j'.isLt
    have hTT : X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) < X.F.fr ((j : ℕ) : ℤ) (r - 1) := by
      have h := fr_last_lt_fr_last_succ X.F hV (((j : ℕ) : ℤ) - 1)
      rwa [sub_add_cancel] at h
    have hf1 := fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
    have hf2 := fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1 - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
    have hg := hV.2.2.2.1 (((j : ℕ) : ℤ) - 1 - 1)
    rw [sub_add_cancel] at hg
    have hA : X.F.fr (((j : ℕ) : ℤ) - 1) 0 ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1) := by omega
    have hC : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 < X.F.fr (((j : ℕ) : ℤ) - 1) 0 := by omega
    have hB : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 ≤ X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) := by omega
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
    · have q1 : X.F.fr (((j : ℕ) : ℤ) - 1 + X.F.J - 1) (r - 1)
          = X.F.fr (((j : ℕ) : ℤ) - 1 - 1) (r - 1) + n' := by
        rw [show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]
        exact hV.2.1 _ _
      have q2 := hV.2.1 (((j : ℕ) : ℤ) - 1) (r - 1)
      have hpy : (x + n') % (n' : ℤ) = x' % (n' : ℤ) := by
        rw [Int.add_emod_right]
        exact emod_eq_of_posOf_eq' hp
      obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1 + X.F.J) ((j' : ℕ) : ℤ) (x + n') x'
        (by omega) (by omega) (by omega) (by omega) (by rw [q1]; omega) (by rw [q2]; omega) b1 b2 hpy
      refine ⟨⟨i, hi, ?_⟩, ?_⟩
      · rw [← e1, ← e2, hxi]
        exact (hV.2.1 _ _).symm
      · rw [← e1, ← e2]
        refine Pz_eq_Pz_mul_Qc X p K _ _ x _ n' (hV.2.1 _ _) ?_ ?_ ?_ rfl a2 hTT hA hB hC
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]
          exact hV.2.1 _ _
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 = ((j : ℕ) : ℤ) + X.F.J by ring]
          exact hV.2.1 _ _
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 - 1 = ((j : ℕ) : ℤ) - 1 + X.F.J by ring]
          exact hV.2.1 _ _
    · obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1) ((j' : ℕ) : ℤ) x x'
        (by omega) (by omega) (by omega) (by omega) a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)
      refine ⟨⟨i, hi, ?_⟩, ?_⟩
      · rw [← e1, ← e2]
        exact hxi
      · rw [← e1, ← e2]
        refine Pz_eq_Pz_mul_Qc X p K _ (((j : ℕ) : ℤ) - 1) x x 0 (by rw [add_zero]) (by rw [add_zero])
          ?_ ?_ (by rw [add_zero]) a2 hTT hA hB hC
        · rw [sub_add_cancel, add_zero]
        · rw [sub_add_cancel, add_zero]
  · intro t ht
    have hper := hV.2.1 (-1) (r - 1)
    obtain ⟨y, hy⟩ : ∃ y : ℤ, y = X.F.fr (-1) (r - 1) + 1
        + (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) % (n' : ℤ) := ⟨_, rfl⟩
    have hy0 := Int.emod_nonneg (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) (ne_of_gt hn)
    have hy1 := Int.emod_lt_of_pos (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) hn
    have ht' := t.isLt
    have hypos : posOf n' y = t := by
      have hmod : y % (n' : ℤ) = ((t : ℕ) : ℤ) := by
        have hy2 : y = ((t : ℕ) : ℤ)
            + (n' : ℤ) * (-((((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) / (n' : ℤ))) := by
          rw [hy, Int.emod_def]
          ring
        rw [hy2, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      unfold posOf
      apply Fin.ext
      simp only
      rw [hmod, Int.toNat_natCast]
      exact Nat.mod_eq_of_lt ht'
    have hyB : y ≤ X.F.fr (((X.F.J - 1 : ℕ)) : ℤ) (r - 1) := by
      rw [show (((X.F.J - 1 : ℕ)) : ℤ) = -1 + X.F.J by omega, hper]
      omega
    have hex : ∃ k : ℕ, y ≤ X.F.fr (k : ℤ) (r - 1) := ⟨_, hyB⟩
    have hk0 := Nat.find_spec hex
    have hk0le := Nat.find_min' hex hyB
    have hmin : ∀ m < Nat.find hex, ¬ y ≤ X.F.fr (m : ℤ) (r - 1) := fun m hm => Nat.find_min hex hm
    generalize Nat.find hex = k0 at hk0 hk0le hmin
    have hlow : X.F.fr ((k0 : ℤ) - 1) (r - 1) < y := by
      rcases Nat.eq_zero_or_pos k0 with h0 | h0
      · subst h0
        rw [Nat.cast_zero, zero_sub]
        omega
      · have h := hmin (k0 - 1) (by omega)
        rw [show (((k0 - 1 : ℕ)) : ℤ) = (k0 : ℤ) - 1 by omega] at h
        omega
    refine ⟨⟨k0, by omega⟩, y, ?_, hypos⟩
    exact mem_late_of_mem_Ioc_of_posOf_mem X hV _ y hlow hk0 (by rw [hypos]; exact ht)

/- English proof (translation)
Introduce `p n' r K _ _ _ X hH la e j i`. Establish `hV` using `hH.valid`. Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`.

Establish `hle : X.F.fr ((j : ℕ) : ℤ) i ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1)` using `fr_le_fr_of_index_le X.F hV _ (r - 1) (by omega) i (by omega)`. Establish `h0i : X.F.fr ((j : ℕ) : ℤ) 0 ≤ X.F.fr ((j : ℕ) : ℤ) i` using `fr_le_fr_of_index_le X.F hV _ i hi 0 (Nat.zero_le _)`. Establish `hg` using `hV.2.2.2.1 (((j : ℕ) : ℤ) - 1)`. Rewrite `hg` using `[sub_add_cancel]`. Establish `h00` using `fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1) (r - 1) (by omega) 0 (Nat.zero_le _)`.

Establish `hT` using `(hV.2.2.2.2.1 ((j : ℕ) : ℤ) i hi).1`. Establish `hmem : X.F.fr ((j : ℕ) : ℤ) i ∈ X.F.letters ((j : ℕ) : ℤ)`. Unfold `Frames.letters`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, hle⟩, hT⟩`.

Establish `hnW : ¬ X.F.IsW ((j : ℕ) : ℤ) (X.F.fr ((j : ℕ) : ℤ) i)`. Unfold `Frames.IsW`. Use linear arithmetic over natural numbers and integers. Unfold `Dat.bfam`. Rewrite using `[if_pos hmem, if_neg hnW, if_pos h0i]`.

Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl]`. Unfold `Dat.eZ`. Rewrite using `[dif_pos (by omega)]`. Use `congr 1`.

Use `ext`. Establish `hm : ((j : ℕ) : ℤ) % (X.F.J : ℤ) = ((j : ℕ) : ℤ)` using `Int.emod_eq_of_lt (by omega) (by omega)`. Simplify using `only [hm, Int.toNat_natCast]`. Conclude with `Nat.mod_eq_of_lt hj`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Establish `hbl` using `b.isLt`. Break down `lt_trichotomy (b : ℕ) (i : ℕ) with hlt | heq | hgt` into its components or cases.

Establish `h1` using `hV.2.2.1 ((j : ℕ) : ℤ) b (by omega)`. Establish `h2` using `fr_le_fr_of_index_le X.F hV ((j : ℕ) : ℤ) i hi ((b : ℕ) + 1) (by omega)`. Use linear arithmetic over natural numbers and integers. Conclude with `Fin.ext heq`. Establish `h1` using `hV.2.2.1 ((j : ℕ) : ℤ) i (by omega)`.

Establish `h2` using `fr_le_fr_of_index_le X.F hV ((j : ℕ) : ℤ) b hbl ((i : ℕ) + 1) (by omega)`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem restLamTau : RestLamTau := by
  classical
  intro p n' r K _ _ _ X hH la e j i
  have hV := hH.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hi := i.isLt
  have hj := j.isLt
  have hle : X.F.fr ((j : ℕ) : ℤ) i ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1) :=
    fr_le_fr_of_index_le X.F hV _ (r - 1) (by omega) i (by omega)
  have h0i : X.F.fr ((j : ℕ) : ℤ) 0 ≤ X.F.fr ((j : ℕ) : ℤ) i :=
    fr_le_fr_of_index_le X.F hV _ i hi 0 (Nat.zero_le _)
  have hg := hV.2.2.2.1 (((j : ℕ) : ℤ) - 1)
  rw [sub_add_cancel] at hg
  have h00 := fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  have hT := (hV.2.2.2.2.1 ((j : ℕ) : ℤ) i hi).1
  have hmem : X.F.fr ((j : ℕ) : ℤ) i ∈ X.F.letters ((j : ℕ) : ℤ) := by
    unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hle⟩, hT⟩
  have hnW : ¬ X.F.IsW ((j : ℕ) : ℤ) (X.F.fr ((j : ℕ) : ℤ) i) := by
    unfold Frames.IsW
    omega
  unfold Dat.bfam
  rw [if_pos hmem, if_neg hnW, if_pos h0i]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    unfold Dat.eZ
    rw [dif_pos (by omega)]
    congr 1
    ext
    have hm : ((j : ℕ) : ℤ) % (X.F.J : ℤ) = ((j : ℕ) : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [hm, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt hj
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    have hbl := b.isLt
    rcases lt_trichotomy (b : ℕ) (i : ℕ) with hlt | heq | hgt
    · have h1 := hV.2.2.1 ((j : ℕ) : ℤ) b (by omega)
      have h2 := fr_le_fr_of_index_le X.F hV ((j : ℕ) : ℤ) i hi ((b : ℕ) + 1) (by omega)
      omega
    · exact Fin.ext heq
    · have h1 := hV.2.2.1 ((j : ℕ) : ℤ) i (by omega)
      have h2 := fr_le_fr_of_index_le X.F hV ((j : ℕ) : ℤ) b hbl ((i : ℕ) + 1) (by omega)
      omega
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
The claim follows from `restLamInj_of C₀ (restLamGeo C₀) restLamTau`.
-/
theorem restLamInj (C₀ : ℝ) : RestLamInj C₀ := restLamInj_of C₀ (restLamGeo C₀) restLamTau

end Formalism.MainNotions.SelectionLemmas.Pf
