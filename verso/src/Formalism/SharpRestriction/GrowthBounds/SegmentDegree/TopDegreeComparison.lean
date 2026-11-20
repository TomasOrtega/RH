import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantMultihomogeneous
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopOccursInAtMostTwoSegments

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Break down `lt_trichotomy a b with h | h | h` into its components or cases. It suffices to derive a contradiction. Use `hm.monotone (show a ≤ b - 1 by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`.

It suffices to derive a contradiction. Use `hm.monotone (show b ≤ a - 1 by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem idx_unique {e : ℤ → ℤ} (hm : StrictMono e) {a b x : ℤ} (h1 : e (a - 1) < x) (h2 : x ≤ e a)
    (h3 : e (b - 1) < x) (h4 : x ≤ e b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exfalso
    have := hm.monotone (show a ≤ b - 1 by omega)
    linarith
  · exact h
  · exfalso
    have := hm.monotone (show b ≤ a - 1 by omega)
    linarith

section U

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Take `⟨hJ, hper, hinc, hgap, -, -, -, -, -⟩` from `hV`. Establish `hperT : ∀ t : ℤ, ∀ (j' : ℤ) i, F.fr (j' + t * F.J) i = F.fr j' i + t * n'`. Introduce `t`. Proceed by induction on `t using Int.induction_on with`. Consider the case `zero => intro j' i`.

Simplify using the standard rewrite rules. Consider the case `succ t ih`. Introduce `j' i`. Establish `e : j' + (t + 1) * F.J = (j' + t * F.J) + F.J` using `by ring`. Rewrite using `[e, hper, ih]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `pred t ih`. Introduce `j' i`. Establish `e1` using `hper (j' + (-(t : ℤ) - 1) * F.J) i`. Establish `e : j' + (-(t : ℤ) - 1) * F.J + F.J = j' + -(t : ℤ) * F.J` using `by ring`.

Rewrite `e1` using `[e, ih]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hin : ∀ (j' : ℤ) (i : ℕ), i ≤ r - 1 → F.fr j' 0 ≤ F.fr j' i`. Introduce `j' i`. Proceed by induction on `i with`.

Consider the case `zero => intro _`. Conclude with `le_rfl`. Consider the case `succ i ih`. Introduce `hi`. Use `hinc j' i (by omega)` as an intermediate fact.

Combine the linear relations using `[ih (by omega)]`. Establish `hr0 : ∀ j' : ℤ, F.fr j' 0 ≤ F.fr j' (r - 1)` using `fun j' => hin j' (r - 1) le_rfl`. Establish `mono0 : StrictMono (fun j' : ℤ => F.fr j' 0)` using `strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 j'; linarith)`. Establish `monoL : StrictMono (fun j' : ℤ => F.fr j' (r - 1))` using `strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 (j' + 1); linarith)`. Establish `key : ∀ (g j' : ℤ) (y : ℤ), F.fr (g - 1) (r - 1) < y → y < F.fr g 0 → F.fr (j' - 1) 0 ≤ y → y ≤ F.fr j' (r - 1) → j' = g`.

Introduce `g j' y h1 h2 h3 h4`. Break down `lt_trichotomy j' g with h | h | h` into its components or cases. It suffices to derive a contradiction. Use `monoL.monotone (show j' ≤ g - 1 by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h`. It suffices to derive a contradiction. Use `mono0.monotone (show g ≤ j' - 1 by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hz`.

Simplify using `only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx`. Take `⟨⟨hz1, hz2⟩, -⟩` from `hz`. Take `⟨⟨hx1, hx2⟩, -⟩` from `hx`. Establish `hmod : x % (n' : ℤ) = z % (n' : ℤ)`. Rewrite using `[← posOf_val, ← posOf_val, hxz]`.

Take `⟨t, ht⟩` from `Int.ModEq.dvd hmod`. Establish `hxt : x = z + (-t) * n'` using `by linarith`. Establish `g1` using `hperT (-t) ((j0 : ℤ) - 1) (r - 1)`. Establish `g2` using `hperT (-t) (j0 : ℤ) 0`. Establish `e1 : (j0 : ℤ) - 1 + -t * F.J = ((j0 : ℤ) + -t * F.J) - 1` using `by ring`.

Rewrite `g1` using `[e1]`. Establish `hjj` using `key ((j0 : ℤ) + -t * F.J) (j : ℤ) x (by rw [g1, hxt]; linarith) (by rw [g2, hxt]; linarith) hx1 hx2`. Establish `hJ1 : (1 : ℤ) ≤ F.J` using `by exact_mod_cast hJ`. Establish `ht0 : t = 0`. Establish `hj' : (j : ℤ) < F.J` using `by exact_mod_cast hj`.

Establish `hj0' : (j0 : ℤ) < F.J` using `by exact_mod_cast hj0`. Break down `lt_trichotomy t 0 with h | h | h` into its components or cases. It suffices to derive a contradiction. Establish `: (1 : ℤ) ≤ -t` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `h`. It suffices to derive a contradiction. Establish `: (1 : ℤ) ≤ t` using `by omega`. Use the polynomial consequences of the given equalities and inequalities. Substitute `ht0` using the available equality.

Prove the components needed by the constructor for the conclusion. Simplify using `at hjj`. Conclude with `hjj` after adjusting the coercions. Simplify using `using hxt`.
-/
theorem LL_unique (hV : F.Valid L₁ N₁) (j0 : ℕ) (hj0 : j0 < F.J) (z : ℤ) (hz : z ∈ F.LLset (j0 : ℤ))
    (j : ℕ) (hj : j < F.J) (x : ℤ) (hx : x ∈ F.letters (j : ℤ)) (hxz : posOf n' x = posOf n' z) :
    j = j0 ∧ x = z := by
  obtain ⟨hJ, hper, hinc, hgap, -, -, -, -, -⟩ := hV

  have hperT : ∀ t : ℤ, ∀ (j' : ℤ) i, F.fr (j' + t * F.J) i = F.fr j' i + t * n' := by
    intro t
    induction t using Int.induction_on with
    | zero => intro j' i; simp
    | succ t ih =>
      intro j' i
      have e : j' + (t + 1) * F.J = (j' + t * F.J) + F.J := by ring
      rw [e, hper, ih]
      ring
    | pred t ih =>
      intro j' i
      have e1 := hper (j' + (-(t : ℤ) - 1) * F.J) i
      have e : j' + (-(t : ℤ) - 1) * F.J + F.J = j' + -(t : ℤ) * F.J := by ring
      rw [e, ih] at e1
      linarith

  have hin : ∀ (j' : ℤ) (i : ℕ), i ≤ r - 1 → F.fr j' 0 ≤ F.fr j' i := by
    intro j' i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have := hinc j' i (by omega)
      linarith [ih (by omega)]
  have hr0 : ∀ j' : ℤ, F.fr j' 0 ≤ F.fr j' (r - 1) := fun j' => hin j' (r - 1) le_rfl
  have mono0 : StrictMono (fun j' : ℤ => F.fr j' 0) :=
    strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 j'; linarith)
  have monoL : StrictMono (fun j' : ℤ => F.fr j' (r - 1)) :=
    strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 (j' + 1); linarith)

  have key : ∀ (g j' : ℤ) (y : ℤ), F.fr (g - 1) (r - 1) < y → y < F.fr g 0 →
      F.fr (j' - 1) 0 ≤ y → y ≤ F.fr j' (r - 1) → j' = g := by
    intro g j' y h1 h2 h3 h4
    rcases lt_trichotomy j' g with h | h | h
    · exfalso
      have := monoL.monotone (show j' ≤ g - 1 by omega)
      linarith
    · exact h
    · exfalso
      have := mono0.monotone (show g ≤ j' - 1 by omega)
      linarith

  simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hz
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
  obtain ⟨⟨hx1, hx2⟩, -⟩ := hx
  have hmod : x % (n' : ℤ) = z % (n' : ℤ) := by
    rw [← posOf_val, ← posOf_val, hxz]
  obtain ⟨t, ht⟩ := Int.ModEq.dvd hmod

  have hxt : x = z + (-t) * n' := by linarith
  have g1 := hperT (-t) ((j0 : ℤ) - 1) (r - 1)
  have g2 := hperT (-t) (j0 : ℤ) 0
  have e1 : (j0 : ℤ) - 1 + -t * F.J = ((j0 : ℤ) + -t * F.J) - 1 := by ring
  rw [e1] at g1
  have hjj := key ((j0 : ℤ) + -t * F.J) (j : ℤ) x (by rw [g1, hxt]; linarith) (by rw [g2, hxt]; linarith) hx1 hx2
  have hJ1 : (1 : ℤ) ≤ F.J := by exact_mod_cast hJ
  have ht0 : t = 0 := by
    have hj' : (j : ℤ) < F.J := by exact_mod_cast hj
    have hj0' : (j0 : ℤ) < F.J := by exact_mod_cast hj0
    rcases lt_trichotomy t 0 with h | h | h
    · exfalso
      have : (1 : ℤ) ≤ -t := by omega
      nlinarith
    · exact h
    · exfalso
      have : (1 : ℤ) ≤ t := by omega
      nlinarith
  subst ht0
  constructor
  · simp at hjj
    exact_mod_cast hjj
  · simpa using hxt

end U

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ _ hX b y l hy hl hdeg hne j0 hj0 z hz`. Establish `hV` using `hX.valid`. Establish `hj0' : j0 < X.F.J` using `Finset.mem_range.mp hj0`. Establish `hzz` using `hz`. Unfold `Frames.LLset at hzz`.

Rewrite `hzz` using `[Finset.mem_filter, Finset.mem_Ioo]`. Take `⟨⟨hz1, hz2⟩, hzT⟩` from `hzz`. Establish `hzW : ¬ X.F.IsW (j0 : ℤ) z` using `not_le.mpr hz1`. Establish `hzl : z ∈ X.F.letters (j0 : ℤ)`. Unfold `Frames.letters`.

Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨(fr_zero_le_eFr hV _).trans hz1.le, hz2.le.trans (fr_zero_le_eFr hV _)⟩, hzT⟩`. Use `set t := posOf n' z with ht`. Use `set P : ℕ := p ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ)) with hP`. Establish `hδ : ∀ j ∈ Finset.range X.F.J, DegAt t (if j = j0 then P * b j0 z else 0) (X.phc p K O (j : ℤ) (y j))`.

Introduce `j hj m' hm'`. Establish `hj' : j < X.F.J` using `Finset.mem_range.mp hj`. Take `⟨m, hm, rfl⟩` from `supp_aeval_pow (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ (X.F.dist (j : ℤ) v.1 + X.Rj p K (j : ℤ))) (y j) hm'`. Establish `hsup` using `XX'_supported O X.F (j : ℤ) _ _ _ (hy j).1.1`. Establish `hT : ∀ v ∈ m.support, v.1 ∈ X.F.letters (j : ℤ)`.

Introduce `v hv`. Establish `hvv : v ∈ (y j).vars` using `(mem_vars_iff_mem_support v).mpr ⟨m, hm, hv⟩`. Conclude with `((mem_supported.mp hsup) (Finset.mem_coe.mpr hvv)).1`. Establish `hPol : y j ∈ Pol O (r + K) (b j)` using `by rw [← segDeg_eq_Pol]; exact (hy j).1.2`. Rewrite using `[multideg_imgMon (fun x : ℤ => posOf n' x) (fun x : ℤ => p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ))) m t, sum_eq_multideg (fun x => if posOf n' x = t then p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ)) else 0) m (X.F.letters (j : ℤ)) hT]`.

Distinguish the cases in `hjj : j = j0`. Substitute `hjj` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single z]`. Rewrite using `[if_pos rfl, mem_Pol_iff.mp hPol m hm z]`. Introduce `x hx hxz`.

Rewrite using `[if_neg, zero_mul]`. Introduce `h`. Conclude with `hxz (LL_unique hV j hj0' z hz j hj' x hx h).2`. Introduce `h`. Conclude with `absurd hzl h`.

Rewrite using `[if_neg hjj]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[if_neg, zero_mul]`. Introduce `h`. Conclude with `hjj (LL_unique hV j0 hj0' z hz j hj' x hx h).1`.

Establish `hU` using `degAt_mul (degAt_prod _ _ _ hδ) (degAt_monomial l (1 : O) t)`. Rewrite `hU` using `[Finset.sum_ite_eq' (Finset.range X.F.J) j0, if_pos hj0]`. Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Establish `hm0'` using `MvPolynomial.mem_support_iff.mpr hm0`. Rewrite `hdeg` using `[RRdeg_eq_Pol]`.

Establish `ha' : X.a' p K t = P * b j0 z + multideg l t` using `(mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hU m0 hm0')`. Establish `hP0 : 0 < P` using `Nat.pow_pos hX.prime.pos`. Establish `hl' : multideg l t ≤ (r + K) * (P - 1)`. Unfold `multideg`. Use `Finset.sum_le_card_nsmul Finset.univ (fun c : Fin (r + K) => l (t, c)) (P - 1) (fun c _ => Nat.le_sub_one_of_lt (hl (j0 : ℤ) z hzl hzW c))` as an intermediate fact.

Simplify using `using this`. Establish `hrK : 0 < r + K` using `Nat.add_pos_left (NeZero.pos r) K`. Establish `hlt : X.a' p K t < (b j0 z + (r + K)) * P`. Rewrite using `[ha']`. Establish `: (r + K) * (P - 1) < (r + K) * P` using `Nat.mul_lt_mul_of_pos_left (by omega) hrK`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hltR : (X.a' p K t : ℝ) < ((b j0 z : ℝ) + Dat.k (r` using `r) K) * (P : ℝ) := by`. Unfold `Dat.k`. Conclude with `hlt` after adjusting the coercions. Establish `hPR : (0 : ℝ) < (P : ℝ)` using `by exact_mod_cast hP0`.

Establish `hPe : ((p : ℝ) ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ))) = (P : ℝ)` using `by rw [hP]; push_cast; rfl`. Rewrite using `[hPe, sub_lt_iff_lt_add, div_lt_iff₀ hPR]`. Conclude with `hltR`.
-/
theorem top_degree_comparison : TopDegreeComparison := by
  intro p n' r K _ _ _ X O _ _ hX b y l hy hl hdeg hne j0 hj0 z hz
  classical
  have hV := hX.valid
  have hj0' : j0 < X.F.J := Finset.mem_range.mp hj0
  have hzz := hz
  unfold Frames.LLset at hzz
  rw [Finset.mem_filter, Finset.mem_Ioo] at hzz
  obtain ⟨⟨hz1, hz2⟩, hzT⟩ := hzz
  have hzW : ¬ X.F.IsW (j0 : ℤ) z := not_le.mpr hz1
  have hzl : z ∈ X.F.letters (j0 : ℤ) := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(fr_zero_le_eFr hV _).trans hz1.le, hz2.le.trans (fr_zero_le_eFr hV _)⟩, hzT⟩
  set t := posOf n' z with ht
  set P : ℕ := p ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ)) with hP
  have hδ : ∀ j ∈ Finset.range X.F.J, DegAt t (if j = j0 then P * b j0 z else 0) (X.phc p K O (j : ℤ) (y j)) := by
    intro j hj m' hm'
    have hj' : j < X.F.J := Finset.mem_range.mp hj
    obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
      (fun v => p ^ (X.F.dist (j : ℤ) v.1 + X.Rj p K (j : ℤ))) (y j) hm'
    have hsup := XX'_supported O X.F (j : ℤ) _ _ _ (hy j).1.1
    have hT : ∀ v ∈ m.support, v.1 ∈ X.F.letters (j : ℤ) := by
      intro v hv
      have hvv : v ∈ (y j).vars := (mem_vars_iff_mem_support v).mpr ⟨m, hm, hv⟩
      exact ((mem_supported.mp hsup) (Finset.mem_coe.mpr hvv)).1
    have hPol : y j ∈ Pol O (r + K) (b j) := by rw [← segDeg_eq_Pol]; exact (hy j).1.2
    rw [multideg_imgMon (fun x : ℤ => posOf n' x) (fun x : ℤ => p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ))) m t,
      sum_eq_multideg (fun x => if posOf n' x = t then p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ)) else 0) m
        (X.F.letters (j : ℤ)) hT]
    by_cases hjj : j = j0
    · subst hjj
      rw [if_pos rfl, Finset.sum_eq_single z]
      · rw [if_pos rfl, mem_Pol_iff.mp hPol m hm z]
      · intro x hx hxz
        rw [if_neg, zero_mul]
        intro h
        exact hxz (LL_unique hV j hj0' z hz j hj' x hx h).2
      · intro h; exact absurd hzl h
    · rw [if_neg hjj]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [if_neg, zero_mul]
      intro h
      exact hjj (LL_unique hV j0 hj0' z hz j hj' x hx h).1
  have hU := degAt_mul (degAt_prod _ _ _ hδ) (degAt_monomial l (1 : O) t)
  rw [Finset.sum_ite_eq' (Finset.range X.F.J) j0, if_pos hj0] at hU
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg
  have ha' : X.a' p K t = P * b j0 z + multideg l t := (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hU m0 hm0')
  have hP0 : 0 < P := Nat.pow_pos hX.prime.pos
  have hl' : multideg l t ≤ (r + K) * (P - 1) := by
    unfold multideg
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin (r + K) => l (t, c)) (P - 1)
      (fun c _ => Nat.le_sub_one_of_lt (hl (j0 : ℤ) z hzl hzW c))
    simpa using this
  have hrK : 0 < r + K := Nat.add_pos_left (NeZero.pos r) K
  have hlt : X.a' p K t < (b j0 z + (r + K)) * P := by
    rw [ha']
    have : (r + K) * (P - 1) < (r + K) * P := Nat.mul_lt_mul_of_pos_left (by omega) hrK
    nlinarith
  have hltR : (X.a' p K t : ℝ) < ((b j0 z : ℝ) + Dat.k (r := r) K) * (P : ℝ) := by
    unfold Dat.k
    exact_mod_cast hlt
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hPe : ((p : ℝ) ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ))) = (P : ℝ) := by rw [hP]; push_cast; rfl
  rw [hPe, sub_lt_iff_lt_add, div_lt_iff₀ hPR]
  exact hltR

end Formalism.MainNotions.SelectionLemmas.Pf
