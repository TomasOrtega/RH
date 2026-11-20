import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Establish `hx : x = Fin.castAdd K ⟨x.val, h⟩` using `Fin.ext rfl`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma app_lt {r K : ℕ} (u : Fin r → ℤ) (v : Fin K → ℤ) (x : Fin (r + K)) (h : x.val < r) :
    Fin.append u v x = u ⟨x.val, h⟩ := by
  have hx : x = Fin.castAdd K ⟨x.val, h⟩ := Fin.ext rfl
  calc Fin.append u v x = Fin.append u v (Fin.castAdd K ⟨x.val, h⟩) := congrArg (Fin.append u v) hx
    _ = u ⟨x.val, h⟩ := Fin.append_left u v _

/- English proof (translation)
Establish `hlt` using `x.isLt`. Establish `hx : x = Fin.natAdd r ⟨x.val - r, by omega⟩` using `Fin.ext (show x.val = r + (x.val - r) by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma app_ge {r K : ℕ} (u : Fin r → ℤ) (v : Fin K → ℤ) (x : Fin (r + K)) (h : r ≤ x.val) :
    Fin.append u v x = v ⟨x.val - r, by omega⟩ := by
  have hlt := x.isLt
  have hx : x = Fin.natAdd r ⟨x.val - r, by omega⟩ := Fin.ext (show x.val = r + (x.val - r) by omega)
  calc Fin.append u v x = Fin.append u v (Fin.natAdd r ⟨x.val - r, by omega⟩) := congrArg (Fin.append u v) hx
    _ = v ⟨x.val - r, by omega⟩ := Fin.append_right u v _

/- English proof (translation)
Establish `hL : ∀ (u : Fin r → ℤ) (v : Fin K → ℤ) (a : Fin r), Fin.append u v (Fin.castAdd K a) = u a` using `fun u v a => Fin.append_left u v a`. Establish `hR : ∀ (u : Fin r → ℤ) (v : Fin K → ℤ) (a : Fin K), Fin.append u v (Fin.natAdd r a) = v a` using `fun u v a => Fin.append_right u v a`. Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `hK : 0 < K` using `Nat.pos_of_ne_zero (NeZero.ne K)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2, h3⟩`. Establish `a1 : ∀ a, n1 a ≤ n2 a` using `fun a => by`. Use `h1 (Fin.castAdd K a)` as an intermediate fact. Rewrite `this` using `[hL, hL]`. Then use the resulting hypothesis. Establish `b1 : ∀ a, k1 a ≤ k2 a` using `fun a => by`.

Use `h1 (Fin.natAdd r a)` as an intermediate fact. Rewrite `this` using `[hR, hR]`. Then use the resulting hypothesis. Establish `a2 : ∀ (a : Fin r) (h : a.1 + 1 < r), n2 ⟨a.1 + 1, h⟩ ≤ n1 a`. Introduce `a h`. Apply the tactic sequence `have hh : (Fin.castAdd K a).1 + 1 < r + K := by simp <;> omega`.

Establish `e1 : (⟨(Fin.castAdd K a).1 + 1, hh⟩ : Fin (r + K)) = Fin.castAdd K ⟨a.1 + 1, h⟩` using `Fin.ext rfl`. Use `h2 (Fin.castAdd K a) hh` as an intermediate fact. Rewrite `this` using `[e1, hL, hL]`. Then use the resulting hypothesis. Establish `b2 : ∀ (a : Fin K) (h : a.1 + 1 < K), k2 ⟨a.1 + 1, h⟩ ≤ k1 a`. Introduce `a h`.

Apply the tactic sequence `have hh : (Fin.natAdd r a).1 + 1 < r + K := by simp <;> omega`. Apply the tactic sequence `have e1 : (⟨(Fin.natAdd r a).1 + 1, hh⟩ : Fin (r + K)) = Fin.natAdd r ⟨a.1 + 1, h⟩ := Fin.ext (by simp <;> omega)`. Use `h2 (Fin.natAdd r a) hh` as an intermediate fact. Rewrite `this` using `[e1, hR, hR]`. Then use the resulting hypothesis. Establish `hj : k2 0 ≤ n1 (lastIdx r)`.

Apply the tactic sequence `have hh : (Fin.castAdd K (lastIdx r)).1 + 1 < r + K := by simp [lastIdx] <;> omega`. Apply the tactic sequence `have e1 : (⟨(Fin.castAdd K (lastIdx r)).1 + 1, hh⟩ : Fin (r + K)) = Fin.natAdd r 0 := Fin.ext (by simp [lastIdx] <;> omega)`. Use `h2 (Fin.castAdd K (lastIdx r)) hh` as an intermediate fact. Rewrite `this` using `[e1, hR, hL]`. Then use the resulting hypothesis. Simplify using `only [Fin.sum_univ_add, hL, hR] at h3`.

Establish `hs1 : 0 ≤ ∑ a, (n2 a - n1 a)` using `Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (a1 a))`. Establish `hs2 : 0 ≤ ∑ a, (k2 a - k1 a)` using `Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (b1 a))`. Establish `e1` using `Int.toNat_of_nonneg hs1`. Establish `e2` using `Int.toNat_of_nonneg hs2`. Use `⟨(∑ a, (n2 a - n1 a)).toNat, (∑ a, (k2 a - k1 a)).toNat, ?_, ⟨a1, a2, e1.symm⟩, ⟨b1, b2, e2.symm⟩, hj⟩` and prove the remaining obligations.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨b', b'', hb, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, hj⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Proceed by induction on `a using Fin.addCases with`.

Consider the case `left a => rw [hL, hL]`. Conclude with `a1 a`. Consider the case `right a => rw [hR, hR]`. Conclude with `b1 a`. Introduce `a`.

Proceed by induction on `a using Fin.addCases with`. Consider the case `left a`. Introduce `h`. Establish `hlt` using `a.isLt`. Distinguish the cases in `ha : a.1 + 1 < r`.

Establish `e1 : (⟨(Fin.castAdd K a).1 + 1, h⟩ : Fin (r + K)) = Fin.castAdd K ⟨a.1 + 1, ha⟩` using `Fin.ext rfl`. Rewrite using `[e1, hL, hL]`. Conclude with `a2 a ha`. Apply the tactic sequence `have e1 : (⟨(Fin.castAdd K a).1 + 1, h⟩ : Fin (r + K)) = Fin.natAdd r 0 := Fin.ext (by simp <;> omega)`. Apply the tactic sequence `have e2 : a = lastIdx r := Fin.ext (by simp [lastIdx] <;> omega)`.

Rewrite using `[e1, hR, hL, e2]`. Conclude with `hj`. Consider the case `right a`. Introduce `h`. Establish `ha : a.1 + 1 < K`.

Establish `h'` using `h`. Apply the tactic sequence `simp at h' <;> omega`. Apply the tactic sequence `have e1 : (⟨(Fin.natAdd r a).1 + 1, h⟩ : Fin (r + K)) = Fin.natAdd r ⟨a.1 + 1, ha⟩ := Fin.ext (by simp <;> omega)`. Rewrite using `[e1, hR, hR]`. Conclude with `b2 a ha`.

Simplify using `only [Fin.sum_univ_add, hL, hR]`. Rewrite using `[a3, b3]`. Use linear arithmetic over natural numbers and integers.
-/
lemma hstrip_append {r K : ℕ} [NeZero r] [NeZero K] (n1 n2 : Fin r → ℤ) (k1 k2 : Fin K → ℤ) (B : ℕ) :
    HStrip (Fin.append n1 k1) (Fin.append n2 k2) B ↔
      ∃ b' b'' : ℕ, b' + b'' = B ∧ HStrip n1 n2 b' ∧ HStrip k1 k2 b'' ∧ k2 0 ≤ n1 (lastIdx r) := by
  have hL : ∀ (u : Fin r → ℤ) (v : Fin K → ℤ) (a : Fin r), Fin.append u v (Fin.castAdd K a) = u a :=
    fun u v a => Fin.append_left u v a
  have hR : ∀ (u : Fin r → ℤ) (v : Fin K → ℤ) (a : Fin K), Fin.append u v (Fin.natAdd r a) = v a :=
    fun u v a => Fin.append_right u v a
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  constructor
  · rintro ⟨h1, h2, h3⟩
    have a1 : ∀ a, n1 a ≤ n2 a := fun a => by
      have := h1 (Fin.castAdd K a)
      rwa [hL, hL] at this
    have b1 : ∀ a, k1 a ≤ k2 a := fun a => by
      have := h1 (Fin.natAdd r a)
      rwa [hR, hR] at this
    have a2 : ∀ (a : Fin r) (h : a.1 + 1 < r), n2 ⟨a.1 + 1, h⟩ ≤ n1 a := by
      intro a h
      have hh : (Fin.castAdd K a).1 + 1 < r + K := by simp <;> omega
      have e1 : (⟨(Fin.castAdd K a).1 + 1, hh⟩ : Fin (r + K)) = Fin.castAdd K ⟨a.1 + 1, h⟩ := Fin.ext rfl
      have := h2 (Fin.castAdd K a) hh
      rwa [e1, hL, hL] at this
    have b2 : ∀ (a : Fin K) (h : a.1 + 1 < K), k2 ⟨a.1 + 1, h⟩ ≤ k1 a := by
      intro a h
      have hh : (Fin.natAdd r a).1 + 1 < r + K := by simp <;> omega
      have e1 : (⟨(Fin.natAdd r a).1 + 1, hh⟩ : Fin (r + K)) = Fin.natAdd r ⟨a.1 + 1, h⟩ :=
        Fin.ext (by simp <;> omega)
      have := h2 (Fin.natAdd r a) hh
      rwa [e1, hR, hR] at this
    have hj : k2 0 ≤ n1 (lastIdx r) := by
      have hh : (Fin.castAdd K (lastIdx r)).1 + 1 < r + K := by simp [lastIdx] <;> omega
      have e1 : (⟨(Fin.castAdd K (lastIdx r)).1 + 1, hh⟩ : Fin (r + K)) = Fin.natAdd r 0 :=
        Fin.ext (by simp [lastIdx] <;> omega)
      have := h2 (Fin.castAdd K (lastIdx r)) hh
      rwa [e1, hR, hL] at this
    simp only [Fin.sum_univ_add, hL, hR] at h3
    have hs1 : 0 ≤ ∑ a, (n2 a - n1 a) := Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (a1 a))
    have hs2 : 0 ≤ ∑ a, (k2 a - k1 a) := Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (b1 a))
    have e1 := Int.toNat_of_nonneg hs1
    have e2 := Int.toNat_of_nonneg hs2
    refine ⟨(∑ a, (n2 a - n1 a)).toNat, (∑ a, (k2 a - k1 a)).toNat, ?_, ⟨a1, a2, e1.symm⟩, ⟨b1, b2, e2.symm⟩, hj⟩
    omega
  · rintro ⟨b', b'', hb, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, hj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      induction a using Fin.addCases with
      | left a => rw [hL, hL]; exact a1 a
      | right a => rw [hR, hR]; exact b1 a
    · intro a
      induction a using Fin.addCases with
      | left a =>
        intro h
        have hlt := a.isLt
        by_cases ha : a.1 + 1 < r
        · have e1 : (⟨(Fin.castAdd K a).1 + 1, h⟩ : Fin (r + K)) = Fin.castAdd K ⟨a.1 + 1, ha⟩ := Fin.ext rfl
          rw [e1, hL, hL]
          exact a2 a ha
        · have e1 : (⟨(Fin.castAdd K a).1 + 1, h⟩ : Fin (r + K)) = Fin.natAdd r 0 :=
            Fin.ext (by simp <;> omega)
          have e2 : a = lastIdx r := Fin.ext (by simp [lastIdx] <;> omega)
          rw [e1, hR, hL, e2]
          exact hj
      | right a =>
        intro h
        have ha : a.1 + 1 < K := by
          have h' := h
          simp at h' <;> omega
        have e1 : (⟨(Fin.natAdd r a).1 + 1, h⟩ : Fin (r + K)) = Fin.natAdd r ⟨a.1 + 1, ha⟩ :=
          Fin.ext (by simp <;> omega)
        rw [e1, hR, hR]
        exact b2 a ha
    · simp only [Fin.sum_univ_add, hL, hR]
      rw [a3, b3]
      omega

/- English proof (translation)
Introduce `a b hab`. Establish `hab' : a.val ≤ b.val` using `hab`. Distinguish the cases in `ha : a.val < r`. Rewrite using `[app_lt n1 k1 a ha]`. Distinguish the cases in `hb : b.val < r`.

Rewrite using `[app_lt n1 k1 b hb]`. Conclude with `h1 (show (⟨a.val, ha⟩ : Fin r) ≤ ⟨b.val, hb⟩ from hab')`. Establish `hb' : r ≤ b.val` using `by omega`. Rewrite using `[app_ge n1 k1 b hb']`. Establish `hlt` using `b.isLt`.

Combine the equalities or inequalities in the displayed calculation. Establish `ha' : r ≤ a.val` using `by omega`. Establish `hb : r ≤ b.val` using `le_trans ha' hab'`. Rewrite using `[app_ge n1 k1 a ha', app_ge n1 k1 b hb]`. Conclude with `h2 (show a.val - r ≤ b.val - r by omega)`.
-/
lemma antitone_append {r K : ℕ} [NeZero r] [NeZero K] (n1 : Fin r → ℤ) (k1 : Fin K → ℤ) (h1 : Antitone n1)
    (h2 : Antitone k1) (hm : k1 0 ≤ n1 (lastIdx r)) : Antitone (Fin.append n1 k1) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  by_cases ha : a.val < r
  · rw [app_lt n1 k1 a ha]
    by_cases hb : b.val < r
    · rw [app_lt n1 k1 b hb]
      exact h1 (show (⟨a.val, ha⟩ : Fin r) ≤ ⟨b.val, hb⟩ from hab')
    · have hb' : r ≤ b.val := by omega
      rw [app_ge n1 k1 b hb']
      have hlt := b.isLt
      calc _ ≤ k1 0 := h2 (by rw [Fin.le_def]; simp)
        _ ≤ n1 (lastIdx r) := hm
        _ ≤ n1 ⟨a.val, ha⟩ := h1 (show (⟨a.val, ha⟩ : Fin r) ≤ lastIdx r from show a.val ≤ r - 1 by omega)
  · have ha' : r ≤ a.val := by omega
    have hb : r ≤ b.val := le_trans ha' hab'
    rw [app_ge n1 k1 a ha', app_ge n1 k1 b hb]
    exact h2 (show a.val - r ≤ b.val - r by omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Use `h (show Fin.castAdd K a ≤ Fin.castAdd K b from hab)` as an intermediate fact. Rewrite `this` using `[Fin.append_left, Fin.append_left]`. Then use the resulting hypothesis. Introduce `a b hab`.

Establish `hab' : r + a.val ≤ r + b.val`. Establish `: a.val ≤ b.val` using `hab`. Use linear arithmetic over natural numbers and integers. Use `h (show Fin.natAdd r a ≤ Fin.natAdd r b from hab')` as an intermediate fact. Rewrite `this` using `[Fin.append_right, Fin.append_right]`. Then use the resulting hypothesis.
-/
lemma antitone_of_append {r K : ℕ} (n1 : Fin r → ℤ) (k1 : Fin K → ℤ) (h : Antitone (Fin.append n1 k1)) :
    Antitone n1 ∧ Antitone k1 := by
  constructor
  · intro a b hab
    have := h (show Fin.castAdd K a ≤ Fin.castAdd K b from hab)
    rwa [Fin.append_left, Fin.append_left] at this
  · intro a b hab
    have hab' : r + a.val ≤ r + b.val := by
      have : a.val ≤ b.val := hab
      omega
    have := h (show Fin.natAdd r a ≤ Fin.natAdd r b from hab')
    rwa [Fin.append_right, Fin.append_right] at this

/- English proof (translation)
Introduce `N r K _ _ LL B _ nu ka`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hP⟩`. Establish `hstep : ∀ i : Fin N, ∃ b' b'' : ℕ, b' + b'' = B i ∧ (if LL.vec i then HStrip (nu i.castSucc) (nu i.succ) b' else HStrip (nu i.succ) (nu i.castSucc) b') ∧ (if LL.vec i then HStrip (ka i.castSucc) (ka i.succ) b'' else HStrip (ka i.succ) (ka i.castSucc) b'') ∧ CondC LL nu ka i`. Introduce `i`.

Use `P.step i` as an intermediate fact. Rewrite `this` using `[hP]`. Unfold `CondC`. Distinguish the cases in `hv : LL.vec i`. Simplify using `only [hv, if_true] at this ⊢`.

Conclude with `(hstrip_append _ _ _ _ _).1 this`. Simplify using `only [hv, if_false, Bool.false_eq_true] at this ⊢`. Conclude with `(hstrip_append _ _ _ _ _).1 this`. Use `choose b' b'' h1 h2 h3 h4 using hstep`. Establish `hdom : ∀ i, Antitone (nu i) ∧ Antitone (ka i)` using `fun i => by`.

Use `P.dom i` as an intermediate fact. Rewrite `this` using `[hP]`. Conclude with `antitone_of_append _ _ this`. Establish `hz` using `P.zero`. Rewrite `hz` using `[hP]`.

Use `⟨b', b'', h1, ⟨⟨nu, ?_, fun i => (hdom i).1, h2⟩, rfl⟩, ⟨⟨ka, ?_, fun i => (hdom i).2, h3⟩, rfl⟩, h4⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Use `congrFun hz (Fin.castAdd K a)` as an intermediate fact. Simplify `this` using `[joinPT]`. Use function extensionality and compare the values at `a`.

Use `congrFun hz (Fin.natAdd r a)` as an intermediate fact. Simplify `this` using `[joinPT]`. Introduce and unpack `⟨b', b'', hb, ⟨P1, rfl⟩, ⟨P2, rfl⟩, hC⟩`. Establish `hmid : ∀ i : Fin (N + 1), P2.mu i 0 ≤ P1.mu i (lastIdx r)`. Introduce `i`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[P1.zero, P2.zero]`. Simplify using the standard rewrite rules. Establish `c` using `hC j`. Establish `s1` using `P1.step j`.

Establish `s2` using `P2.step j`. Unfold `CondC at c`. Distinguish the cases in `hv : LL.vec j`. Simplify using `only [hv, if_true] at c s1 s2`. Conclude with `c.trans (s1.1 _)`.

Simplify using `only [hv, if_false, Bool.false_eq_true] at c s1 s2`. Conclude with `(s2.1 _).trans c`. Use `⟨⟨joinPT P1.mu P2.mu, ?_, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [joinPT, P1.zero, P2.zero]`.

Distinguish the cases in `hx : x.val < r`. Rewrite using `[app_lt _ _ _ hx]`. Both sides reduce to the same expression. Rewrite using `[app_ge _ _ _ (by omega)]; rfl`. Introduce `i`.

Conclude with `antitone_append _ _ (P1.dom i) (P2.dom i) (hmid i)`. Introduce `i`. Establish `c` using `hC i`. Establish `s1` using `P1.step i`. Establish `s2` using `P2.step i`.

Unfold `CondC at c`. Distinguish the cases in `hv : LL.vec i`. Simplify using `only [hv, if_true] at c s1 s2 ⊢`. Conclude with `(hstrip_append _ _ _ _ _).2 ⟨_, _, hb i, s1, s2, c⟩`. Simplify using `only [hv, if_false, Bool.false_eq_true] at c s1 s2 ⊢`.

Conclude with `(hstrip_append _ _ _ _ _).2 ⟨_, _, hb i, s1, s2, c⟩`.
-/
theorem prvB1_of_D7 (D : Formalism.BasicNotions.D7) : RotatedSumBound D := by
  intro N r K _ _ LL B _ nu ka
  constructor
  · rintro ⟨P, hP⟩
    have hstep : ∀ i : Fin N, ∃ b' b'' : ℕ, b' + b'' = B i ∧
        (if LL.vec i then HStrip (nu i.castSucc) (nu i.succ) b' else HStrip (nu i.succ) (nu i.castSucc) b') ∧
        (if LL.vec i then HStrip (ka i.castSucc) (ka i.succ) b'' else HStrip (ka i.succ) (ka i.castSucc) b'') ∧
        CondC LL nu ka i := by
      intro i
      have := P.step i
      rw [hP] at this
      unfold CondC
      by_cases hv : LL.vec i
      · simp only [hv, if_true] at this ⊢
        exact (hstrip_append _ _ _ _ _).1 this
      · simp only [hv, if_false, Bool.false_eq_true] at this ⊢
        exact (hstrip_append _ _ _ _ _).1 this
    choose b' b'' h1 h2 h3 h4 using hstep
    have hdom : ∀ i, Antitone (nu i) ∧ Antitone (ka i) := fun i => by
      have := P.dom i
      rw [hP] at this
      exact antitone_of_append _ _ this
    have hz := P.zero
    rw [hP] at hz
    refine ⟨b', b'', h1, ⟨⟨nu, ?_, fun i => (hdom i).1, h2⟩, rfl⟩, ⟨⟨ka, ?_, fun i => (hdom i).2, h3⟩, rfl⟩, h4⟩
    · funext a
      have := congrFun hz (Fin.castAdd K a)
      simpa [joinPT] using this
    · funext a
      have := congrFun hz (Fin.natAdd r a)
      simpa [joinPT] using this
  · rintro ⟨b', b'', hb, ⟨P1, rfl⟩, ⟨P2, rfl⟩, hC⟩
    have hmid : ∀ i : Fin (N + 1), P2.mu i 0 ≤ P1.mu i (lastIdx r) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [P1.zero, P2.zero]; simp
      · have c := hC j
        have s1 := P1.step j
        have s2 := P2.step j
        unfold CondC at c
        by_cases hv : LL.vec j
        · simp only [hv, if_true] at c s1 s2
          exact c.trans (s1.1 _)
        · simp only [hv, if_false, Bool.false_eq_true] at c s1 s2
          exact (s2.1 _).trans c
    refine ⟨⟨joinPT P1.mu P2.mu, ?_, ?_, ?_⟩, rfl⟩
    · funext x
      simp only [joinPT, P1.zero, P2.zero]
      by_cases hx : x.val < r
      · rw [app_lt _ _ _ hx]; rfl
      · rw [app_ge _ _ _ (by omega)]; rfl
    · intro i
      exact antitone_append _ _ (P1.dom i) (P2.dom i) (hmid i)
    · intro i
      have c := hC i
      have s1 := P1.step i
      have s2 := P2.step i
      unfold CondC at c
      by_cases hv : LL.vec i
      · simp only [hv, if_true] at c s1 s2 ⊢
        exact (hstrip_append _ _ _ _ _).2 ⟨_, _, hb i, s1, s2, c⟩
      · simp only [hv, if_false, Bool.false_eq_true] at c s1 s2 ⊢
        exact (hstrip_append _ _ _ _ _).2 ⟨_, _, hb i, s1, s2, c⟩

end Formalism.MainNotions.LemmaBAlt
