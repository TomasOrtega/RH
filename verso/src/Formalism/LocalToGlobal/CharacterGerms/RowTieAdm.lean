import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section Jet

variable {C : Type} [Field C] {σ : Type}

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Use `show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (x ^ k) / (k.factorial : C)) = 1`. Simplify using the standard rewrite rules.
-/
theorem cc_mvExp (x : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp x) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (x ^ k) / (k.factorial : C)) = 1
  simp

/- English proof (translation)
Unfold `jetAt0`. Rewrite using `[MvPolynomial.support_one, Finset.sum_singleton]`. Simplify using `[mfact]`.
-/
theorem jetAt0_one (G : MvPowerSeries σ C) : jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  unfold jetAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simp [mfact]

end Jet

section Par

/- English proof (translation)
Establish `h2 : 2 ∣ d` using `hd.two_dvd`. Establish `e : y = x + (y - x)` using `by ring`. Establish `e1 : y.val = (x.val + (y - x).val) % d` using `by conv_lhs => rw [e]`. Conclude with `ZMod.val_add _ _`. Establish `e2 : y.val % 2 = (x.val + (y - x).val) % 2` using `by rw [e1, Nat.mod_mod_of_dvd _ h2]`.

Rewrite `h` using `[Nat.even_iff, Nat.even_iff]`. Rewrite using `[Nat.odd_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem odd_sub_val {d : ℕ} [NeZero d] (hd : Even d) (x y : ZMod d) (h : ¬ (Even x.val ↔ Even y.val)) :
    Odd (y - x).val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : y = x + (y - x) := by ring
  have e1 : y.val = (x.val + (y - x).val) % d := by
    conv_lhs => rw [e]
    exact ZMod.val_add _ _
  have e2 : y.val % 2 = (x.val + (y - x).val) % 2 := by rw [e1, Nat.mod_mod_of_dvd _ h2]
  rw [Nat.even_iff, Nat.even_iff] at h
  rw [Nat.odd_iff]
  omega

end Par

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)

/- English proof (translation)
Take `⟨x, -, e⟩` from `Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h)`. Establish `e2 : (⟨g, F.en g a x.2⟩ : WV I) = w` using `congrArg Prod.snd e`. Substitute `e2` using the available equality. Conclude with `⟨rfl, F.en_ty g a x.2⟩`.
-/
theorem vars_letter {g : Fin 2} {a : ZMod d} {N : ℕ} {Q : MvPolynomial (Fin N × Fin (X.rkF g a)) C} {ρ : Fin N} {w : WV I}
    (h : (ρ, w) ∈ (MvPolynomial.rename (F.letter g a) Q).vars) : w.1 = g ∧ tyW X.G w = a := by
  obtain ⟨x, -, e⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h)
  have e2 : (⟨g, F.en g a x.2⟩ : WV I) = w := congrArg Prod.snd e
  subst e2
  exact ⟨rfl, F.en_ty g a x.2⟩

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Use `X.rk_small g a hb` as an intermediate fact. Unfold `RowData.rkF at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem big_of_le_rk (hj : X.j' < X.n) {g : Fin 2} {a : ZMod d} (h : X.n ≤ X.rkF g a) : X.big g a := by
  by_contra hb
  have := X.rk_small g a hb
  unfold RowData.rkF at h
  omega

/- English proof (translation)
Simplify using `using X.big_compl 0 a`.
-/
theorem big_one_iff (a : ZMod d) : X.big 1 a ↔ ¬ X.big 0 a := by
  simpa using X.big_compl 0 a

/- English proof (translation)
Establish `h3 : ¬ X.big g a'` using `(X.big_compl g a').1 h2`. Break down `hdich with hA | hB` into its components or cases. Use `⟨hA, odd_sub_val hA.1 a a' ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp`. Break down `hg with rfl | rfl` into its components or cases.

Rewrite using `[← hA.2 a, ← hA.2 a']`. The claim follows by propositional logic. Rewrite `h1`, `h3` using `[big_one_iff]`. Rewrite using `[← hA.2 a, ← hA.2 a']`. The claim follows by propositional logic.

It suffices to derive a contradiction. Apply the tactic sequence `have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp`. Break down `hg with rfl | rfl` into its components or cases. Conclude with `h3 (hB a')`. Rewrite `h1` using `[big_one_iff]`.

Conclude with `h1 (hB a)`.
-/
theorem alt_odd_of_big (hdich : X.Alt ∨ ∀ a, X.big 0 a) {g : Fin 2} {a a' : ZMod d} (h1 : X.big g a)
    (h2 : X.big (1 - g) a') : X.Alt ∧ Odd (a' - a).val := by
  have h3 : ¬ X.big g a' := (X.big_compl g a').1 h2
  rcases hdich with hA | hB
  · refine ⟨hA, odd_sub_val hA.1 a a' ?_⟩
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [← hA.2 a, ← hA.2 a']
      tauto
    · rw [big_one_iff] at h1 h3
      rw [← hA.2 a, ← hA.2 a']
      tauto
  · exfalso
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact h3 (hB a')
    · rw [big_one_iff] at h1
      exact h1 (hB a)

/- English proof (translation)
Consider the cases of `b with`. Consider the case `ch g a u`. Use `⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩` and prove the remaining obligations. Introduce `ρ g' a1 a2 hk`. Conclude with `absurd hk (by simp [GlobalTheory.kind])`.

Introduce `ρ _`. Use `⟨g, fun w hw => ?_⟩` and prove the remaining obligations. Conclude with `(vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1`. Consider the case `mon g e N`. Use `⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩` and prove the remaining obligations.

Introduce `ρ g' a1 a2 hk`. Conclude with `absurd hk (by simp [GlobalTheory.kind])`. Introduce `ρ _`. Use `⟨g, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨a, -, ha⟩` from `Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hw)`.

Conclude with `(vars_letter X F ha).1`. Consider the case `bi g a i y`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Establish `hp : (GlobalTheory.bi g a i 0).poly X F = 1`.

Simplify using `[GlobalTheory.poly]`. Both sides reduce to the same expression. Take `⟨S, t, ht, gr, hg, hc⟩` from `h`. Use `⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, S, t, ht, gr, hg, ?_⟩` and prove the remaining obligations. Introduce `ρ g' a1 a2 hk`.

Conclude with `absurd hk (by simp)`. Introduce `ρ _`. Use `⟨0, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[hp]`. Simplify using `at hw`.

Use `le_of_eq_of_le ?_ hc` and prove the remaining obligations. Use `congr 1`. Unfold `ValOf`. Rewrite using `[hp, jetAt0_one, jetAt0_one, map_prod, map_prod]`. Use `Finset.prod_congr rfl fun ρ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, cc_mvExp, cc_mvExp]`. Establish `hl : 0 < V.l ^ i * y` using `Nat.mul_pos (pow_pos V.l_prime.pos i) (Nat.pos_of_ne_zero hy)`. Establish `w1 : X.n ≤ X.rkF g a`. Apply `hwt g a X.n` to reduce the goal to its premises. Simplify using `only [GlobalTheory.wt, and_self, if_true]`.

Use linear arithmetic over natural numbers and integers. Establish `w2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d))`. Apply `hwt (1 - g) (a + (i : ZMod d)) X.n` to reduce the goal to its premises. Simplify using `only [GlobalTheory.wt, and_self, if_true]`. Use linear arithmetic over natural numbers and integers.

Establish `hao` using `alt_odd_of_big X hdich (big_of_le_rk X hj w1) (big_of_le_rk X hj w2)`. Use `⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩` and prove the remaining obligations. Introduce `ρ g' a1 a2 hk`. Establish `hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2)` using `by simpa [GlobalTheory.kind] using hk`. Take `⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2` from `by simpa using hk'`.

Use `⟨hao.1, hao.2, fun w hw => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1` into its components or cases. Conclude with `Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))`. Conclude with `Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))`. Introduce `ρ hk`.

Conclude with `absurd hk (by simp [GlobalTheory.kind])`.
-/
theorem attainsOK_of (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d) (c : ℝ)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) (h : b.Attains X F c) : b.AttainsOK X F c := by
  cases b with
  | ch g a u =>
    refine ⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      exact (vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1
  | mon g e N =>
    refine ⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hw)
      exact (vars_letter X F ha).1
  | bi g a i y =>
    by_cases hy : y = 0
    · subst hy
      have hp : (GlobalTheory.bi g a i 0).poly X F = 1 := by
        simp [GlobalTheory.poly]
        rfl
      obtain ⟨S, t, ht, gr, hg, hc⟩ := h
      refine ⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, S, t, ht, gr, hg, ?_⟩
      · intro ρ g' a1 a2 hk
        exact absurd hk (by simp)
      · intro ρ _
        refine ⟨0, fun w hw => ?_⟩
        rw [hp] at hw
        simp at hw
      · refine le_of_eq_of_le ?_ hc
        congr 1
        unfold ValOf
        rw [hp, jetAt0_one, jetAt0_one, map_prod, map_prod]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [map_mul, map_mul, cc_mvExp, cc_mvExp]
    · have hl : 0 < V.l ^ i * y := Nat.mul_pos (pow_pos V.l_prime.pos i) (Nat.pos_of_ne_zero hy)
      have w1 : X.n ≤ X.rkF g a := by
        apply hwt g a X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have w2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) := by
        apply hwt (1 - g) (a + (i : ZMod d)) X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have hao := alt_odd_of_big X hdich (big_of_le_rk X hj w1) (big_of_le_rk X hj w2)
      refine ⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
      · intro ρ g' a1 a2 hk
        have hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2) := by simpa [GlobalTheory.kind] using hk
        obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2 := by simpa using hk'
        refine ⟨hao.1, hao.2, fun w hw => ?_⟩
        rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1
        · exact Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
        · exact Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
      · intro ρ hk
        exact absurd hk (by simp [GlobalTheory.kind])

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact absurd hq (by simp)`. Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.sum_cons]`. Break down `List.mem_cons.1 hq with rfl | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Use `ih h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem le_sum_map {α : Type} (l : List α) (f : α → ℕ) {q : α} (hq : q ∈ l) : f q ≤ (l.map f).sum := by
  induction l with
  | nil => exact absurd hq (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hq with rfl | h
    · omega
    · have := ih h
      omega

variable {X F} in
/- English proof (translation)
Unfold `RowData.rkF`. Distinguish the cases in `hb : X.big g a`. Rewrite using `[X.rk_big g a hb, X.rk_big g' a' (h.1 hb)]`. Rewrite using `[X.rk_small g a hb, X.rk_small g' a' (fun h' => hb (h.2 h'))]`.
-/
theorem rkF_eq_of_big_iff {g g' : Fin 2} {a a' : ZMod d} (h : X.big g a ↔ X.big g' a') : X.rkF g a = X.rkF g' a' := by
  unfold RowData.rkF
  by_cases hb : X.big g a
  · rw [X.rk_big g a hb, X.rk_big g' a' (h.1 hb)]
  · rw [X.rk_small g a hb, X.rk_small g' a' (fun h' => hb (h.2 h'))]

end Formalism.L2.FormalSeriesBounds.RF

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section G

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

/- English proof (translation)
Introduce `L hwt o ho q hq hatt`. Use `attainsOK_of _ _ (hdich o ho) (hj o ho) q.1 q.2 (fun g a k hk => hga o ho g a k ?_) hatt` and prove the remaining obligations. Rewrite using `[← hwt o ho g a k]`. Use `le_sum_map (L o) (fun q => q.1.wt (X o) g a k) hq` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem blkAdm (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : BlockAdmissible X F Z ga := by
  intro L hwt o ho q hq hatt
  refine attainsOK_of _ _ (hdich o ho) (hj o ho) q.1 q.2 (fun g a k hk => hga o ho g a k ?_) hatt
  rw [← hwt o ho g a k]
  have := le_sum_map (L o) (fun q => q.1.wt (X o) g a k) hq
  omega

end G

section Cc

/- English proof (translation)
Use `revert a`. Evaluate the decidable proposition.
-/
theorem zmod_two_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by revert a; decide

/- English proof (translation)
Use `revert a`. Evaluate the decidable proposition.
-/
theorem zmod_two_even_succ_iff (a : ZMod 2) : Even (a + 1).val ↔ ¬ Even a.val := by revert a; decide

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)

/- English proof (translation)
Introduce `L hwt o q hq hatt`. Use `attainsOK_of _ _ (Or.inl (hA o)) (hj o) q.1 q.2 (fun g a k hk => ?_) hatt` and prove the remaining obligations. Apply the tactic sequence `have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp`. Break down `hg with rfl | rfl` into its components or cases. Apply `hga o a k` to reduce the goal to its premises.

Rewrite using `[← hwt o a k]`. Establish `h : q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k ≤ _` using `le_sum_map (L o) (fun q => q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k) hq`. Use linear arithmetic over natural numbers and integers. Establish `hk' : q.1.wt (X o) 1 (a + 1 + 1) k ≠ 0` using `by rwa [zmod_two_add_one_add_one]`. Establish `h1 : k ≤ (X o).rkF 0 (a + 1)`.

Apply `hga o (a + 1) k` to reduce the goal to its premises. Rewrite using `[← hwt o (a + 1) k]`. Establish `h : q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k ≤ _` using `le_sum_map (L o) (fun q => q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k) hq`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (X o).big 0 (a + 1) ↔ (X o).big 1 a`.

Rewrite using `[big_one_iff, (hA o).2 (a + 1), (hA o).2 a]`. Conclude with `zmod_two_even_succ_iff a`. Rewrite `h1` using `[rkF_eq_of_big_iff h2]`. Then use the resulting hypothesis.
-/
theorem blkAdmC (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) : BlockAdmissibleSelfConjugate X F gaC := by
  intro L hwt o q hq hatt
  refine attainsOK_of _ _ (Or.inl (hA o)) (hj o) q.1 q.2 (fun g a k hk => ?_) hatt
  have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  rcases hg with rfl | rfl
  · apply hga o a k
    rw [← hwt o a k]
    have h : q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k ≤ _ :=
      le_sum_map (L o) (fun q => q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k) hq
    omega
  · have hk' : q.1.wt (X o) 1 (a + 1 + 1) k ≠ 0 := by rwa [zmod_two_add_one_add_one]
    have h1 : k ≤ (X o).rkF 0 (a + 1) := by
      apply hga o (a + 1) k
      rw [← hwt o (a + 1) k]
      have h : q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k ≤ _ :=
        le_sum_map (L o) (fun q => q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k) hq
      omega
    have h2 : (X o).big 0 (a + 1) ↔ (X o).big 1 a := by
      rw [big_one_iff, (hA o).2 (a + 1), (hA o).2 a]
      exact zmod_two_even_succ_iff a
    rwa [rkF_eq_of_big_iff h2] at h1

end Cc

end Formalism.L2.FormalSeriesBounds.RF
