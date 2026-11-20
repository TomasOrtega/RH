import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem wt_root : ∀ i j : Fin 4, i ≠ j → wt i j ∈ roots := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem low_case : ∀ i j : Fin 4, i ≠ j → wt i j ∉ qQ → i < j ∨ (i = 2 ∧ j = 1) := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem be_case : ∀ i j : Fin 4, wt i j = wBe → i = 1 ∧ j = 2 := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem vV_case : ∀ i j : Fin 4, wt i j ∉ vV → wt i j ∉ nP ∨ wt i j = -wPs := by decide

/- English proof (translation)
Simplify using `[nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]`.
-/
private theorem nCo_be {R : Type} [CommRing R] (X : M4 R) : nCo X wBe = 0 := by
  simp [nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]

/- English proof (translation)
Simplify using `[nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]`.
-/
private theorem nCo_nbe {R : Type} [CommRing R] (X : M4 R) : nCo X (-wBe) = X 2 1 := by
  simp [nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]

/- English proof (translation)
Simplify using `[nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]`.
-/
private theorem nCo_nps {R : Type} [CommRing R] (X : M4 R) : nCo X (-wPs) = X 2 0 := by
  simp [nCo, wBe, UpperTheory.V.GradeZeroInterpolatingElement.wAl, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.wTh]

/- English proof (translation)
Take `⟨hg, hd, hu⟩` from `hN`. Unfold `IsGSp at hg`. Establish `e1` using `congrFun (congrFun hg 2) 0`. Establish `e2` using `hup 2 0 (by decide)`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj, sgn] at e1 e2`.

Rewrite `e2` using `[hu 0 1 (by decide), hd 0, hd 1, hN21, hX0 1 (by decide), hX0 2 (by decide), hX0 3 (by decide), hX2 0 (by decide), hX2 1 (by decide), hX2 3 (by decide)]`. Rewrite `e1` using `[hu 0 1 (by decide), hd 0, hd 1, hN21]`. Establish `h : (X 2 2 - X 0 0) * N 2 0 = 0` using `by linear_combination e2 - X 0 0 * e1`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Take the linear combination `-h`.

Conclude with `absurd h hc`.
-/
private theorem entry_zero_zero_eq_two_two_of_isUp_conj {k : Type} [Field k] (N X : M4 k) (hN : IsLow N) (hN21 : N 2 1 = 0)
    (hX0 : ∀ j, j ≠ 0 → X 0 j = 0) (hX2 : ∀ j, j ≠ 2 → X 2 j = 0)
    (hup : IsUp (adj N * X * N)) (hc : N 2 0 ≠ 0) : X 0 0 = X 2 2 := by
  obtain ⟨hg, hd, hu⟩ := hN
  unfold IsGSp at hg
  have e1 := congrFun (congrFun hg 2) 0
  have e2 := hup 2 0 (by decide)
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj, sgn] at e1 e2
  rw [hu 0 1 (by decide), hd 0, hd 1, hN21, hX0 1 (by decide), hX0 2 (by decide), hX0 3 (by decide),
    hX2 0 (by decide), hX2 1 (by decide), hX2 3 (by decide)] at e2
  rw [hu 0 1 (by decide), hd 0, hd 1, hN21] at e1
  have h : (X 2 2 - X 0 0) * N 2 0 = 0 := by linear_combination e2 - X 0 0 * e1
  rcases mul_eq_zero.mp h with h | h
  · linear_combination -h
  · exact absurd h hc

/- English proof (translation)
Introduce `O Γ _ _ _ Φ k _ a P hP hE hbe hps hsub`. Establish `hS : Supp nP P.r`. Introduce `g i j hij hw`. Assume the negation of the conclusion as `h`. Conclude with `hw (hsub ⟨wt_root i j hij, Or.inl ⟨g, i, j, rfl, h⟩⟩)`.

Establish `hN : ∀ v, SuppM qQ (P.n v)`. Introduce `v i j hij hw`. Break down `low_case i j hij hw with h | ⟨rfl, rfl⟩` into its components or cases. Conclude with `(hP.pair.low v).2.2 i j h`. Assume the negation of the conclusion as `h`.

Establish `hT : -wBe ∈ Tight P` using `⟨by decide, Or.inr ⟨v, by rw [nCo_nbe]; exact h⟩⟩`. Conclude with `absurd (hsub hT) (by decide)`. Establish `hEbe : Ent P.r wBe`. Break down `hbe.2 with h | ⟨v, hv⟩` into its components or cases. Conclude with `h`.

Conclude with `absurd (nCo_be _) hv`. Use `⟨hS, hN, hEbe, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp : Ent P.r (-wPs)`. Conclude with `Or.inl hp`. Use `right`.

Take `⟨v, hv⟩` from `hps.2.resolve_left hp`. Rewrite `hv` using `[nCo_nps]`. Establish `h0 : ∀ g i j, wt i j = -wPs → P.r g i j = 0` using `fun g i j hw => by`. Assume the negation of the conclusion as `h`. Conclude with `hp ⟨g, i, j, hw, h⟩`.

Use `⟨?_, ⟨v, hv, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `g i j hij hw`. Break down `vV_case i j hw with h | h` into its components or cases. Conclude with `hS g i j hij h`. Conclude with `h0 g i j h`.

Introduce `s hs`. Establish `key` using `entry_zero_zero_eq_two_two_of_isUp_conj (P.n v) (P.r s) (hP.pair.low v) (hN v 2 1 (by decide) (by decide)) ?_ ?_ (hP.pair.flag v s hs) hv`. Rewrite `key` using `[hP.diag s 0, hP.diag s 2]`. Conclude with `key`. Introduce `j hj`.

Apply `hS s 0 j (Ne.symm hj)` to reduce the goal to its premises. Use `revert hj`. Use `revert j`. Evaluate the decidable proposition. Introduce `j hj`.

Distinguish the cases in `hw : wt 2 j = -wPs`. Conclude with `h0 s 2 j hw`. Apply `hS s 2 j (Ne.symm hj) revert hw hj revert j` to reduce the goal to its premises. Evaluate the decidable proposition. Introduce and unpack `⟨m, hm⟩`.

Establish `hz` using `(hE 1 2 (by decide) ?_ m hm).1`. Take `⟨g, i, j, hw, hne⟩` from `hEbe`. Take `⟨rfl, rfl⟩` from `be_case i j hw`. Conclude with `hne (hz g)`. Introduce `g h x hx1 hx2`.

Establish `a1 : P.r h 0 2 = 0` using `hS h 0 2 (by decide) (by decide)`. Establish `a2 : P.r g 1 3 = 0` using `hS g 1 3 (by decide) (by decide)`. Use `fin_cases x`. Simplify using `[a1]`. Conclude with `absurd rfl hx1`.

Conclude with `absurd rfl hx2`. Simplify using `[a2]`.
-/
theorem UpperTheory.V.Ws.Lat.shape :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (P : PD Φ.ι Γ k), PreRes Φ a P → EntVan Φ a P →
      wBe ∈ Tight P → -wPs ∈ Tight P → Tight P ⊆ nP →
      Supp nP P.r ∧ (∀ v, SuppM qQ (P.n v)) ∧ Ent P.r wBe ∧
        (Ent P.r (-wPs) ∨ (Supp vV P.r ∧ (∃ v, P.n v 2 0 ≠ 0 ∧ ∀ s ∈ Φ.Gv v, a (Φ.χ 0 s) = a (Φ.χ 2 s)) ∧
          ¬ ∃ m : Φ.ι → k, ∀ v, ∀ s ∈ Φ.Gv v, P.r s 1 2 = m v * (a (Φ.χ 2 s) - a (Φ.χ 1 s)))) := by
  intro O Γ _ _ _ Φ k _ a P hP hE hbe hps hsub
  have hS : Supp nP P.r := by
    intro g i j hij hw
    by_contra h
    exact hw (hsub ⟨wt_root i j hij, Or.inl ⟨g, i, j, rfl, h⟩⟩)
  have hN : ∀ v, SuppM qQ (P.n v) := by
    intro v i j hij hw
    rcases low_case i j hij hw with h | ⟨rfl, rfl⟩
    · exact (hP.pair.low v).2.2 i j h
    · by_contra h
      have hT : -wBe ∈ Tight P := ⟨by decide, Or.inr ⟨v, by rw [nCo_nbe]; exact h⟩⟩
      exact absurd (hsub hT) (by decide)
  have hEbe : Ent P.r wBe := by
    rcases hbe.2 with h | ⟨v, hv⟩
    · exact h
    · exact absurd (nCo_be _) hv
  refine ⟨hS, hN, hEbe, ?_⟩
  by_cases hp : Ent P.r (-wPs)
  · exact Or.inl hp
  right
  obtain ⟨v, hv⟩ := hps.2.resolve_left hp
  rw [nCo_nps] at hv
  have h0 : ∀ g i j, wt i j = -wPs → P.r g i j = 0 := fun g i j hw => by
    by_contra h
    exact hp ⟨g, i, j, hw, h⟩
  refine ⟨?_, ⟨v, hv, ?_⟩, ?_⟩
  · intro g i j hij hw
    rcases vV_case i j hw with h | h
    · exact hS g i j hij h
    · exact h0 g i j h
  · intro s hs
    have key := entry_zero_zero_eq_two_two_of_isUp_conj (P.n v) (P.r s) (hP.pair.low v) (hN v 2 1 (by decide) (by decide)) ?_ ?_
      (hP.pair.flag v s hs) hv
    · rw [hP.diag s 0, hP.diag s 2] at key
      exact key
    · intro j hj
      apply hS s 0 j (Ne.symm hj)
      revert hj
      revert j
      decide
    · intro j hj
      by_cases hw : wt 2 j = -wPs
      · exact h0 s 2 j hw
      · apply hS s 2 j (Ne.symm hj)
        revert hw hj
        revert j
        decide
  · rintro ⟨m, hm⟩
    have hz := (hE 1 2 (by decide) ?_ m hm).1
    · obtain ⟨g, i, j, hw, hne⟩ := hEbe
      obtain ⟨rfl, rfl⟩ := be_case i j hw
      exact hne (hz g)
    · intro g h x hx1 hx2
      have a1 : P.r h 0 2 = 0 := hS h 0 2 (by decide) (by decide)
      have a2 : P.r g 1 3 = 0 := hS g 1 3 (by decide) (by decide)
      fin_cases x
      · simp [a1]
      · exact absurd rfl hx1
      · exact absurd rfl hx2
      · simp [a2]
