import Mathlib

/- English proof (translation)
Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `⟨1 - e, by linear_combination (-1 : R) * hxe⟩`. Introduce `h`. Establish `h1 : (1 - x) ∈ Ideal.span ({1 - e} : Set R)`.

Rewrite using `[h]`. Conclude with `Ideal.mem_span_singleton_self _`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 h1`. Apply `hne` to reduce the goal to its premises. Take the linear combination `e * hc + c * he - hxe`.
-/
private theorem idem_lt {R : Type} [CommRing R] {e x : R} (he : e * e = e)
    (hxe : x * e = x) (hne : x ≠ e) :
    Ideal.span ({1 - e} : Set R) < Ideal.span ({1 - x} : Set R) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨1 - e, by linear_combination (-1 : R) * hxe⟩
  · intro h
    have h1 : (1 - x) ∈ Ideal.span ({1 - e} : Set R) := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    apply hne
    linear_combination e * hc + c * he - hxe

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.sum_eq_single i]`. Conclude with `h1 i`. Introduce `j _ hj`. Conclude with `h2 i j (Ne.symm hj)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
private theorem idem_absorb {R : Type} [CommRing R] {s : ℕ} (g : Fin s → R)
    (h1 : ∀ i, g i * g i = g i) (h2 : ∀ i j, i ≠ j → g i * g j = 0) (i : Fin s) :
    g i * ∑ j, g j = g i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact h1 i
  · intro j _ hj
    exact h2 i j (Ne.symm hj)
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `R _ _`. It suffices to establish `H : ∀ I : Ideal R, ∀ e : R, Ideal.span ({1 - e} : Set R) = I → e * e = e → ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧ (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e from fun e he => H _ e rfl he`. Introduce `I`. Proceed by induction on `I using WellFoundedGT.induction with`. Consider the case `ind I ih`.

Introduce `e hI he`. Substitute `hI` using the available equality. Distinguish the cases in `h0 : e = 0`. Conclude with `⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp [h0]⟩`. Distinguish the cases in `hp : ∀ x : R, x * x = x → x * e = x → x = 0 ∨ x = e`.

Use `⟨1, fun _ => e, fun _ => ⟨he, h0, hp⟩, ?_, by simp⟩` and prove the remaining obligations. Introduce `i j hij`. Conclude with `absurd (Subsingleton.elim i j) hij`. Use `push Not at hp`. Take `⟨x, hx, hxe, hx0, hxne⟩` from `hp`.

Establish `hy : (e - x) * (e - x) = e - x` using `by linear_combination he + hx - 2 * hxe`. Establish `hye : (e - x) * e = e - x` using `by linear_combination he - hxe`. Establish `hyne : e - x ≠ e` using `fun h => hx0 (by linear_combination -h)`. Establish `hxy : x * (e - x) = 0` using `by linear_combination hxe - hx`. Take `⟨s, g, hg1, hg2, hg3⟩` from `ih _ (idem_lt he hxe hxne) x rfl hx`.

Take `⟨t, k, hk1, hk2, hk3⟩` from `ih _ (idem_lt he hye hyne) (e - x) rfl hy`. Establish `hcross : ∀ i j, g i * k j = 0`. Introduce `i j`. Establish `a` using `idem_absorb g (fun i => (hg1 i).1) hg2 i`. Establish `b` using `idem_absorb k (fun i => (hk1 i).1) hk2 j`.

Rewrite `a` using `[hg3]`. Rewrite `b` using `[hk3]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨s + t, Fin.append g k, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => simpa only [Fin.append_left] using hg1 i`. Consider the case `right i => simpa only [Fin.append_right] using hk1 i`. Introduce `i j hij`. Proceed by induction on `i using Fin.addCases with`.

Consider the case `left i`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`. Simplify using `only [Fin.append_left]`. Conclude with `hg2 i j (fun h => hij (by rw [h]))`.

Consider the case `right j`. Simplify using `only [Fin.append_left, Fin.append_right]`. Conclude with `hcross i j`. Consider the case `right i`. Proceed by induction on `j using Fin.addCases with`.

Consider the case `left j`. Simplify using `only [Fin.append_left, Fin.append_right]`. Rewrite using `[mul_comm]`. Conclude with `hcross j i`. Consider the case `right j`.

Simplify using `only [Fin.append_right]`. Conclude with `hk2 i j (fun h => hij (by rw [h]))`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right]`. Rewrite using `[hg3, hk3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (e : R), e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e := by
  intro R _ _
  suffices H : ∀ I : Ideal R, ∀ e : R, Ideal.span ({1 - e} : Set R) = I → e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e from fun e he => H _ e rfl he
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
  intro e hI he
  subst hI
  by_cases h0 : e = 0
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp [h0]⟩
  by_cases hp : ∀ x : R, x * x = x → x * e = x → x = 0 ∨ x = e
  · refine ⟨1, fun _ => e, fun _ => ⟨he, h0, hp⟩, ?_, by simp⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  push Not at hp
  obtain ⟨x, hx, hxe, hx0, hxne⟩ := hp
  have hy : (e - x) * (e - x) = e - x := by linear_combination he + hx - 2 * hxe
  have hye : (e - x) * e = e - x := by linear_combination he - hxe
  have hyne : e - x ≠ e := fun h => hx0 (by linear_combination -h)
  have hxy : x * (e - x) = 0 := by linear_combination hxe - hx
  obtain ⟨s, g, hg1, hg2, hg3⟩ := ih _ (idem_lt he hxe hxne) x rfl hx
  obtain ⟨t, k, hk1, hk2, hk3⟩ := ih _ (idem_lt he hye hyne) (e - x) rfl hy
  have hcross : ∀ i j, g i * k j = 0 := by
    intro i j
    have a := idem_absorb g (fun i => (hg1 i).1) hg2 i
    have b := idem_absorb k (fun i => (hk1 i).1) hk2 j
    rw [hg3] at a
    rw [hk3] at b
    calc g i * k j = (g i * x) * (k j * (e - x)) := by rw [a, b]
      _ = g i * k j * (x * (e - x)) := by ring
      _ = 0 := by rw [hxy, mul_zero]
  refine ⟨s + t, Fin.append g k, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using hg1 i
    | right i => simpa only [Fin.append_right] using hk1 i
  · intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        exact hg2 i j (fun h => hij (by rw [h]))
      | right j =>
        simp only [Fin.append_left, Fin.append_right]
        exact hcross i j
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left, Fin.append_right]
        rw [mul_comm]; exact hcross j i
      | right j =>
        simp only [Fin.append_right]
        exact hk2 i j (fun h => hij (by rw [h]))
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hg3, hk3]; ring
