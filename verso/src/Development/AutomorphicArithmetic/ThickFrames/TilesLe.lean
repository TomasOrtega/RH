import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import Development.AutomorphicArithmetic.ThickFrames.expectationSpec
import Development.AutomorphicArithmetic.ThickFrames.MarkedGe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTops

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open GlobalTheory.RandomTops (tile tile_disjoint marked_congr)

/- English proof (translation)
Simplify using `[ind, h]`.
-/
private theorem ind_neg' {q : Prop} (h : ¬ q) : ind q = 0 := by simp [ind, h]

/- English proof (translation)
Apply the tactic sequence `by_cases h : q <;> simp [ind, h]`.
-/
private theorem ind_le_one' (q : Prop) : ind q ≤ 1 := by
  by_cases h : q <;> simp [ind, h]

/- English proof (translation)
Distinguish the cases in `h : q`. Simplify `h1 h` using `[ind, h]`. Simplify `h0` using `[ind, h]`.
-/
private theorem ind_le' {q : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : q → 1 ≤ x) : ind q ≤ x := by
  by_cases h : q
  · simpa [ind, h] using h1 h
  · simpa [ind, h] using h0

/- English proof (translation)
Use `(expectation_spec p).2.1 S (fun T => 1 - f T) f` as an intermediate fact. Simplify using `only [sub_add_cancel] at this`. Rewrite `this` using `[(expectation_spec p).1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem bernoulliExpectation_one_sub (p : ℕ → ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    exP p S (fun T => 1 - f T) = 1 - exP p S f := by
  have := (expectation_spec p).2.1 S (fun T => 1 - f T) f
  simp only [sub_add_cancel] at this
  rw [(expectation_spec p).1] at this
  linarith

/- English proof (translation)
Introduce `p δ n r u M₀ i₀ hp h0 h1 hu hn`. Take `⟨ex_const, -, ex_sum, ex_mono', -, -, ex_prod⟩` from `expectation_spec p`. Establish `ex_mono : ∀ {S : Finset ℕ} {f g : Finset ℕ → ℝ}, (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g` using `fun {S f g} h => ex_mono' S f g (fun a _ => ⟨by linarith [(hp a).1], (hp a).2.trans h1⟩) h`. Establish `hmk : ∀ s, markedLow δ r u ≤ exP p (tile r u s) (fun T => ind (Marked T r u s))` using `fun s => marked_ge p δ r u s hp h0 h1`. Establish `h1' : 0 ≤ 1 - δ` using `by linarith`.

Establish `hl : 0 < (6 * r + 1) * u` using `by positivity`. Use `set l := (6 * r + 1) * u with hldef`. Use `set t := n / l with ht`. Establish `hMt : M₀ + 1 ≤ t` using `(Nat.le_div_iff_mul_le hl).2 hn`. Establish `hP1 : ∀ s, exP p (tile r u s) (fun T => ind (Marked T r u s)) ≤ 1` using `fun s => (ex_mono fun T _ => ind_le_one' _).trans (ex_const _ _).le`.

Establish `hπ0 : 0 ≤ markedLow δ r u` using `by unfold markedLow; positivity`. Establish `hπ1 : markedLow δ r u ≤ 1` using `(hmk 0).trans (hP1 0)`. Set `J : ℕ → Finset ℕ` to `fun s₀ => ((Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t).erase (i₀ / l)`. Establish `hJc : ∀ s₀, M₀ ≤ (J s₀).card` using `fun s₀ => by`. Establish `h2 : ((Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t).card = M₀ + 1`.

Rewrite using `[Finset.card_image_of_injOn, Finset.card_range]`. Introduce `i hi j hj hij`. Establish `hi'` using `Finset.mem_range.1 (Finset.mem_coe.1 hi)`. Establish `hj'` using `Finset.mem_range.1 (Finset.mem_coe.1 hj)`. Conclude with `Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' s₀ hij) (by omega) (by omega)`.

Establish `h3` using `Finset.pred_card_le_card_erase (s := (Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t) (a := i₀ / l)`. Simplify using `only [J]`. Use linear arithmetic over natural numbers and integers. Establish `hnot : ∀ s, s ≠ i₀ / l → i₀ ∉ tile r u s` using `fun s hs h => by`. Rewrite `h` using `[tile, Finset.mem_Ico]`.

Conclude with `hs (Nat.div_eq_of_lt_le h.1 h.2).symm`. Establish `hJs : ∀ s₀, ∀ s ∈ J s₀, tile r u s ⊆ (Finset.range n).erase i₀` using `fun s₀ s hs x hx => by`. Take `⟨hs1, hs2⟩` from `Finset.mem_erase.1 hs`. Take `⟨j, _, hj⟩` from `Finset.mem_image.1 hs2`. Establish `hst : s + 1 ≤ t` using `by rw [← hj]; exact Nat.mod_lt _ (by omega)`.

Use `Finset.mem_erase.2 ⟨fun h => hnot s hs1 (h ▸ hx), Finset.mem_range.2 ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[tile, Finset.mem_Ico]`. Conclude with `hx.2.trans_le ((Nat.le_div_iff_mul_le hl).1 hst)`. Combine the equalities or inequalities in the displayed calculation. Establish `hnn : ∀ U s₀, 0 ≤ ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s))` using `fun U s₀ => Finset.prod_nonneg fun s _ => sub_nonneg.2 (ind_le_one' _)`.

Use `ex_mono fun U hU => ind_le' (Finset.sum_nonneg fun _ _ => hnn _ _) ?_` and prove the remaining obligations. Introduce `h`. Unfold `CondTiles at h`. Use `push Not at h`. Take `⟨s₀, hs₀, h⟩` from `h`.

Use `le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun s₀ => ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s))) (fun _ _ => hnn _ _) (Finset.mem_range.2 hs₀))` and prove the remaining obligations. Use `(Finset.prod_eq_one fun s hs => ?_).symm` and prove the remaining obligations. Take `⟨hs1, hs2⟩` from `Finset.mem_erase.1 hs`. Take `⟨j, hj, hjs⟩` from `Finset.mem_image.1 hs2`. Rewrite using `[ind_neg', sub_zero]`.

Introduce `hM`. Use `h j (by have := Finset.mem_range.1 hj; omega) ?_` and prove the remaining obligations. Establish `hjs' : (s₀ + j) % t = s` using `hjs`. Rewrite using `[hjs']`. Use `marked_congr ?_ hM` and prove the remaining obligations.

Rewrite using `[Finset.insert_inter_of_notMem (hnot s hs1), Finset.inter_assoc, Finset.inter_self]`. Use `_ ≤ ∑ s₀ ∈ Finset.range t, (1 - markedLow δ r u) ^ M₀ := by`. Rewrite using `[ex_sum]`. Use `Finset.sum_le_sum fun s₀ _ => ?_` and prove the remaining obligations. Rewrite using `[ex_prod (J s₀) (tile r u) (fun s V => 1 - ind (Marked V r u s)) _ (fun i _ j _ hij => tile_disjoint hij) (hJs s₀)]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun s _ => ?_) fun s _ => ?_` and prove the remaining obligations. Rewrite using `[bernoulliExpectation_one_sub]`. Combine the linear relations using `[hP1 s]`. Rewrite using `[bernoulliExpectation_one_sub]`.

Combine the linear relations using `[hmk s]`. Use `_ ≤ _ := by`. Rewrite using `[Finset.prod_const]`. Conclude with `pow_le_pow_of_le_one (by linarith) (by linarith) (hJc s₀)`. Use `_ ≤ _ := by`.

Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self n l) (pow_nonneg (by linarith) _)`.
-/
theorem UpperTheory.BernoulliSumsFrobeniusOrbits.tiles_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (n r u M₀ i₀ : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 1 ≤ u →
      (M₀ + 1) * ((6 * r + 1) * u) ≤ n →
      exP p ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) ≤ n * (1 - markedLow δ r u) ^ M₀ := by
  intro p δ n r u M₀ i₀ hp h0 h1 hu hn
  obtain ⟨ex_const, -, ex_sum, ex_mono', -, -, ex_prod⟩ := expectation_spec p
  have ex_mono : ∀ {S : Finset ℕ} {f g : Finset ℕ → ℝ}, (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g :=
    fun {S f g} h => ex_mono' S f g (fun a _ => ⟨by linarith [(hp a).1], (hp a).2.trans h1⟩) h
  have hmk : ∀ s, markedLow δ r u ≤ exP p (tile r u s) (fun T => ind (Marked T r u s)) :=
    fun s => marked_ge p δ r u s hp h0 h1
  have h1' : 0 ≤ 1 - δ := by linarith
  have hl : 0 < (6 * r + 1) * u := by positivity
  set l := (6 * r + 1) * u with hldef
  set t := n / l with ht
  have hMt : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hl).2 hn
  have hP1 : ∀ s, exP p (tile r u s) (fun T => ind (Marked T r u s)) ≤ 1 := fun s =>
    (ex_mono fun T _ => ind_le_one' _).trans (ex_const _ _).le
  have hπ0 : 0 ≤ markedLow δ r u := by unfold markedLow; positivity
  have hπ1 : markedLow δ r u ≤ 1 := (hmk 0).trans (hP1 0)
  let J : ℕ → Finset ℕ := fun s₀ =>
    ((Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t).erase (i₀ / l)
  have hJc : ∀ s₀, M₀ ≤ (J s₀).card := fun s₀ => by
    have h2 : ((Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t).card = M₀ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' := Finset.mem_range.1 (Finset.mem_coe.1 hi)
      have hj' := Finset.mem_range.1 (Finset.mem_coe.1 hj)
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' s₀ hij) (by omega) (by omega)
    have h3 := Finset.pred_card_le_card_erase
      (s := (Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t) (a := i₀ / l)
    simp only [J]
    omega
  have hnot : ∀ s, s ≠ i₀ / l → i₀ ∉ tile r u s := fun s hs h => by
    rw [tile, Finset.mem_Ico] at h
    exact hs (Nat.div_eq_of_lt_le h.1 h.2).symm
  have hJs : ∀ s₀, ∀ s ∈ J s₀, tile r u s ⊆ (Finset.range n).erase i₀ := fun s₀ s hs x hx => by
    obtain ⟨hs1, hs2⟩ := Finset.mem_erase.1 hs
    obtain ⟨j, _, hj⟩ := Finset.mem_image.1 hs2
    have hst : s + 1 ≤ t := by rw [← hj]; exact Nat.mod_lt _ (by omega)
    refine Finset.mem_erase.2 ⟨fun h => hnot s hs1 (h ▸ hx), Finset.mem_range.2 ?_⟩
    rw [tile, Finset.mem_Ico] at hx
    exact hx.2.trans_le ((Nat.le_div_iff_mul_le hl).1 hst)
  calc _ ≤ exP p ((Finset.range n).erase i₀) (fun U => ∑ s₀ ∈ Finset.range t,
          ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s))) := by
        have hnn : ∀ U s₀, 0 ≤ ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s)) :=
          fun U s₀ => Finset.prod_nonneg fun s _ => sub_nonneg.2 (ind_le_one' _)
        refine ex_mono fun U hU => ind_le' (Finset.sum_nonneg fun _ _ => hnn _ _) ?_
        intro h
        unfold CondTiles at h
        push Not at h
        obtain ⟨s₀, hs₀, h⟩ := h
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum
          (f := fun s₀ => ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s)))
          (fun _ _ => hnn _ _) (Finset.mem_range.2 hs₀))
        refine (Finset.prod_eq_one fun s hs => ?_).symm
        obtain ⟨hs1, hs2⟩ := Finset.mem_erase.1 hs
        obtain ⟨j, hj, hjs⟩ := Finset.mem_image.1 hs2
        rw [ind_neg', sub_zero]
        intro hM
        refine h j (by have := Finset.mem_range.1 hj; omega) ?_
        have hjs' : (s₀ + j) % t = s := hjs
        rw [hjs']
        refine marked_congr ?_ hM
        rw [Finset.insert_inter_of_notMem (hnot s hs1), Finset.inter_assoc, Finset.inter_self]
    _ ≤ ∑ s₀ ∈ Finset.range t, (1 - markedLow δ r u) ^ M₀ := by
        rw [ex_sum]
        refine Finset.sum_le_sum fun s₀ _ => ?_
        rw [ex_prod (J s₀) (tile r u) (fun s V => 1 - ind (Marked V r u s)) _
          (fun i _ j _ hij => tile_disjoint hij) (hJs s₀)]
        calc _ ≤ ∏ s ∈ J s₀, (1 - markedLow δ r u) := by
              refine Finset.prod_le_prod (fun s _ => ?_) fun s _ => ?_
              · rw [bernoulliExpectation_one_sub]; linarith [hP1 s]
              · rw [bernoulliExpectation_one_sub]; linarith [hmk s]
          _ ≤ _ := by
              rw [Finset.prod_const]
              exact pow_le_pow_of_le_one (by linarith) (by linarith) (hJc s₀)
    _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self n l)
          (pow_nonneg (by linarith) _)
