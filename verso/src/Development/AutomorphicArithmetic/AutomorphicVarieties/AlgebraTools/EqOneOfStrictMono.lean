import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Establish `key : ∀ z : Fin n, (swap a c z).val = if z.val = a.val then c.val else if z.val = c.val then a.val else z.val`. Introduce `z`. Rewrite using `[swap_apply_def]`. Distinguish the cases in `h1 : z = a`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules. Distinguish the cases in `h2 : z = c`. Substitute `h2` using the available equality. Establish `h1' : z.val ≠ a.val` using `fun e => h1 (Fin.ext e)`. Simplify using `[h1, h1']`.

Establish `h1' : z.val ≠ a.val` using `fun e => h1 (Fin.ext e)`. Establish `h2' : z.val ≠ c.val` using `fun e => h2 (Fin.ext e)`. Simplify using `[h1, h2, h1', h2']`. Rewrite using `[Fin.lt_def, key, key]`. Rewrite `hxy` using `[Fin.lt_def]`.

Establish `hne' : ¬ (x.val = a.val ∧ y.val = c.val)` using `fun e => hne ⟨Fin.ext e.1, Fin.ext e.2⟩`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem swap_lt {n : ℕ} {a c : Fin n} (h : a.val + 1 = c.val) {x y : Fin n} (hxy : x < y)
    (hne : ¬ (x = a ∧ y = c)) : swap a c x < swap a c y := by
  have key : ∀ z : Fin n, (swap a c z).val = if z.val = a.val then c.val else if z.val = c.val then a.val else z.val := by
    intro z
    rw [swap_apply_def]
    by_cases h1 : z = a
    · subst h1
      simp
    · by_cases h2 : z = c
      · subst h2
        have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        simp [h1, h1']
      · have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        have h2' : z.val ≠ c.val := fun e => h2 (Fin.ext e)
        simp [h1, h2, h1', h2']
  rw [Fin.lt_def, key, key]
  rw [Fin.lt_def] at hxy
  have hne' : ¬ (x.val = a.val ∧ y.val = c.val) := fun e => hne ⟨Fin.ext e.1, Fin.ext e.2⟩
  split_ifs <;> omega

/- English proof (translation)
Simplify using `[invSet, pairs]`.
-/
private theorem mem_invSet {n : ℕ} (w : Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ invSet w ↔ p.1 < p.2 ∧ w⁻¹ p.2 < w⁻¹ p.1 := by
  simp [invSet, pairs]

/- English proof (translation)
Conclude with `Equiv.ext fun x => congrFun h.eq_id x`.
-/
private theorem eq_one_of_strictMono {n : ℕ} (w : Perm (Fin n)) (h : StrictMono w) : w = 1 := by
  exact Equiv.ext fun x => congrFun h.eq_id x

/- English proof (translation)
Use extensionality with `⟨x, y⟩`. Rewrite using `[mem_invSet]`. Establish `hinv : ∀ z : Fin n, (Fin.revPerm : Perm (Fin n))⁻¹ z = z.rev`. Introduce `z`. Rewrite using `[Perm.inv_eq_iff_eq, Fin.revPerm_apply, Fin.rev_rev]`.

Simplify using `only [hinv, Fin.rev_lt_rev]`. Simplify using `only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, h⟩⟩`.
-/
private theorem invSet_rev (n : ℕ) : invSet (Fin.revPerm : Perm (Fin n)) = pairs n := by
  ext ⟨x, y⟩
  rw [mem_invSet]
  have hinv : ∀ z : Fin n, (Fin.revPerm : Perm (Fin n))⁻¹ z = z.rev := by
    intro z
    rw [Perm.inv_eq_iff_eq, Fin.revPerm_apply, Fin.rev_rev]
  simp only [hinv, Fin.rev_lt_rev]
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/- English proof (translation)
Introduce `n`. Use `⟨?_, ?_, ?_, invSet_rev n, ?_⟩` and prove the remaining obligations. Introduce `a c hac w hw`. Establish `hlt : a < c`. Rewrite using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers. Establish `hff : ∀ p : Fin n × Fin n, (swap a c (swap a c p.1), swap a c (swap a c p.2)) = p`. Introduce `p`. Simplify using the standard rewrite rules. Establish `hmemimg : ∀ q : Fin n × Fin n, q ∈ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ↔ (swap a c q.1, swap a c q.2) ∈ invSet w`.

Introduce `q`. Rewrite using `[Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Rewrite using `[hff]` and apply the resulting hypothesis.

Introduce `hq`. Conclude with `⟨_, hq, hff q⟩`. Establish `hnot : (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2))`. Rewrite using `[hmemimg, mem_invSet]`. Simplify using `only [swap_apply_left, swap_apply_right]`.

Conclude with `fun h => absurd h.1 (lt_asymm hlt)`. Establish `heq : invSet (swap a c * w) = insert (a, c) ((invSet w).image (fun p => (swap a c p.1, swap a c p.2)))`. Use extensionality with `⟨x, y⟩`. Rewrite using `[Finset.mem_insert, hmemimg, mem_invSet, mem_invSet]`. Simplify using `only [mul_inv_rev, swap_inv, Perm.mul_apply, Prod.mk.injEq]`.

Distinguish the cases in `hp : x = a ∧ y = c`. Take `⟨rfl, rfl⟩` from `hp`. Simplify using `only [swap_apply_left, swap_apply_right]`. Conclude with `⟨fun _ => Or.inl (by simp), fun _ => ⟨hlt, hw⟩⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hxy, hA⟩`. Conclude with `Or.inr ⟨swap_lt hac hxy hp, hA⟩`. Introduce and unpack `(h | ⟨hs, hA⟩)`. Conclude with `absurd h hp`. Use `⟨?_, hA⟩` and prove the remaining obligations.

Break down `lt_trichotomy x y with h | h | h` into its components or cases. Conclude with `h`. Substitute `h` using the available equality. Conclude with `absurd hs (lt_irrefl _)`. Distinguish the cases in `hq : y = a ∧ x = c`.

Take `⟨rfl, rfl⟩` from `hq`. Simplify using `only [swap_apply_left, swap_apply_right] at hA`. Conclude with `absurd hA (lt_asymm hw)`. Conclude with `absurd (swap_lt hac h hq) (lt_asymm hs)`. Use `⟨heq, hnot, ?_⟩` and prove the remaining obligations.

Unfold `invN`. Rewrite using `[heq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective]`. Introduce `p q hpq`. Use `congrArg (fun r : Fin n × Fin n => (swap a c r.1, swap a c r.2)) hpq` as an intermediate fact. Simplify using `only [hff] at this`.

Conclude with `this`. Introduce `w hw`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hw` to reduce the goal to its premises.

Establish `hadj : ∀ a c : Fin n, a.val + 1 = c.val → w⁻¹ a < w⁻¹ c`. Introduce `a c h`. Use `lt_of_le_of_ne (hcon a c h) ?_` and prove the remaining obligations. Introduce `h'`. Use `w⁻¹.injective h'` as an intermediate fact.

Rewrite `h` using `[this]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k + 1 → w⁻¹ i < w⁻¹ j`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `i j h`. Conclude with `hadj i j (by omega)`. Consider the case `succ k ih`. Introduce `i j h`.

Establish `hj` using `j.isLt`. Establish `hm : i.val + k + 1 < n` using `by omega`. Conclude with `lt_trans (ih i ⟨i.val + k + 1, hm⟩ rfl) (hadj _ _ (by show i.val + k + 1 + 1 = j.val; omega))`. Establish `hsm : StrictMono ⇑(w⁻¹)`. Introduce `i j hij`.

Rewrite `hij` using `[Fin.lt_def]`. Conclude with `key (j.val - i.val - 1) i j (by omega)`. Conclude with `inv_eq_one.mp (eq_one_of_strictMono _ hsm)`. Apply `Finset.eq_empty_of_forall_notMem` to reduce the goal to its premises. Introduce `p hp`.

Rewrite `hp` using `[mem_invSet]`. Simplify using `only [inv_one, Perm.one_apply] at hp`. Conclude with `lt_asymm hp.1 hp.2`. Introduce `w hw`. Unfold `invN`.

Rewrite using `[invSet_rev]`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_subset_ne]`. Use `⟨Finset.filter_subset _ _, ?_⟩` and prove the remaining obligations. Introduce `hset`.

Apply `hw` to reduce the goal to its premises. Establish `hall : ∀ i j : Fin n, i < j → w⁻¹ j < w⁻¹ i`. Introduce `i j hij`. Establish `hm : (i, j) ∈ invSet w`. Rewrite using `[hset]`.

Simplify using `[pairs, hij]`. Conclude with `((mem_invSet w _).mp hm).2`. Establish `hsm : StrictMono ⇑(w⁻¹ * (Fin.revPerm : Perm (Fin n)))`. Introduce `i j hij`. Simplify using `only [Perm.mul_apply, Fin.revPerm_apply]`.

Conclude with `hall _ _ (Fin.rev_lt_rev.mpr hij)`. Establish `h1` using `eq_one_of_strictMono _ hsm`. Rewrite `h1` using `[mul_eq_one_iff_eq_inv]`. Conclude with `inv_inj.mp h1`.
-/
theorem UpperTheory.V.AlgebraTools.hkInv :
    ∀ n : ℕ, (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c →
        invSet (swap a c * w) = insert (a, c) ((invSet w).image fun p => (swap a c p.1, swap a c p.2)) ∧
        (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ∧ invN (swap a c * w) = invN w + 1) ∧
      (∀ w : Perm (Fin n), w ≠ 1 → ∃ a c : Fin n, a.val + 1 = c.val ∧ w⁻¹ c < w⁻¹ a) ∧
      invSet (1 : Perm (Fin n)) = ∅ ∧ invSet (Fin.revPerm : Perm (Fin n)) = pairs n ∧
      (∀ w : Perm (Fin n), w ≠ Fin.revPerm → invN w < invN (Fin.revPerm : Perm (Fin n))) := by
  intro n
  refine ⟨?_, ?_, ?_, invSet_rev n, ?_⟩
  · intro a c hac w hw
    have hlt : a < c := by
      rw [Fin.lt_def]
      omega
    have hff : ∀ p : Fin n × Fin n, (swap a c (swap a c p.1), swap a c (swap a c p.2)) = p := by
      intro p
      simp
    have hmemimg : ∀ q : Fin n × Fin n, q ∈ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ↔
        (swap a c q.1, swap a c q.2) ∈ invSet w := by
      intro q
      rw [Finset.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rwa [hff]
      · intro hq
        exact ⟨_, hq, hff q⟩
    have hnot : (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) := by
      rw [hmemimg, mem_invSet]
      simp only [swap_apply_left, swap_apply_right]
      exact fun h => absurd h.1 (lt_asymm hlt)
    have heq : invSet (swap a c * w) = insert (a, c) ((invSet w).image (fun p => (swap a c p.1, swap a c p.2))) := by
      ext ⟨x, y⟩
      rw [Finset.mem_insert, hmemimg, mem_invSet, mem_invSet]
      simp only [mul_inv_rev, swap_inv, Perm.mul_apply, Prod.mk.injEq]
      by_cases hp : x = a ∧ y = c
      · obtain ⟨rfl, rfl⟩ := hp
        simp only [swap_apply_left, swap_apply_right]
        exact ⟨fun _ => Or.inl (by simp), fun _ => ⟨hlt, hw⟩⟩
      · constructor
        · rintro ⟨hxy, hA⟩
          exact Or.inr ⟨swap_lt hac hxy hp, hA⟩
        · rintro (h | ⟨hs, hA⟩)
          · exact absurd h hp
          · refine ⟨?_, hA⟩
            rcases lt_trichotomy x y with h | h | h
            · exact h
            · subst h
              exact absurd hs (lt_irrefl _)
            · by_cases hq : y = a ∧ x = c
              · obtain ⟨rfl, rfl⟩ := hq
                simp only [swap_apply_left, swap_apply_right] at hA
                exact absurd hA (lt_asymm hw)
              · exact absurd (swap_lt hac h hq) (lt_asymm hs)
    refine ⟨heq, hnot, ?_⟩
    unfold invN
    rw [heq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective]
    intro p q hpq
    have := congrArg (fun r : Fin n × Fin n => (swap a c r.1, swap a c r.2)) hpq
    simp only [hff] at this
    exact this
  · intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    have hadj : ∀ a c : Fin n, a.val + 1 = c.val → w⁻¹ a < w⁻¹ c := by
      intro a c h
      refine lt_of_le_of_ne (hcon a c h) ?_
      intro h'
      have := w⁻¹.injective h'
      rw [this] at h
      omega
    have key : ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k + 1 → w⁻¹ i < w⁻¹ j := by
      intro k
      induction k with
      | zero =>
        intro i j h
        exact hadj i j (by omega)
      | succ k ih =>
        intro i j h
        have hj := j.isLt
        have hm : i.val + k + 1 < n := by omega
        exact lt_trans (ih i ⟨i.val + k + 1, hm⟩ rfl) (hadj _ _ (by show i.val + k + 1 + 1 = j.val; omega))
    have hsm : StrictMono ⇑(w⁻¹) := by
      intro i j hij
      rw [Fin.lt_def] at hij
      exact key (j.val - i.val - 1) i j (by omega)
    exact inv_eq_one.mp (eq_one_of_strictMono _ hsm)
  · apply Finset.eq_empty_of_forall_notMem
    intro p hp
    rw [mem_invSet] at hp
    simp only [inv_one, Perm.one_apply] at hp
    exact lt_asymm hp.1 hp.2
  · intro w hw
    unfold invN
    rw [invSet_rev]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hset
    apply hw
    have hall : ∀ i j : Fin n, i < j → w⁻¹ j < w⁻¹ i := by
      intro i j hij
      have hm : (i, j) ∈ invSet w := by
        rw [hset]
        simp [pairs, hij]
      exact ((mem_invSet w _).mp hm).2
    have hsm : StrictMono ⇑(w⁻¹ * (Fin.revPerm : Perm (Fin n))) := by
      intro i j hij
      simp only [Perm.mul_apply, Fin.revPerm_apply]
      exact hall _ _ (Fin.rev_lt_rev.mpr hij)
    have h1 := eq_one_of_strictMono _ hsm
    rw [mul_eq_one_iff_eq_inv] at h1
    exact inv_inj.mp h1
