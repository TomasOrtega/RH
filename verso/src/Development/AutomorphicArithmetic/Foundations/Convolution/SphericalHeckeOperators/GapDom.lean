import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Rewrite `h` using `[AddMonoidAlgebra.coeff_single]`. Simplify using `using Finsupp.support_single_subset h`.
-/
private theorem mem_supp_monomial {n : ℕ} {a b : Fin n → ℤ}
    (h : a ∈ (monomial b : LaurentRing n).coeff.support) : a = b := by
  rw [AddMonoidAlgebra.coeff_single] at h
  simpa using Finsupp.support_single_subset h

/- English proof (translation)
Use `Finset.card_le_card_of_injOn (s := T.filter fun p => p.1 = j ∨ p.2 = j) (t := Finset.univ) (fun p : Fin n × Fin n => if p.1 = j then p.2 else p.1) (fun _ _ => by simp) (by` as an intermediate fact. Introduce and unpack `⟨a, b⟩ hp ⟨c, d⟩ hq h`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq`. Establish `h1 : a < b` using `by simpa [pairs] using hT hp.1`. Establish `h2 : c < d` using `by simpa [pairs] using hT hq.1`.

Establish `h3` using `hp.2`. Establish `h4` using `hq.2`. Simplify using `only at h h3 h4`. Simplify using `only [Prod.mk.injEq]`. Apply the tactic sequence `split_ifs at h <;> omega)`.

Simplify using `using this`.
-/
private theorem card_touch_le {n : ℕ} (T : Finset (Fin n × Fin n)) (hT : T ⊆ pairs n) (j : Fin n) :
    (T.filter fun p => p.1 = j ∨ p.2 = j).card ≤ n := by
  have := Finset.card_le_card_of_injOn (s := T.filter fun p => p.1 = j ∨ p.2 = j) (t := Finset.univ)
    (fun p : Fin n × Fin n => if p.1 = j then p.2 else p.1) (fun _ _ => by simp) (by
      rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : a < b := by simpa [pairs] using hT hp.1
      have h2 : c < d := by simpa [pairs] using hT hq.1
      have h3 := hp.2
      have h4 := hq.2
      simp only at h h3 h4
      simp only [Prod.mk.injEq]
      split_ifs at h <;> omega)
  simpa using this

private def Bd {n : ℕ} (T : Finset (Fin n × Fin n)) (e : Fin n → ℤ) : Prop :=
  ∀ j, 0 ≤ e j ∧ e j ≤ ((T.filter fun p => p.1 = j ∨ p.2 = j).card : ℤ)

/- English proof (translation)
Introduce `j`. Take `⟨h0, h1⟩` from `he j`. Rewrite using `[Finset.filter_insert]`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality.

Rewrite using `[if_pos (by tauto), Finset.card_insert_of_notMem (by simp [hp])]`. Simplify using `only [Pi.add_apply, Pi.single_eq_same]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Pi.add_apply, Pi.single_eq_of_ne hj] split_ifs`.

Rewrite using `[Finset.card_insert_of_notMem (by simp [hp])]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
private theorem bd_insert {n : ℕ} {T : Finset (Fin n × Fin n)} {p : Fin n × Fin n} (hp : p ∉ T)
    {e : Fin n → ℤ} (he : Bd T e) {k : Fin n} (hk : k = p.1 ∨ k = p.2) :
    Bd (insert p T) (Pi.single k 1 + e) := by
  intro j
  obtain ⟨h0, h1⟩ := he j
  rw [Finset.filter_insert]
  by_cases hj : j = k
  · subst hj
    rw [if_pos (by tauto), Finset.card_insert_of_notMem (by simp [hp])]
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hj]
    split_ifs
    · rw [Finset.card_insert_of_notMem (by simp [hp])]
      push_cast
      omega
    · omega

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro j`. Simplify using the standard rewrite rules. Consider the case `insert p T hp ih => rw [Finset.sum_insert hp]`. Conclude with `bd_insert hp ih (hf p)`.
-/
private theorem bd_sum {n : ℕ} (f : Fin n × Fin n → Fin n) (hf : ∀ p, f p = p.1 ∨ f p = p.2)
    (T : Finset (Fin n × Fin n)) : Bd T (∑ p ∈ T, Pi.single (f p) 1) := by
  induction T using Finset.induction_on with
  | empty => intro j; simp
  | insert p T hp ih => rw [Finset.sum_insert hp]; exact bd_insert hp ih (hf p)

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `a ha`. Rewrite `ha` using `[Finset.prod_empty]`. Establish `: a = 0` using `mem_supp_monomial (b := 0) ha`.

Substitute `this` using the available equality. Introduce `j`. Simplify using the standard rewrite rules. Consider the case `insert p T hp ih`. Introduce `a ha`.

Rewrite `ha` using `[Finset.prod_insert hp]`. Take `⟨b, hb, c, hc, rfl⟩` from `Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)`. Rewrite `hb` using `[AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul]`. Break down `Finset.mem_union.1 (Finsupp.support_sub hb) with hb | hb` into its components or cases. Rewrite using `[mem_supp_monomial hb]`.

Conclude with `bd_insert hp (ih c hc) (Or.inl rfl)`. Rewrite using `[mem_supp_monomial (Finsupp.support_smul hb)]`. Conclude with `bd_insert hp (ih c hc) (Or.inr rfl)`.
-/
private theorem bd_prod {n : ℕ} (t : ℂ) (T : Finset (Fin n × Fin n)) :
    ∀ a ∈ (∏ p ∈ T, (varL p.1 - t • varL p.2) : LaurentRing n).coeff.support, Bd T a := by
  induction T using Finset.induction_on with
  | empty =>
    intro a ha
    rw [Finset.prod_empty] at ha
    have : a = 0 := mem_supp_monomial (b := 0) ha
    subst this
    intro j; simp
  | insert p T hp ih =>
    intro a ha
    rw [Finset.prod_insert hp] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul] at hb
    rcases Finset.mem_union.1 (Finsupp.support_sub hb) with hb | hb
    · rw [mem_supp_monomial hb]; exact bd_insert hp (ih c hc) (Or.inl rfl)
    · rw [mem_supp_monomial (Finsupp.support_smul hb)]; exact bd_insert hp (ih c hc) (Or.inr rfl)

/- English proof (translation)
Introduce `i j hij`. Break down `hij.eq_or_lt with rfl | hij` into its components or cases. Conclude with `le_rfl`. Establish `h1` using `hν i j hij`. Establish `h2` using `(he i).1`.

Establish `h3` using `(he j).2`. Establish `h4` using `card_touch_le T hT j`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem anti_of_bd {n : ℕ} {ν e : Fin n → ℤ} (hν : Gap n ν) {T : Finset (Fin n × Fin n)}
    (hT : T ⊆ pairs n) (he : Bd T e) : Antitone (ν + e) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · have h1 := hν i j hij
    have h2 := (he i).1
    have h3 := (he j).2
    have h4 := card_touch_le T hT j
    simp only [Pi.add_apply]
    omega

/- English proof (translation)
Introduce `n ν hν`. Use `⟨fun S hS => ⟨?_, ?_⟩, fun t a ha => ?_, fun a ha i j hij => ?_⟩` and prove the remaining obligations. Conclude with `anti_of_bd hν (Finset.mem_powerset.1 hS) (bd_sum Prod.fst (fun _ => Or.inl rfl) S)`. Conclude with `anti_of_bd hν Finset.sdiff_subset (bd_sum Prod.snd (fun _ => Or.inr rfl) _)`. Take `⟨b, hb, c, hc, rfl⟩` from `Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)`.

Rewrite using `[mem_supp_monomial hb]`. Conclude with `anti_of_bd hν subset_rfl (bd_prod t _ c hc)`. Establish `h1` using `hν i j hij`. Establish `h2` using `ha hij.le`. Simplify using `only [Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.ConvolutionTheory.H.gapDom :
    ∀ (n : ℕ) (ν : Fin n → ℤ), Gap n ν → (∀ S ∈ (pairs n).powerset, Antitone (ν + eL S) ∧ Antitone (ν + eR S)) ∧
      (∀ t : ℂ, Dom (monomial ν * dPol n t)) ∧ ∀ a, Antitone a → Gap n (a + ν) := by
  intro n ν hν
  refine ⟨fun S hS => ⟨?_, ?_⟩, fun t a ha => ?_, fun a ha i j hij => ?_⟩
  · exact anti_of_bd hν (Finset.mem_powerset.1 hS) (bd_sum Prod.fst (fun _ => Or.inl rfl) S)
  · exact anti_of_bd hν Finset.sdiff_subset (bd_sum Prod.snd (fun _ => Or.inr rfl) _)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [mem_supp_monomial hb]
    exact anti_of_bd hν subset_rfl (bd_prod t _ c hc)
  · have h1 := hν i j hij
    have h2 := ha hij.le
    simp only [Pi.add_apply]
    omega
