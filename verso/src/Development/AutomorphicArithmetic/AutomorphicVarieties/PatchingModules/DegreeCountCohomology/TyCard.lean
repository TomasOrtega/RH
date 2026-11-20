import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hd : (w : Matrix (Fin n) (Fin n) R).det = 0`. Rewrite using `[Matrix.det_apply]`. Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `h σ`. Establish `hp : ∏ j, (w : Matrix (Fin n) (Fin n) R) (σ j) j = 0` using `Finset.prod_eq_zero (f := fun j => (w : Matrix (Fin n) (Fin n) R) (σ j) j) (Finset.mem_univ i) hi`. Rewrite using `[hp, smul_zero]`. Establish `hu : IsUnit (w : Matrix (Fin n) (Fin n) R).det` using `(Matrix.isUnit_iff_isUnit_det _).1 w.isUnit`. Conclude with `hu.ne_zero hd`.
-/
private theorem tc_perm {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : GL (Fin n) R) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) i ≠ 0 := by
  by_contra h
  push Not at h
  have hd : (w : Matrix (Fin n) (Fin n) R).det = 0 := by
    rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨i, hi⟩ := h σ
    have hp : ∏ j, (w : Matrix (Fin n) (Fin n) R) (σ j) j = 0 :=
      Finset.prod_eq_zero (f := fun j => (w : Matrix (Fin n) (Fin n) R) (σ j) j) (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  have hu : IsUnit (w : Matrix (Fin n) (Fin n) R).det := (Matrix.isUnit_iff_isUnit_det _).1 w.isUnit
  exact hu.ne_zero hd

/- English proof (translation)
Use `set M : Matrix (Fin n) (Fin n) R := (w : Matrix (Fin n) (Fin n) R) with hM`. Use `set N : Matrix (Fin n) (Fin n) R := ((w⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hN`. Set `Dt : Matrix (Fin n) (Fin n) R` to `Matrix.diagonal fun k => if t k then 1 else 0`. Set `Db : Matrix (Fin n) (Fin n) R` to `Matrix.diagonal fun k => if b k then 1 else 0`. Establish `hc : M * Dt = Db * M`.

Use extensionality with `p q`. Simplify using `only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hpq : b p = t q`. Rewrite using `[hpq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[show M p q = 0 from h p q hpq]`. Simplify using the standard rewrite rules. Establish `hNM : N * M = 1` using `Units.inv_mul w`. Establish `hMN : M * N = 1` using `Units.mul_inv w`. Establish `key : Dt * N = N * Db`.

Combine the equalities or inequalities in the displayed calculation. Establish `hij` using `congrFun (congrFun key i) j`. Simplify using `only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij`. Apply the tactic sequence `cases hti : t i <;> cases hbj : b j <;> simp [hti, hbj] at hij e ⊢ <;> first | exact hij | exact hij.symm`.
-/
private theorem tc_inv {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (b t : Fin n → Bool)
    (h : ∀ i j, b i ≠ t j → w i j = 0) (i j : Fin n) (e : t i ≠ b j) : (w⁻¹ : GL (Fin n) R) i j = 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) R := (w : Matrix (Fin n) (Fin n) R) with hM
  set N : Matrix (Fin n) (Fin n) R := ((w⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hN
  let Dt : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if t k then 1 else 0
  let Db : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if b k then 1 else 0
  have hc : M * Dt = Db * M := by
    ext p q
    simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : b p = t q
    · rw [hpq]; ring
    · rw [show M p q = 0 from h p q hpq]; simp
  have hNM : N * M = 1 := Units.inv_mul w
  have hMN : M * N = 1 := Units.mul_inv w
  have key : Dt * N = N * Db := by
    calc Dt * N = N * M * Dt * N := by rw [hNM, Matrix.one_mul]
      _ = N * (M * Dt) * N := by simp only [Matrix.mul_assoc]
      _ = N * (Db * M) * N := by rw [hc]
      _ = N * Db * (M * N) := by simp only [Matrix.mul_assoc]
      _ = N * Db := by rw [hMN, Matrix.mul_one]
  have hij := congrFun (congrFun key i) j
  simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  cases hti : t i <;> cases hbj : b j <;> simp [hti, hbj] at hij e ⊢ <;>
    first | exact hij | exact hij.symm

/- English proof (translation)
Establish `hU : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2) = ((Finset.univ.filter fun i => t i = true) ×ˢ (Finset.univ.filter fun i => t i = true)).filter (fun p => p.1 < p.2) ∪ ((Finset.univ.filter fun i => ¬ t i = true) ×ˢ (Finset.univ.filter fun i => ¬ t i = …`. Use extensionality with `⟨x, y⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]`. Apply the tactic sequence `cases t x <;> cases t y <;> simp`. Rewrite using `[hU, Finset.card_union_of_disjoint, Finset.card_product_filter_lt, Finset.card_product_filter_lt]`.

Rewrite using `[Finset.disjoint_left]`. Introduce and unpack `⟨x, y⟩ h1 h2`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2`. Conclude with `h2.1.1 h1.1.1`.
-/
private theorem tc_same {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card =
      (Finset.univ.filter fun i => t i = true).card.choose 2 +
        (Finset.univ.filter fun i => ¬ t i = true).card.choose 2 := by
  classical
  have hU : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2) =
      ((Finset.univ.filter fun i => t i = true) ×ˢ (Finset.univ.filter fun i => t i = true)).filter
          (fun p => p.1 < p.2) ∪
        ((Finset.univ.filter fun i => ¬ t i = true) ×ˢ
          (Finset.univ.filter fun i => ¬ t i = true)).filter (fun p => p.1 < p.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]
    cases t x <;> cases t y <;> simp
  rw [hU, Finset.card_union_of_disjoint, Finset.card_product_filter_lt,
    Finset.card_product_filter_lt]
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
  exact h2.1.1 h1.1.1

/- English proof (translation)
Establish `hsplit : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card`. Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`.

The claim follows by propositional logic. Rewrite using `[Finset.disjoint_left]`. Introduce `p h1 h2`. Simplify using `only [Finset.mem_filter] at h1 h2`. Conclude with `h2.2.2 h1.2.2`.

Establish `htot : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2`. Simplify using `using Fintype.card_product_filter_lt (α := Fin n)`. Establish `hcard : (Finset.univ.filter fun i => t i = true).card + (Finset.univ.filter fun i => ¬ t i = true).card = n`. Rewrite using `[Finset.card_filter_add_card_filter_not]`. Simplify using the standard rewrite rules.

Establish `hch : ∀ a b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b`. Introduce `a b`. Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[← Nat.add_assoc, Nat.choose_succ_succ', Nat.choose_succ_succ' k, Nat.choose_one_right, Nat.choose_one_right, ih]`. Expand and normalize the polynomial expressions, which then agree. Establish `hh` using `hch (Finset.univ.filter fun i => t i = true).card (Finset.univ.filter fun i => ¬ t i = true).card`. Rewrite `hh` using `[hcard]`. Rewrite `hsplit` using `[htot, tc_same t]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem tc_diff {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card =
      (Finset.univ.filter fun i => t i = true).card *
        (Finset.univ.filter fun i => ¬ t i = true).card := by
  classical
  have hsplit : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2.2 h1.2.2
  have htot : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2 := by
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have hcard : (Finset.univ.filter fun i => t i = true).card +
      (Finset.univ.filter fun i => ¬ t i = true).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hch : ∀ a b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    intro a b
    induction b with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.choose_succ_succ' k, Nat.choose_one_right,
        Nat.choose_one_right, ih]
      ring
  have hh := hch (Finset.univ.filter fun i => t i = true).card
    (Finset.univ.filter fun i => ¬ t i = true).card
  rw [hcard] at hh
  rw [htot, tc_same t] at hsplit
  linarith

/- English proof (translation)
Introduce `l _ F n x v g`. Take `⟨σ, hσ⟩` from `tc_perm (x.w v)`. Establish `hty : ∀ j, x.ty v j = decide (((σ j : Fin n) : ℕ) < x.a)`. Introduce `j`. Assume the negation of the conclusion as `hne`.

Conclude with `hσ j (x.w_blk v (σ j) j (Ne.symm hne))`. Establish `hT : (Finset.univ.filter fun i => x.ty v i = true).card = x.a`. Rewrite using `[← Fintype.card_subtype, ← Fintype.card_fin_lt_of_le x.a_le]`. Use `Fintype.card_congr (Equiv.subtypeEquiv σ fun j => ?_)` and prove the remaining obligations. Rewrite using `[hty j]`.

Simplify using the standard rewrite rules. Establish `hF : (Finset.univ.filter fun i => ¬ x.ty v i = true).card = n - x.a`. Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun i => x.ty v i = true)` as an intermediate fact. Simplify using `only [Finset.card_univ, Fintype.card_fin] at this`. Use linear arithmetic over natural numbers and integers.

Use `⟨hT, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[tc_same, tc_diff, hT, hF]`. Simplify using `[nu]`. Rewrite using `[tc_diff, hT, hF]`. Introduce `i j e`.

Conclude with `tc_inv (x.w v) (fun k => decide ((k : ℕ) < x.a)) (x.ty v) (fun p q hpq => x.w_blk v p q hpq) i j e`.
-/
theorem UpperTheory.V.Pa.tyCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (v : F.Vl) (g : ℕ), (Finset.univ.filter fun i => x.ty v i = true).card = x.a ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2).card + g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = nu n x.a g ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = x.a * (n - x.a) ∧ ∀ i j : Fin n, x.ty v i ≠ decide ((j : ℕ) < x.a) → ((x.w v)⁻¹ : GL (Fin n) x.A) i j = 0 := by
  intro l _ F n x v g
  classical
  obtain ⟨σ, hσ⟩ := tc_perm (x.w v)
  have hty : ∀ j, x.ty v j = decide (((σ j : Fin n) : ℕ) < x.a) := by
    intro j
    by_contra hne
    exact hσ j (x.w_blk v (σ j) j (Ne.symm hne))
  have hT : (Finset.univ.filter fun i => x.ty v i = true).card = x.a := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin_lt_of_le x.a_le]
    refine Fintype.card_congr (Equiv.subtypeEquiv σ fun j => ?_)
    rw [hty j]
    simp
  have hF : (Finset.univ.filter fun i => ¬ x.ty v i = true).card = n - x.a := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => x.ty v i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [tc_same, tc_diff, hT, hF]
    simp [nu]
  · rw [tc_diff, hT, hF]
  · intro i j e
    exact tc_inv (x.w v) (fun k => decide ((k : ℕ) < x.a)) (x.ty v)
      (fun p q hpq => x.w_blk v p q hpq) i j e
