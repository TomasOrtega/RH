import Mathlib

/- English proof (translation)
Introduce `L _ _ n r h0 h1`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _`. Conclude with `⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩`.

Consider the case `succ n ih`. Introduce `A hA`. Establish `hlc : ∀ i : Fin n, Fin.last n ≠ i.castSucc` using `fun i => (Fin.castSucc_lt_last i).ne'`. Establish `hcl : ∀ i : Fin n, i.castSucc ≠ Fin.last n` using `fun i => (Fin.castSucc_lt_last i).ne`. Establish `hd1 : ‖A (Fin.last n) (Fin.last n) - 1‖ ≤ r`.

Simplify using `using hA (Fin.last n) (Fin.last n)`. Establish `hd : ‖A (Fin.last n) (Fin.last n)‖ = 1`. Establish `hne : ‖A (Fin.last n) (Fin.last n) - 1‖ ≠ ‖(1 : L)‖`. Rewrite using `[norm_one]`. Conclude with `(hd1.trans_lt h1).ne`.

Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Rewrite using `[this]`. Conclude with `max_eq_right (hd1.trans h1.le)`. Establish `hd0 : A (Fin.last n) (Fin.last n) ≠ 0`.

Introduce `h`. Rewrite `hd` using `[h, norm_zero]`. Conclude with `zero_ne_one hd`. Establish `hb : ∀ i : Fin n, ‖A i.castSucc (Fin.last n)‖ ≤ r` using `fun i => by`. Simplify `hA i.castSucc (Fin.last n)` using `[Matrix.one_apply_ne (hcl i)]`.

Establish `hc : ∀ i : Fin n, ‖A (Fin.last n) i.castSucc‖ ≤ r` using `fun i => by`. Simplify `hA (Fin.last n) i.castSucc` using `[Matrix.one_apply_ne (hlc i)]`. Establish `hu : ∀ i : Fin n, ‖A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)‖ ≤ r` using `fun i => by rw [norm_div, hd, div_one]; exact hb i`. Establish `hone : ∀ i j : Fin n, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i.castSucc j.castSucc = (1 : Matrix (Fin n) (Fin n) L) i j` using `fun i j => by`. Simplify using `[Matrix.one_apply]`.

Take `⟨U, W, hU, hW, hU1, hW1, hUW⟩` from `ih (Matrix.of fun i j : Fin n => A i.castSucc j.castSucc - A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n) * A (Fin.last n) j.castSucc) (fun i j => by`. Establish `h2` using `hA i.castSucc j.castSucc`. Rewrite `h2` using `[Matrix.sub_apply, hone]`. Rewrite using `[Matrix.sub_apply, Matrix.of_apply, sub_right_comm, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)` and prove the remaining obligations.

Rewrite using `[norm_neg, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => L) (Fin.lastCases (motive := fun _ => L) 1 (fun _ => 0) j) (fun i' => Fin.lastCases (motive := fun _ => L) (A i'.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)) (fun j' => U i' j') j) i, Matrix.of fun i j => Fin.lastCas …` and prove the remaining obligations. Introduce `i j hij`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases`.

Conclude with `absurd hij (lt_irrefl _)`. Simplify using the standard rewrite rules. Conclude with `absurd hij (Fin.le_last _).not_gt`. Simplify `hij)` using `using hU _ _ (by simpa`. Introduce `i j hij`.

Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases`. Conclude with `absurd hij (lt_irrefl _)`. Conclude with `absurd hij (Fin.le_last _).not_gt`. Simplify using the standard rewrite rules. Simplify `hij)` using `using hW _ _ (by simpa`.

Introduce `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases`. Simplify using `using h0`. Simplify `h0` using `[Matrix.one_apply_ne (hlc _)]`. Simplify `hb _` using `[Matrix.one_apply_ne (hcl _), hd]`.

Rewrite using `[Matrix.sub_apply, hone]`. Simplify using `using hU1 _ _`. Introduce `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases`. Simplify using `using hd1`.

Simplify `hc _` using `[Matrix.one_apply_ne (hlc _)]`. Simplify `h0` using `[Matrix.one_apply_ne (hcl _)]`. Rewrite using `[Matrix.sub_apply, hone]`. Simplify using `using hW1 _ _`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply, Fin.sum_univ_castSucc]`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `[hd0]`.

Name the introduced variables `i j`. Use `congrFun (congrFun hUW i) j` as an intermediate fact. Rewrite `this` using `[Matrix.of_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]`. Rewrite using `[← this, sub_add_cancel]`.
-/
theorem UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ),
      (0 : ℝ) ≤ r →
        r < (1 : ℝ) →
          ∀ (A : Matrix (Fin n) (Fin n) L),
            (∀ (i j : Fin n), ‖(A - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) →
              ∃ (U : Matrix (Fin n) (Fin n) L) (W : Matrix (Fin n) (Fin n) L),
                (∀ (i j : Fin n), j < i → U i j = (0 : L)) ∧
                  (∀ (i j : Fin n), i < j → W i j = (0 : L)) ∧
                    (∀ (i j : Fin n), ‖(U - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧
                      (∀ (i j : Fin n), ‖(W - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧ A = U * W := by
  intro L _ _ n r h0 h1
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro A hA
    have hlc : ∀ i : Fin n, Fin.last n ≠ i.castSucc := fun i => (Fin.castSucc_lt_last i).ne'
    have hcl : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    have hd1 : ‖A (Fin.last n) (Fin.last n) - 1‖ ≤ r := by
      simpa using hA (Fin.last n) (Fin.last n)
    have hd : ‖A (Fin.last n) (Fin.last n)‖ = 1 := by
      have hne : ‖A (Fin.last n) (Fin.last n) - 1‖ ≠ ‖(1 : L)‖ := by
        rw [norm_one]; exact (hd1.trans_lt h1).ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, norm_one] at this
      rw [this]
      exact max_eq_right (hd1.trans h1.le)
    have hd0 : A (Fin.last n) (Fin.last n) ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    have hb : ∀ i : Fin n, ‖A i.castSucc (Fin.last n)‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hcl i)] using hA i.castSucc (Fin.last n)
    have hc : ∀ i : Fin n, ‖A (Fin.last n) i.castSucc‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hlc i)] using hA (Fin.last n) i.castSucc
    have hu : ∀ i : Fin n, ‖A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)‖ ≤ r :=
      fun i => by rw [norm_div, hd, div_one]; exact hb i
    have hone : ∀ i j : Fin n, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i.castSucc j.castSucc
        = (1 : Matrix (Fin n) (Fin n) L) i j := fun i j => by
      simp [Matrix.one_apply]
    obtain ⟨U, W, hU, hW, hU1, hW1, hUW⟩ := ih
      (Matrix.of fun i j : Fin n => A i.castSucc j.castSucc -
        A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n) * A (Fin.last n) j.castSucc)
      (fun i j => by
        have h2 := hA i.castSucc j.castSucc
        rw [Matrix.sub_apply, hone] at h2
        rw [Matrix.sub_apply, Matrix.of_apply, sub_right_comm, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
        rw [norm_neg, norm_mul]
        calc _ ≤ r * 1 := mul_le_mul (hu i) ((hc j).trans h1.le) (norm_nonneg _) h0
          _ = r := mul_one r)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => L)
          (A i'.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)) (fun j' => U i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (A (Fin.last n) j)
        (fun i' => Fin.lastCases (motive := fun _ => L) 0 (fun j' => W i' j') j) i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (Fin.le_last _).not_gt
      · simpa using hU _ _ (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Fin.le_last _).not_gt
      · simp
      · simpa using hW _ _ (by simpa using hij)
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using h0
      · simpa [Matrix.one_apply_ne (hlc _)] using h0
      · simpa [Matrix.one_apply_ne (hcl _), hd] using hb _
      · rw [Matrix.sub_apply, hone]
        simpa using hU1 _ _
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using hd1
      · simpa [Matrix.one_apply_ne (hlc _)] using hc _
      · simpa [Matrix.one_apply_ne (hcl _)] using h0
      · rw [Matrix.sub_apply, hone]
        simpa using hW1 _ _
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simp
      · simp
      · simp [hd0]
      · rename_i i j
        have := congrFun (congrFun hUW i) j
        rw [Matrix.of_apply, Matrix.mul_apply] at this
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [← this, sub_add_cancel]
