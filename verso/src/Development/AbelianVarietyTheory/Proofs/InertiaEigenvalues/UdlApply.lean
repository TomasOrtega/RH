import Mathlib

namespace GlobalTheory.UnipotentDecomposition

open Matrix

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Repeatedly rewrite using `[Matrix.mul_diagonal]`.
-/
theorem udl_apply {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_diagonal]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `g _ _`. Use `⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩` and prove the remaining obligations.

Use extensionality with `i`. Conclude with `i.elim0`. Consider the case `succ n ih`. Introduce `g hg hu`. Use `set a : Oˣ := (hu (Fin.last n)).unit with ha`.

Establish `haa : (a : O) = g (Fin.last n) (Fin.last n)` using `IsUnit.unit_spec _`. Establish `hinv : (↑a⁻¹ : O) * ↑a = 1` using `Units.inv_mul a`. Use `set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def`. Use `set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def`. Use `set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def`.

Establish `hr : ∀ i, α ∣ r i` using `fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)`. Establish `hc : ∀ j, β ∣ c j` using `fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)`. Establish `hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j)`. Introduce `i j`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)`. Introduce `h`. Conclude with `dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)`. Establish `hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i`.

Introduce `i`. Rewrite using `[show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]`. Conclude with `Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _`. Establish `hGu : ∀ i, IsUnit (G i i)`. Introduce `i`.

Assume the negation of the conclusion as `h`. Establish `h1 : r i * ↑a⁻¹ * c i ∈ nonunits O` using `fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')`. Establish `h2` using `IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1`. Establish `h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc` using `sub_add_cancel _ _`. Rewrite `h2` using `[h3]`.

Conclude with `h2 (hu _)`. Take `⟨U, D, L, hU, hL, hUDL, hD⟩` from `ih G hG hGu`. Use `⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O) (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j) (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i, fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i, Matrix.of fun i j => Fi …` and prove the remaining obligations. Introduce `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`.

Simplify using the standard rewrite rules. Simplify using `[Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]`. Apply the tactic sequence `simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)] first | exact hr i | exact (hr i).mul_right _`. Simplify using `using hU i j`. Introduce `i j`.

Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`. Simplify using the standard rewrite rules. Apply the tactic sequence `simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)] first | exact hc j | exact (hc j).mul_left _`. Simplify using `[Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]`. Simplify using `using hL i j`.

Use extensionality with `i j`. Rewrite using `[udl_apply, Fin.sum_univ_castSucc]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`. Simplify using `[haa]`. Simplify using `[c] done`.

Simplify using `[r] done`. Establish `e` using `congrFun (congrFun hUDL i) j`. Rewrite `e` using `[udl_apply]`. Simplify using `only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]`. Rewrite using `[← e]`.

Simplify using `only [G]`. Take the linear combination `(-(r i * ↑a⁻¹ * c j)) * hinv`. Introduce `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[haa]`.

Establish `e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i`. Simplify using `[G]`. Expand and normalize the polynomial expressions, which then agree. Simplify `dvd_sub (hD i) (hrc i)` using `[e]`.
-/
theorem key {O : Type} [CommRing O] [IsLocalRing O] {α β : O} (hab : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
      (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        (∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)) ∧
        (∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)) ∧
        g = (u * Matrix.diagonal fun i => (d i : O)) * l ∧ ∀ i, α * β ∣ (d i : O) - g i i := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    refine ⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    ext i; exact i.elim0
  | succ n ih =>
    intro g hg hu
    set a : Oˣ := (hu (Fin.last n)).unit with ha
    have haa : (a : O) = g (Fin.last n) (Fin.last n) := IsUnit.unit_spec _
    have hinv : (↑a⁻¹ : O) * ↑a = 1 := Units.inv_mul a
    set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def
    set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def
    set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def
    have hr : ∀ i, α ∣ r i := fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)
    have hc : ∀ j, β ∣ c j := fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)
    have hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j) := by
      intro i j
      constructor
      · intro h
        exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)
      · intro h
        exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)
    have hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i := by
      intro i
      rw [show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]
      exact Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _
    have hGu : ∀ i, IsUnit (G i i) := by
      intro i
      by_contra h
      have h1 : r i * ↑a⁻¹ * c i ∈ nonunits O := fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')
      have h2 := IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1
      have h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc := sub_add_cancel _ _
      rw [h3] at h2
      exact h2 (hu _)
    obtain ⟨U, D, L, hU, hL, hUDL, hD⟩ := ih G hG hGu
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
              (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i,
            fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i,
            Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun j' => ↑a⁻¹ * c j') j)
              (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => L i' j') j) i,
            ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
        first | exact hr i | exact (hr i).mul_right _
      · simpa using hU i j
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
        first | exact hc j | exact (hc j).mul_left _
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
      · simpa using hL i j
    · ext i j
      rw [udl_apply, Fin.sum_univ_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [haa]
      · simp [c]
        done
      · simp [r]
        done
      · have e := congrFun (congrFun hUDL i) j
        rw [udl_apply] at e
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]
        rw [← e]
        simp only [G]
        linear_combination (-(r i * ↑a⁻¹ * c j)) * hinv
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [haa]
      · have e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i := by
          simp [G]; ring
        simpa [e] using dvd_sub (hD i) (hrc i)

/- English proof (translation)
Introduce `d1 d2 d3 O _ _ α β hab n g hg hu`. Conclude with `key hab n g hg hu`.
-/
theorem main : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by
  intro d1 d2 d3 O _ _ α β hab n g hg hu
  exact key hab n g hg hu

end GlobalTheory.UnipotentDecomposition
