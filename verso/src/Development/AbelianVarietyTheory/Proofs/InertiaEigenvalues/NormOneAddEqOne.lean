import Mathlib

namespace GlobalTheory.UnitValueExistence

open Matrix

/- English proof (translation)
The claim follows from `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)`.
-/
theorem norm_add_lt_one {E : Type} [NormedField E] [IsUltrametricDist E] {a b : E}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

/- English proof (translation)
Establish `h : ‖(1 : E)‖ ≠ ‖a‖` using `by rw [norm_one]; exact ha.ne'`. Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]`.
-/
theorem norm_one_add_eq_one {E : Type} [NormedField E] [IsUltrametricDist E] {a : E}
    (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  have h : ‖(1 : E)‖ ≠ ‖a‖ := by rw [norm_one]; exact ha.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `Finset.sum_induction _ (fun x : E => ‖x‖ < 1) (fun a b ha hb => norm_add_lt_one ha hb) (by simp) ?_` and prove the remaining obligations. Introduce `σ _`. Establish `hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]`.

Rewrite using `[norm_mul, hs, one_mul, norm_prod]`. Take `⟨i⟩` from `‹Nonempty n›`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Establish `h2 : ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => (h _ _).le)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_det_lt_one {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (h : ∀ i j, ‖G i j‖ < 1) : ‖G.det‖ < 1 := by
  rw [Matrix.det_apply']
  refine Finset.sum_induction _ (fun x : E => ‖x‖ < 1) (fun a b ha hb => norm_add_lt_one ha hb)
    (by simp) ?_
  intro σ _
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [norm_mul, hs, one_mul, norm_prod]
  obtain ⟨i⟩ := ‹Nonempty n›
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h2 : ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => (h _ _).le)
  calc ‖G (σ i) i‖ * ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ ‖G (σ i) i‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact h _ _

/- English proof (translation)
Distinguish the cases in `hd : ∃ i, ‖G i i‖ = 1`. Take `⟨i, hi⟩` from `hd`. Use `⟨i, Pi.single i 1, ?_, by simp, ?_⟩` and prove the remaining obligations. Introduce `a`. Distinguish the cases in `ha : a = i`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne ha]`. Establish `hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1`. Rewrite using `[Pi.star_single, star_one]`.

Rewrite using `[hs, single_dotProduct, Matrix.mulVec_single_one]`. Simplify using `using hi`. Establish `hdiag : ∀ i, ‖G i i‖ < 1` using `fun i => lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)`. Establish `hex : ∃ i j, ‖G i j‖ = 1`. Assume the negation of the conclusion as `hne`.

Use `norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))` as an intermediate fact. Conclude with `this.ne hdet`. Take `⟨i, j, hij⟩` from `hex`. Establish `hne : i ≠ j`. Introduce and unpack `rfl`.

Conclude with `(hdiag i).ne hij`. Establish `hg0 : G i j ≠ 0`. Introduce `h`. Rewrite `hij` using `[h, norm_zero]`. Conclude with `zero_ne_one hij`.

Use `set t : E := e0 / G i j with ht`. Establish `htn : ‖t‖ ≤ 1` using `by rw [ht, norm_div, hij, div_one]; exact he`. Establish `htG : G i j * t = e0` using `by rw [ht]; field_simp`. Establish `hji : G j i = star (G i j)` using `(hG.apply j i).symm`. Establish `htG' : star t * G j i = star e0` using `by rw [hji, ← star_mul, htG]`.

Use `⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality. Simplify using `[Pi.single_eq_of_ne hne]`.

Distinguish the cases in `hb : a = j`. Substitute `hb` using the available equality. Simplify `htn` using `[Pi.single_eq_of_ne ha]`. Simplify using `[Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]`. Simplify using `[Pi.single_eq_of_ne hne]`.

Establish `hs : star (Pi.single i (1 : E) + Pi.single j t : n → E) = Pi.single i 1 + Pi.single j (star t)`. Rewrite using `[star_add, Pi.star_single, Pi.star_single, star_one]`. Establish `key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ Matrix.mulVec G (Pi.single i 1 + Pi.single j t) = 1 + (G i i + star t * (G j j * t))`. Rewrite using `[hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]`. Simplify using `only [Pi.add_apply, Matrix.mulVec, dotProduct_single]`.

Take the linear combination `htG + htG' + htr`. Rewrite using `[key]`. Apply `norm_one_add_eq_one` to reduce the goal to its premises. Apply `norm_add_lt_one (hdiag i)` to reduce the goal to its premises. Rewrite using `[norm_mul, norm_mul, hstar]`.

Establish `h1` using `hdiag j`. Establish `h2` using `norm_nonneg t`. Establish `h3` using `norm_nonneg (G j j)`. Establish `h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖` using `mul_le_of_le_one_right h3 htn`. Establish `h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖` using `mul_le_of_le_one_left (mul_nonneg h3 h2) htn`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_unit_value {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he : ‖e0‖ ≤ (1 : ℝ)) (htr : e0 + star e0 = 1)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (hG : Matrix.IsHermitian G) (hint : ∀ i j, ‖G i j‖ ≤ (1 : ℝ)) (hdet : ‖G.det‖ = (1 : ℝ)) :
    ∃ (i : n) (w : n → E), (∀ a, ‖w a‖ ≤ (1 : ℝ)) ∧ w i = 1 ∧
      ‖star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ) := by
  by_cases hd : ∃ i, ‖G i i‖ = 1
  · obtain ⟨i, hi⟩ := hd
    refine ⟨i, Pi.single i 1, ?_, by simp, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
        rw [Pi.star_single, star_one]
      rw [hs, single_dotProduct, Matrix.mulVec_single_one]
      simpa using hi
  · have hdiag : ∀ i, ‖G i i‖ < 1 := fun i =>
      lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)
    have hex : ∃ i j, ‖G i j‖ = 1 := by
      by_contra hne
      have := norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))
      exact this.ne hdet
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := by
      rintro rfl
      exact (hdiag i).ne hij
    have hg0 : G i j ≠ 0 := by
      intro h; rw [h, norm_zero] at hij; exact zero_ne_one hij
    set t : E := e0 / G i j with ht
    have htn : ‖t‖ ≤ 1 := by rw [ht, norm_div, hij, div_one]; exact he
    have htG : G i j * t = e0 := by rw [ht]; field_simp
    have hji : G j i = star (G i j) := (hG.apply j i).symm
    have htG' : star t * G j i = star e0 := by rw [hji, ← star_mul, htG]
    refine ⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp [Pi.single_eq_of_ne hne]
      · by_cases hb : a = j
        · subst hb; simpa [Pi.single_eq_of_ne ha] using htn
        · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
    · simp [Pi.single_eq_of_ne hne]
    · have hs : star (Pi.single i (1 : E) + Pi.single j t : n → E)
          = Pi.single i 1 + Pi.single j (star t) := by
        rw [star_add, Pi.star_single, Pi.star_single, star_one]
      have key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ
          Matrix.mulVec G (Pi.single i 1 + Pi.single j t)
          = 1 + (G i i + star t * (G j j * t)) := by
        rw [hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct_single]
        linear_combination htG + htG' + htr
      rw [key]
      apply norm_one_add_eq_one
      apply norm_add_lt_one (hdiag i)
      rw [norm_mul, norm_mul, hstar]
      have h1 := hdiag j
      have h2 := norm_nonneg t
      have h3 := norm_nonneg (G j j)
      have h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖ := mul_le_of_le_one_right h3 htn
      have h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖ :=
        mul_le_of_le_one_left (mul_nonneg h3 h2) htn
      linarith

/- English proof (translation)
Introduce `d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet`. Conclude with `exists_unit_value hstar e0 he htr G hG hint hdet`.
-/
theorem main : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by
  intro d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet
  exact exists_unit_value hstar e0 he htr G hG hint hdet

end GlobalTheory.UnitValueExistence
