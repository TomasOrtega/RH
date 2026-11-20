import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.UtSubOneLast

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

/- English proof (translation)
Establish `hG : gramM k r z z' γ = (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ`. Use extensionality with `i j`. Simplify using `only [gramM, herm, Fm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.

Unfold `PI.StabPairsW.rhoOf PI.StabPairs.ConvAlg.rhoOf PI.StabPairsW.Km`. Rewrite using `[hG]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem rho_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' =
      PI.StabPairs.ConvAlg.rhoOf (Hpk k r) (Fm k r z z' γ) (Wm u u') := by
  have hG : gramM k r z z' γ = (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
    ext i j
    simp only [gramM, herm, Fm, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold PI.StabPairsW.rhoOf PI.StabPairs.ConvAlg.rhoOf PI.StabPairsW.Km
  rw [hG]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `Wm`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply]`.
-/
theorem Wm_sub_one {r : ℕ} (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Wm u u' - 1 = Matrix.fromBlocks (u - 1) 0 0 (u' - 1) := by
  unfold Wm
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

/- English proof (translation)
Establish `hF : ∀ (x y : Fin (r + 1) → ℂ), Fm k r z z' γ *ᵥ Sum.elim x y = Ff k r z *ᵥ x + (γ * Ff k r z') *ᵥ y`. Introduce `x y`. Rewrite using `[← Matrix.mulVec_mulVec]`. Use extensionality with `i`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fm, Matrix.of_apply, gramVec, Ff, Pi.add_apply, Finset.sum_mul, Finset.mul_sum]`.

Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Unfold `PI.StabPairsW.rhoOf`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Wm_sub_one, Matrix.fromBlocks_mulVec]`.

Simplify using `only [Matrix.zero_mulVec, add_zero, zero_add]`. Rewrite using `[hF, ← add_assoc]`.
-/
theorem rho_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' *ᵥ v =
      v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
        (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by
  have hF : ∀ (x y : Fin (r + 1) → ℂ), Fm k r z z' γ *ᵥ Sum.elim x y =
      Ff k r z *ᵥ x + (γ * Ff k r z') *ᵥ y := by
    intro x y
    rw [← Matrix.mulVec_mulVec]
    ext i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fm,
      Matrix.of_apply, gramVec, Ff, Pi.add_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold PI.StabPairsW.rhoOf
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Wm_sub_one, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  rw [hF, ← add_assoc]

/- English proof (translation)
Unfold `PI.StabPairsW.Km`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc (gramM k r z z' γ)⁻¹, ← Matrix.mul_assoc (gramM k r z z' γ), Matrix.mul_nonsing_inv _ hGi, Matrix.one_mul]`.
-/
theorem gram_Km (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ) :
    gramM k r z z' γ *ᵥ (Km k r z z' γ *ᵥ v) = ((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v := by
  unfold PI.StabPairsW.Km
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (gramM k r z z' γ)⁻¹, ← Matrix.mul_assoc (gramM k r z z' γ),
    Matrix.mul_nonsing_inv _ hGi, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.
-/
theorem FH_apply (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ)
    (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by
  rw [← Matrix.mulVec_mulVec]
  rfl

/- English proof (translation)
Establish `hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0`. Introduce `e c he hc`. Unfold `Hpk`. Rewrite using `[if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega))]`. Establish `hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r → ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) → herm (Hpk k r) x (fvec k r y a) = 0`.

Introduce `y a ha x hx`. Unfold `fvec`. Rewrite using `[dif_pos ha]`. Simplify using `only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]`. Rewrite using `[Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]`.

Simplify using `only [Pi.single_eq_same, star_one, one_mul]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : r + k < c.val`. Rewrite using `[hx c hc, mul_zero]`. Rewrite using `[hHz _ _ ha (by omega), zero_mul]`.

Introduce `i _ hi`. Rewrite using `[Pi.single_eq_of_ne hi, star_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)), r + k < c.val → fvec k r y b c = 0`.

Introduce `y hy b c hc`. Unfold `fvec`. Use `split_ifs with hb`. Conclude with `Pi.single_eq_of_ne (fun h' => by`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `[eI] at this`. Use the proof step `omega) _`. Conclude with `hy c (Or.inr hc)`. Introduce `a ha`. Establish `hK` using `congrFun (gram_Km k r z z' γ hGi v) (Sum.inl a)`.

Rewrite `hK` using `[FH_apply]`. Generalize the expression as in `Km k r z z' γ *ᵥ v = w at hK ⊢`. Establish `h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inl a)) = 0` using `hv a ha`. Rewrite `hK` using `[h0]`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK`.

Establish `h1 : ∀ b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = 0` using `fun b => hrow z a ha _ (hfz z hS.2.1.1 b)`. Simplify using `only [h1, zero_mul, Finset.sum_const_zero, zero_add] at hK`. Simplify using `only [Matrix.mulVec, dotProduct, Function.comp]`. Conclude with `hK`.
-/
theorem Z_cR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hS : Std k r z z')
    (hP : PosPt k r z z' γ) (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a : Fin (r + 1), a.val < r → herm (Hpk k r) v (fvec k r z a) = 0) :
    ∀ a : Fin (r + 1), a.val < r → (Zhat k r z z' γ *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) a = 0 := by
  have hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0 := by
    intro e c he hc
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r →
      ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) →
      herm (Hpk k r) x (fvec k r y a) = 0 := by
    intro y a ha x hx
    unfold fvec
    rw [dif_pos ha]
    simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]
    · simp only [Pi.single_eq_same, star_one, one_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : r + k < c.val
      · rw [hx c hc, mul_zero]
      · rw [hHz _ _ ha (by omega), zero_mul]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)),
      r + k < c.val → fvec k r y b c = 0 := by
    intro y hy b c hc
    unfold fvec
    split_ifs with hb
    · exact Pi.single_eq_of_ne (fun h' => by
        have := congrArg Fin.val h'
        simp [eI] at this
        omega) _
    · exact hy c (Or.inr hc)
  intro a ha
  have hK := congrFun (gram_Km k r z z' γ hGi v) (Sum.inl a)
  rw [FH_apply] at hK
  generalize Km k r z z' γ *ᵥ v = w at hK ⊢
  have h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inl a)) = 0 := hv a ha
  rw [h0] at hK
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK
  have h1 : ∀ b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = 0 :=
    fun b => hrow z a ha _ (hfz z hS.2.1.1 b)
  simp only [h1, zero_mul, Finset.sum_const_zero, zero_add] at hK
  simp only [Matrix.mulVec, dotProduct, Function.comp]
  exact hK

/- English proof (translation)
Establish `hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0`. Introduce `e c he hc`. Unfold `Hpk`. Rewrite using `[if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega))]`. Establish `hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r → ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) → herm (Hpk k r) x (fvec k r y a) = 0`.

Introduce `y a ha x hx`. Unfold `fvec`. Rewrite using `[dif_pos ha]`. Simplify using `only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]`. Rewrite using `[Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]`.

Simplify using `only [Pi.single_eq_same, star_one, one_mul]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : r + k < c.val`. Rewrite using `[hx c hc, mul_zero]`. Rewrite using `[hHz _ _ ha (by omega), zero_mul]`.

Introduce `i _ hi`. Rewrite using `[Pi.single_eq_of_ne hi, star_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)), r + k < c.val → fvec k r y b c = 0`.

Introduce `y hy b c hc`. Unfold `fvec`. Use `split_ifs with hb`. Conclude with `Pi.single_eq_of_ne (fun h' => by`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `[eI] at this`. Use the proof step `omega) _`. Conclude with `hy c (Or.inr hc)`. Introduce `b hb`. Establish `hK` using `congrFun (gram_Km k r z z' γ hGi v) (Sum.inr b)`.

Rewrite `hK` using `[FH_apply]`. Generalize the expression as in `Km k r z z' γ *ᵥ v = w at hK ⊢`. Establish `h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inr b)) = 0` using `hv b hb`. Rewrite `hK` using `[h0]`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK`.

Establish `h1 : ∀ a, gramM k r z z' γ (Sum.inr b) (Sum.inr a) = 0`. Introduce `a`. Use `show herm (Hpk k r) (γ *ᵥ fvec k r z' a) (γ *ᵥ fvec k r z' b) = 0`. Rewrite using `[herm_GV hP.1]`. Conclude with `hrow z' b hb _ (hfz z' hS.2.2.1 a)`.

Simplify using `only [h1, zero_mul, Finset.sum_const_zero, add_zero] at hK`. Simplify using `only [Matrix.mulVec, dotProduct, Function.comp, Matrix.conjTranspose_apply]`. Rewrite using `[← hK]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `show star (herm (Hpk k r) (γ *ᵥ fvec k r z' b) (fvec k r z a)) = herm (Hpk k r) (fvec k r z a) (γ *ᵥ fvec k r z' b)`. Rewrite using `[herm_swap (fvec k r z a)]`.
-/
theorem Z_cL (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hS : Std k r z z')
    (hP : PosPt k r z z' γ) (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin (r + 1), b.val < r → herm (Hpk k r) v (γ *ᵥ fvec k r z' b) = 0) :
    ∀ b : Fin (r + 1), b.val < r → ((Zhat k r z z' γ)ᴴ *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) b = 0 := by
  have hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0 := by
    intro e c he hc
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r →
      ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) →
      herm (Hpk k r) x (fvec k r y a) = 0 := by
    intro y a ha x hx
    unfold fvec
    rw [dif_pos ha]
    simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]
    · simp only [Pi.single_eq_same, star_one, one_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : r + k < c.val
      · rw [hx c hc, mul_zero]
      · rw [hHz _ _ ha (by omega), zero_mul]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)),
      r + k < c.val → fvec k r y b c = 0 := by
    intro y hy b c hc
    unfold fvec
    split_ifs with hb
    · exact Pi.single_eq_of_ne (fun h' => by
        have := congrArg Fin.val h'
        simp [eI] at this
        omega) _
    · exact hy c (Or.inr hc)
  intro b hb
  have hK := congrFun (gram_Km k r z z' γ hGi v) (Sum.inr b)
  rw [FH_apply] at hK
  generalize Km k r z z' γ *ᵥ v = w at hK ⊢
  have h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inr b)) = 0 := hv b hb
  rw [h0] at hK
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK
  have h1 : ∀ a, gramM k r z z' γ (Sum.inr b) (Sum.inr a) = 0 := by
    intro a
    show herm (Hpk k r) (γ *ᵥ fvec k r z' a) (γ *ᵥ fvec k r z' b) = 0
    rw [herm_GV hP.1]
    exact hrow z' b hb _ (hfz z' hS.2.2.1 a)
  simp only [h1, zero_mul, Finset.sum_const_zero, add_zero] at hK
  simp only [Matrix.mulVec, dotProduct, Function.comp, Matrix.conjTranspose_apply]
  rw [← hK]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  show star (herm (Hpk k r) (γ *ᵥ fvec k r z' b) (fvec k r z a)) =
    herm (Hpk k r) (fvec k r z a) (γ *ᵥ fvec k r z' b)
  rw [herm_swap (fvec k r z a)]

/- English proof (translation)
Establish `hH : ∀ (e j : Fin (2 * r + k + 1)), e.val < r → r ≤ j.val → j.val ≤ r + k → Hpk k r e j = 0`. Introduce `e j he hj1 hj2`. Unfold `Hpk`. Rewrite using `[if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega)), if_neg (fun h => absurd h.1 (by omega))]`. Establish `hf : fvec k r z a = bvec (eI k r ⟨a.val, ha⟩)`.

Unfold `fvec`. Rewrite using `[dif_pos ha]`. Rewrite using `[hf]`. Establish `h1 : herm (Hpk k r) (bvec j) (bvec (eI k r ⟨a.val, ha⟩)) = Hpk k r (eI k r ⟨a.val, ha⟩) j`. Simplify using `[herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]`.

Rewrite using `[h1]`. Conclude with `hH _ _ ha hj1 hj2`.
-/
theorem herm_bvec_fvec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1))
    (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin (r + 1)) (ha : a.val < r) :
    herm (Hpk k r) (bvec j) (fvec k r z a) = 0 := by
  have hH : ∀ (e j : Fin (2 * r + k + 1)), e.val < r → r ≤ j.val → j.val ≤ r + k →
      Hpk k r e j = 0 := by
    intro e j he hj1 hj2
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hf : fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) := by
    unfold fvec
    rw [dif_pos ha]
  rw [hf]
  have h1 : herm (Hpk k r) (bvec j) (bvec (eI k r ⟨a.val, ha⟩)) = Hpk k r (eI k r ⟨a.val, ha⟩) j := by
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  exact hH _ _ ha hj1 hj2

/- English proof (translation)
Establish `hfa : fvec k r z (Fin.castSucc a) = bvec (eI k r a)`. Unfold `fvec`. Rewrite using `[dif_pos (by simp)]`. Both sides reduce to the same expression. Establish `h1` using `congrFun (congrFun hM i) (Fin.castSucc a)`.

Establish `hL : (M * Ff k r z) i (Fin.castSucc a) = M i (eI k r a)`. Simplify using `only [Matrix.mul_apply, Ff, Matrix.of_apply, hfa]`. Simplify using `[bvec, Pi.single_apply]`. Establish `hR : (Ff k r z * u) i (Fin.castSucc a) = if i = eI k r a then 1 else 0`. Simplify using `only [Matrix.mul_apply, Ff, Matrix.of_apply]`.

Rewrite using `[Finset.sum_eq_single (Fin.castSucc a)]`. Rewrite using `[hu.2, mul_one, hfa]`. Simplify using `[bvec, Pi.single_apply]`. Introduce `b _ hb`. Distinguish the cases in `hba : Fin.castSucc a < b`.

Rewrite using `[hu.1 _ _ hba, mul_zero]`. Establish `hlt : b.val < a.val`. Establish `h2 : b < Fin.castSucc a` using `lt_of_le_of_ne (not_lt.mp hba) hb`. Conclude with `h2`. Establish `hbr : b.val < r` using `by omega`.

Establish `: fvec k r z b i = 0`. Unfold `fvec`. Rewrite using `[dif_pos hbr]`. Conclude with `Pi.single_eq_of_ne (fun h' => by`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `[eI] at this`. Use the proof step `omega) _`. Rewrite using `[this, zero_mul]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.

Rewrite using `[← hL, h1, hR]`.
-/
theorem N2gen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r)
    {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (hM : M * Ff k r z = Ff k r z * u)
    (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    M i (eI k r a) = if i = eI k r a then 1 else 0 := by
  classical
  have hfa : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by
    unfold fvec
    rw [dif_pos (by simp)]
    rfl
  have h1 := congrFun (congrFun hM i) (Fin.castSucc a)
  have hL : (M * Ff k r z) i (Fin.castSucc a) = M i (eI k r a) := by
    simp only [Matrix.mul_apply, Ff, Matrix.of_apply, hfa]
    simp [bvec, Pi.single_apply]
  have hR : (Ff k r z * u) i (Fin.castSucc a) = if i = eI k r a then 1 else 0 := by
    simp only [Matrix.mul_apply, Ff, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.castSucc a)]
    · rw [hu.2, mul_one, hfa]
      simp [bvec, Pi.single_apply]
    · intro b _ hb
      by_cases hba : Fin.castSucc a < b
      · rw [hu.1 _ _ hba, mul_zero]
      · have hlt : b.val < a.val := by
          have h2 : b < Fin.castSucc a := lt_of_le_of_ne (not_lt.mp hba) hb
          exact h2
        have hbr : b.val < r := by omega
        have : fvec k r z b i = 0 := by
          unfold fvec
          rw [dif_pos hbr]
          exact Pi.single_eq_of_ne (fun h' => by
            have := congrArg Fin.val h'
            simp [eI] at this
            omega) _
        rw [this, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  rw [← hL, h1, hR]

/- English proof (translation)
Establish `h1` using `congrFun h i`. Establish `hMj : (M *ᵥ bvec j) i = M i j`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite `h1` using `[hMj]`. Rewrite using `[h1, Pi.add_apply]`.

Establish `h2 : (Ff k r z *ᵥ x) i = 0`. Simplify using `only [Matrix.mulVec, dotProduct, Ff, Matrix.of_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b.val < r`. Establish `: fvec k r z b i = 0`.

Unfold `fvec`. Rewrite using `[dif_pos hb]`. Conclude with `Pi.single_eq_of_ne (fun h' => by`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `[eI] at this`.

Use the proof step `omega) _`. Rewrite using `[this, zero_mul]`. Establish `hbl : b = Fin.last r` using `Fin.ext (by have := b.isLt; simp; omega)`. Rewrite using `[hbl, hx, mul_zero]`. Rewrite using `[h2, add_zero]`.

Simplify using `[bvec, Pi.single_apply]`.
-/
theorem N3gen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) (x : Fin (r + 1) → ℂ) (hx : x (Fin.last r) = 0)
    (h : M *ᵥ bvec j = bvec j + Ff k r z *ᵥ x) : M i j = if i = j then 1 else 0 := by
  classical
  have h1 := congrFun h i
  have hMj : (M *ᵥ bvec j) i = M i j := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hMj] at h1
  rw [h1, Pi.add_apply]
  have h2 : (Ff k r z *ᵥ x) i = 0 := by
    simp only [Matrix.mulVec, dotProduct, Ff, Matrix.of_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b.val < r
    · have : fvec k r z b i = 0 := by
        unfold fvec
        rw [dif_pos hb]
        exact Pi.single_eq_of_ne (fun h' => by
          have := congrArg Fin.val h'
          simp [eI] at this
          omega) _
      rw [this, zero_mul]
    · have hbl : b = Fin.last r := Fin.ext (by have := b.isLt; simp; omega)
      rw [hbl, hx, mul_zero]
  rw [h2, add_zero]
  simp [bvec, Pi.single_apply]

end PI.StabPairs.Conv
