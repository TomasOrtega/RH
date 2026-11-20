import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Central

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n : ℕ}

private def sgnM (F : Type) [Field F] (n a : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else -1

/- English proof (translation)
Rewrite using `[sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem sgnM_sq (a : ℕ) : sgnM F n a * sgnM F n a = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj]`.
-/
private theorem sgnM_conj_apply (a : ℕ) (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (sgnM F n a * X * sgnM F n a) i j = if ((i : ℕ) < a ↔ (j : ℕ) < a) then X i j else -X i j := by
  simp only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj]

/- English proof (translation)
Establish `hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) ∧ (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F))` using `hX`. Use extensionality with `i j`. Rewrite using `[sgnM_conj_apply]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Establish `h0 : X i j = 0` using `by simpa using (hX' i j).2 h`. Rewrite using `[h0, neg_zero]`.
-/
private theorem sgnM_ev (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Ev F F n a) :
    sgnM F n a * X * sgnM F n a = X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply]
  split_ifs with h
  · rfl
  · have h0 : X i j = 0 := by simpa using (hX' i j).2 h
    rw [h0, neg_zero]

/- English proof (translation)
Establish `hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧ (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F))` using `hX`. Use extensionality with `i j`. Rewrite using `[sgnM_conj_apply, Matrix.neg_apply]`. Use `split_ifs with h`. Establish `h0 : X i j = 0` using `by simpa using (hX' i j).1 h`.

Rewrite using `[h0, neg_zero]`. Both sides reduce to the same expression.
-/
private theorem sgnM_od (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Od F F n a) :
    sgnM F n a * X * sgnM F n a = -X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply, Matrix.neg_apply]
  split_ifs with h
  · have h0 : X i j = 0 := by simpa using (hX' i j).1 h
    rw [h0, neg_zero]
  · rfl

/- English proof (translation)
Use `show ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧ (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F))`. Introduce `i j`. Use `⟨fun h => ?_, fun _ => Submodule.mem_top⟩` and prove the remaining obligations. Establish `e` using `congrFun (congrFun hX i) j`. Rewrite `e` using `[sgnM_conj_apply, if_pos h, Matrix.neg_apply]`.

Establish `h2 : (2 : F) * X i j = 0` using `by rw [two_mul]; nth_rewrite 1 [e]; ring`. Rewrite using `[Submodule.mem_bot]`. Conclude with `(mul_eq_zero.mp h2).resolve_left two`.
-/
private theorem od_of_sgnM (two : (2 : F) ≠ 0) (a : ℕ) {X : Matrix (Fin n) (Fin n) F}
    (hX : sgnM F n a * X * sgnM F n a = -X) : X ∈ Od F F n a := by
  show ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F))
  intro i j
  refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
  have e := congrFun (congrFun hX i) j
  rw [sgnM_conj_apply, if_pos h, Matrix.neg_apply] at e
  have h2 : (2 : F) * X i j = 0 := by rw [two_mul]; nth_rewrite 1 [e]; ring
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.mp h2).resolve_left two

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (sgnM F n a) (sgnM F n a), sgnM_sq, Matrix.one_mul]`.
-/
private theorem sgnM_mul (a : ℕ) (X Y : Matrix (Fin n) (Fin n) F) :
    sgnM F n a * (X * Y) * sgnM F n a = (sgnM F n a * X * sgnM F n a) * (sgnM F n a * Y * sgnM F n a) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (sgnM F n a) (sgnM F n a), sgnM_sq, Matrix.one_mul]

/- English proof (translation)
Simplify using `only [dTw, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, sgnM_mul, sgnM_ev D.a (D.ev g), sgnM_ev D.a (D.ev g⁻¹)]`.
-/
private theorem sgnM_dTw {G : Type} [Group G] (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G) :
    sgnM F n D.a * dTw χ D.r Y g * sgnM F n D.a = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) g := by
  simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, sgnM_mul,
    sgnM_ev D.a (D.ev g), sgnM_ev D.a (D.ev g⁻¹)]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F G _ _ n D χ z Y hχ hχ' hz hzod hzG`. Establish `two : (2 : F) ≠ 0` using `D.two`. Establish `hdTw_sub : ∀ A B g, dTw χ D.r (A - B) g = dTw χ D.r A g - dTw χ D.r B g`. Introduce `A B g`. Simplify using `only [dTw, Matrix.mul_sub, Matrix.sub_mul, smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `hdTw_smul : ∀ (c : F) A g, dTw χ D.r (c • A) g = c • dTw χ D.r A g`. Introduce `c A g`. Simplify using `only [dTw, Matrix.mul_smul, Matrix.smul_mul, smul_sub]`. Rewrite using `[smul_comm]`.

Establish `hdTw_neg : ∀ A g, dTw χ D.r (-A) g = -dTw χ D.r A g`. Introduce `A g`. Simplify using `only [dTw, Matrix.mul_neg, Matrix.neg_mul, smul_neg]`. Normalize the expressions using the abelian group laws. Establish `hdc : ∀ A g h, dTw χ D.r A (g * h) = dTw χ D.r A g + χ g • (D.r g * dTw χ D.r A h * D.r g⁻¹)`.

Introduce `A g h`. Simplify using `only [dTw, hχ, _root_.mul_inv_rev, map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Establish `hss` using `sgnM_sq (F := F) (n := n) D.a`. Establish `hcc : ∀ A : Matrix (Fin n) (Fin n) F, sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a = A`.

Introduce `A`. Rewrite using `[show sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a = (sgnM F n D.a * sgnM F n D.a) * A * (sgnM F n D.a * sgnM F n D.a) by`. Simplify using `only [Matrix.mul_assoc], hss, Matrix.one_mul, Matrix.mul_one]`. Use `set Y' : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (Y - sgnM F n D.a * Y * sgnM F n D.a) with hY'`. Establish `hY'od : Y' ∈ Od F F n D.a`.

Apply `od_of_sgnM two` to reduce the goal to its premises. Rewrite using `[hY', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcc, ← smul_neg, neg_sub]`. Establish `hG' : ∀ h ∈ D.G', z h = dTw χ D.r Y' h`. Introduce `h hh`. Establish `h1` using `hzG h hh`.

Establish `h2 : -z h = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) h`. Rewrite using `[← sgnM_od D.a (hzod h), h1, sgnM_dTw]`. Rewrite using `[hY', hdTw_smul, hdTw_sub, ← h1, ← h2, sub_neg_eq_add, ← two_smul F (z h), smul_smul, inv_mul_cancel₀ two, one_smul]`. Establish `key : ∀ g, z g - dTw χ D.r Y' g = 0`. Introduce `g`.

Use `set w : G → Matrix (Fin n) (Fin n) F := fun x => z x - dTw χ D.r Y' x with hw`. Establish `hwc : ∀ x y, w (x * y) = w x + χ x • (D.r x * w y * D.r x⁻¹)`. Introduce `x y`. Simplify using `only [hw]`. Rewrite using `[hz x trivial y trivial, hdc]`.

Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hw0 : ∀ h ∈ D.G', w h = 0` using `fun h hh => by`. Simplify using `only [hw]`. Rewrite using `[hG' h hh, sub_self]`.

Establish `hcomm : ∀ h ∈ D.G', D.r h * w g = w g * D.r h`. Introduce `h hh`. Establish `hh' : g⁻¹ * h * g ∈ D.G'`. Establish `hm` using `D.G'.mul_mem (D.comm g⁻¹ h) hh`. Simplify `hm` using `[mul_assoc]`.

Establish `e1` using `hwc g (g⁻¹ * h * g)`. Establish `e2` using `hwc h g`. Rewrite `e1` using `[hw0 _ hh', Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero]`. Rewrite `e2` using `[hw0 _ hh, hχ' h hh, one_smul, zero_add]`. Establish `heq : g * (g⁻¹ * h * g) = h * g` using `by group`.

Rewrite `e1` using `[heq, e2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul D.r h⁻¹ h, inv_mul_cancel, map_one, Matrix.mul_one]`. Use `_ = (D.r h * w g * D.r h⁻¹) * D.r h := by simp only [Matrix.mul_assoc]`. Use `_ = w g * D.r h := by rw [e1]`.

Establish `hwod : w g ∈ Od F F n D.a`. Simplify using `only [hw]`. Use `Submodule.sub_mem _ (hzod g) ?_` and prove the remaining obligations. Apply `od_of_sgnM two` to reduce the goal to its premises. Rewrite using `[sgnM_dTw, sgnM_od D.a hY'od, hdTw_neg]`.

Conclude with `(Det.central D (w g) hcomm).1 hwod`. Conclude with `⟨Y', hY'od, fun g => sub_eq_zero.mp (key g)⟩`.
-/
theorem UpperTheory.V.Pa.Det.infres :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g h, χ (g * h) = χ g * χ h) → (∀ g ∈ D.G', χ g = 1) → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g ∈ D.G', z g = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ z Y hχ hχ' hz hzod hzG
  have two : (2 : F) ≠ 0 := D.two
  have hdTw_sub : ∀ A B g, dTw χ D.r (A - B) g = dTw χ D.r A g - dTw χ D.r B g := by
    intro A B g
    simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have hdTw_smul : ∀ (c : F) A g, dTw χ D.r (c • A) g = c • dTw χ D.r A g := by
    intro c A g
    simp only [dTw, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [smul_comm]
  have hdTw_neg : ∀ A g, dTw χ D.r (-A) g = -dTw χ D.r A g := by
    intro A g
    simp only [dTw, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
    abel
  have hdc : ∀ A g h, dTw χ D.r A (g * h) = dTw χ D.r A g + χ g • (D.r g * dTw χ D.r A h * D.r g⁻¹) := by
    intro A g h
    simp only [dTw, hχ, _root_.mul_inv_rev, map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc]
    abel
  have hss := sgnM_sq (F := F) (n := n) D.a
  have hcc : ∀ A : Matrix (Fin n) (Fin n) F,
      sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a = A := by
    intro A
    rw [show sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a
        = (sgnM F n D.a * sgnM F n D.a) * A * (sgnM F n D.a * sgnM F n D.a) by
      simp only [Matrix.mul_assoc], hss, Matrix.one_mul, Matrix.mul_one]
  set Y' : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (Y - sgnM F n D.a * Y * sgnM F n D.a) with hY'
  have hY'od : Y' ∈ Od F F n D.a := by
    apply od_of_sgnM two
    rw [hY', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcc, ← smul_neg, neg_sub]
  have hG' : ∀ h ∈ D.G', z h = dTw χ D.r Y' h := by
    intro h hh
    have h1 := hzG h hh
    have h2 : -z h = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) h := by
      rw [← sgnM_od D.a (hzod h), h1, sgnM_dTw]
    rw [hY', hdTw_smul, hdTw_sub, ← h1, ← h2, sub_neg_eq_add, ← two_smul F (z h), smul_smul,
      inv_mul_cancel₀ two, one_smul]
  have key : ∀ g, z g - dTw χ D.r Y' g = 0 := by
    intro g
    set w : G → Matrix (Fin n) (Fin n) F := fun x => z x - dTw χ D.r Y' x with hw
    have hwc : ∀ x y, w (x * y) = w x + χ x • (D.r x * w y * D.r x⁻¹) := by
      intro x y
      simp only [hw]
      rw [hz x trivial y trivial, hdc]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    have hw0 : ∀ h ∈ D.G', w h = 0 := fun h hh => by
      simp only [hw]
      rw [hG' h hh, sub_self]
    have hcomm : ∀ h ∈ D.G', D.r h * w g = w g * D.r h := by
      intro h hh
      have hh' : g⁻¹ * h * g ∈ D.G' := by
        have hm := D.G'.mul_mem (D.comm g⁻¹ h) hh
        simpa [mul_assoc] using hm
      have e1 := hwc g (g⁻¹ * h * g)
      have e2 := hwc h g
      rw [hw0 _ hh', Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero] at e1
      rw [hw0 _ hh, hχ' h hh, one_smul, zero_add] at e2
      have heq : g * (g⁻¹ * h * g) = h * g := by group
      rw [heq, e2] at e1
      calc D.r h * w g = D.r h * w g * (D.r h⁻¹ * D.r h) := by
            rw [← map_mul D.r h⁻¹ h, inv_mul_cancel, map_one, Matrix.mul_one]
        _ = (D.r h * w g * D.r h⁻¹) * D.r h := by simp only [Matrix.mul_assoc]
        _ = w g * D.r h := by rw [e1]
    have hwod : w g ∈ Od F F n D.a := by
      simp only [hw]
      refine Submodule.sub_mem _ (hzod g) ?_
      apply od_of_sgnM two
      rw [sgnM_dTw, sgnM_od D.a hY'od, hdTw_neg]
    exact (Det.central D (w g) hcomm).1 hwod
  exact ⟨Y', hY'od, fun g => sub_eq_zero.mp (key g)⟩
